# Cantina PR #36 postmortem — what our verification stack missed

Reserve-Governor PR #36 (`Cantina Contest Fixes`,
[reserve-protocol/reserve-governor#36](https://github.com/reserve-protocol/reserve-governor/pull/36))
landed two changes:

1. **Bug fix**: `ReserveOptimisticGovernor.state()` was computing the
   veto threshold against `token.getPastTotalSupply(snapshot)`. It now
   uses `getPastOptimisticVotingSupply(snapshot)` — only counting
   tokens whose holder *opted in* by setting a non-zero optimistic
   delegate.

2. **Storage refactor enabling the fix**: StakingVault swapped two
   separate mappings (`optimisticDelegatees`,
   `optimisticDelegateCheckpoints`) for a single `VotesStorage`
   struct that adds `_totalCheckpoints` — the supply-over-time
   checkpoint that the new `getPastOptimisticVotingSupply()` reads.
   Without that storage, the contract literally could not answer the
   "what was the optimistic supply at past snapshot N" question.

The headline question for this memo: **would any of our three
verification layers have caught the wrong-supply-denominator bug?**

## Honest answer: no.

All three layers verify "the implementation matches the spec," and the
spec was wrong. None of the layers ask "is the spec correct?"

### Why Rocq missed it

`formal-verification/rocq/simulations/Governor.v:19` documents the
modeling assumption explicitly:

> token.getPastTotalSupply / getPastVotes — supplied per-call as
> explicit U256.t arguments.

The simulation takes `pastSupply : U256.t` as an opaque parameter and
computes:

```coq
Definition vetoThresholdTokOf (vetoThresholdD18 pastSupply : U256.t) : U256.t :=
  let raw := (vetoThresholdD18 * pastSupply) / FIX_ONE in
  ...
```

The Gallina model has no concept of "total supply vs optimistic
voting supply" — it has *one* parameter called `pastSupply`. Every
theorem about veto-threshold reachability (`add_veto_*`,
`transition_to_pessimistic_*`) holds for *whatever* the caller passes
as `pastSupply`. A faithful Yul-IR-derived model would copy the
contract's `getPastTotalSupply` call without question, and the proofs
would hold equally for the wrong implementation.

### Why CAS missed it

The CAS witnesses in `cas/governor/escalation.gp` test threshold-
reaching scenarios with numerical inputs. They drive `pastSupply` from
the same source as the Rocq simulation — an explicit argument. The
witnesses confirm that `vetoVotes >= threshold(pastSupply)` triggers
the Defeated transition. They don't constrain *where* `pastSupply`
comes from in the contract.

### Why Certora missed it

`formal-verification/certora/Governor/Governor.spec:133-134`:

```cvl
function _.getPastTotalSupply(uint256) external => NONDET;
function _.getPastVotes(address, uint256) external => NONDET;
```

Both reads are summarized as NONDET — the prover picks an arbitrary
uint256 per call. Worse, the wildcard form

```cvl
function _.someMethod(...) external => NONDET;
```

also covers `getPastOptimisticVotingSupply` automatically. So if the
fix were applied tomorrow and the contract switched from
`getPastTotalSupply` to `getPastOptimisticVotingSupply`, *the
identical spec verifies cleanly*. Our Certora rules don't distinguish
which downstream method is called.

## The general pattern

> Formal verification proves a system meets its spec.
> It cannot tell you the spec is wrong.

Wrong-spec bugs slip past every verification layer because each layer
is downstream of the spec. Rocq formalizes the spec. CAS witnesses
the spec numerically. Certora confirms the bytecode implements the
spec. None of those answers the question "is the spec the right
thing?"

The Cantina finding is a classic wrong-spec bug. Someone designed
the veto-threshold semantics around total supply when the model's
own logic dictates only opted-in voters should count toward the
denominator. Every layer of our stack faithfully encoded the wrong
intent.

## What kinds of bugs WE DO catch

To be fair to the stack: our verification *does* catch implementation
bugs — places where the code deviates from its documented spec. The
58 → 91 rule sweep in this branch has surfaced and fixed several of
these. Examples that the stack would catch:

- Guardian G6: a refactor that flipped `!=` to `==` on the Defeated
  check would now violate `cancelNonAdminRequiresNotDefeated`.
- UnstakingManager U8: a regression that double-incremented or
  skipped a nextLockId would violate `createLockIncrementsNextLockId`.
- Timelock T8/T9/T10: any change that disturbs unrelated operation
  slots during bypass/schedule/cancel would violate the parametric
  preservation rules.
- ThrottleLib T1: an unintentional change to the integer-divide
  direction in `consumeProposalCharge` would violate
  `consumeStorageDelta`.

These are all "implementation deviates from spec" bugs. The Cantina
finding was a different class: "spec is wrong."

## How to evolve the stack to catch wrong-spec bugs

Three approaches, in order of feasibility:

### 1. Property-from-intent, not property-from-code

When writing a CVL rule, do not derive the rule from reading the
implementation. Derive it from the *user-facing intent* and verify
against the implementation. For PR #36's bug, the intent property
would have been:

> The veto threshold should be reachable in principle by the set of
> voters who can actually cast vetoes.

In CVL terms:

```cvl
rule vetoThresholdReachableByEligibleVoters {
    env e;
    uint256 pid;
    require getProposalKind(pid) == OPTIMISTIC();

    uint256 thresholdTok = vetoThresholdInTokens(pid);
    uint256 eligibleSupply = sumOptimisticDelegateSupply(snapshot(pid));

    // The threshold must be at most the supply that could vote
    // (otherwise the proposal can never be defeated by legitimate vetoes)
    assert thresholdTok <= eligibleSupply,
        "veto threshold exceeds the supply that could cast vetoes";
}
```

The original code violates this: `eligibleSupply` is the optimistically-
delegated subset, but `thresholdTok` is computed from total supply. If
70% of supply is undelegated, the threshold can be set so high that no
legitimate veto coalition reaches it.

Writing this rule requires *domain understanding* — recognizing that
"set of voters who can veto" and "set of token holders" are different
populations. The Rocq/CAS/Certora stacks won't notice the difference
unless we tell them.

### 2. Adversarial-actor properties

Pose the question as an adversary: can a malicious party use a
known-permitted action to defeat a property? For PR #36:

> An adversary holds X tokens but does not delegate optimistically.
> Their tokens count toward `pastTotalSupply` (inflating the
> denominator) but not toward any vetoer's voting power. Result:
> the threshold-as-fraction-of-total-supply is unreachable; the
> proposal succeeds despite holding sufficient stakes to veto.

Translate that to CVL: pin one ghost account holding undelegated
tokens, prove the proposal does NOT defeat even when all delegated
voters cast vetoes. Such a rule would have flagged the bug.

The Foundry test added in PR #36
(`test_optimisticProposal_vetoThresholdUsesOptimisticDelegatedSupply`)
is exactly this adversarial property, written after the bug was
known. If similar tests existed before the audit, the bug would
have surfaced.

### 3. Cross-layer invariants

Use the Rocq simulation as a SOURCE of properties for Certora, not as
an oracle for the same answer. Specifically: when the Rocq sim takes
`pastSupply` as an opaque parameter, that's a signal — the sim
*itself* doesn't know which supply to use. That ambiguity is a place
to write a meta-rule: "the production contract MUST pass the supply
relevant to the voter set whose votes are aggregated against the
threshold."

This is harder to mechanize but conceptually sound: anywhere the
Rocq sim leaves a choice to the production contract, that's a place
where a wrong choice can hide.

## What this changes about our recommendations going forward

Add a new class of rules to the Certora coverage, separate from the
"per-contract correctness" rules: **intent-derived rules**, sourced
from documentation and design-doc claims rather than from code
inspection.

Candidates the team should write next:

1. **Veto-threshold reachability** (the PR #36 issue) — even though
   the contract is now fixed, write the rule as a regression guard.
2. **Throttle-bound under all proposers** — the `2*capacity` bound
   should hold under any sequence of proposers, not just the well-
   behaved cases. (Rocq has this; Certora doesn't.)
3. **Reward-accrual conservation under arbitrary token sequences** —
   `sum(claimed) + sum(accrued) <= sum(deposited rewards)` over any
   call trace.
4. **Auth-discriminator semantic intent** — for every role-gated
   function, the rule should be "this role cannot achieve outcome X
   without doing Y first." Stronger than the current "this role's
   callsite reverts on missing role."

The Cantina finding is a calibrating data point. Three independent
verification layers all missed a wrong-spec bug. That's not a defect
in any one layer — it's a property of the entire methodology. The
mitigation is to add an *intent-first* layer above the three
existing ones.
