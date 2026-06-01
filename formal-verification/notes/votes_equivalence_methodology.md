# OZ Votes equivalence — methodology memo (task #240)

This memo records the equivalence-proof methodology for OpenZeppelin's
abstract `Votes` base contract (`@openzeppelin/contracts@5.4.0`,
`governance/utils/Votes.sol`). The companion file is
`proofs/equivalence/Votes.v`.

The contract is abstract — its storage slots are reserved on the
*inheriting* contract, not on `Votes` itself. There is consequently no
standalone `Votes_shallow.v` from solc; the Yul-translation lands inside
each consumer's shallow form. The Reserve corpus has two prospective
consumers, both Phase 4 parked:

- `StakingVault` (issue #256): inherits `ERC20Votes` (which inherits
  `Votes`). Voting units = ERC20 balance.
- `ReserveOptimisticGovernor` (issue #244): consumes the `Votes`
  surface via `IVotes` (does not inherit it directly — it calls
  `getPastVotes` / `getPastTotalSupply` on the voting token).

So the question is structural, not mechanical: *where does the
Votes-specific equivalence reasoning live*, and how does it compose at
each concrete inheritance site when those contracts unpark?

## (A) Where does the Votes-specific reasoning live?

Three options:

### Option 1 — Inline at each inheritor
Duplicate every Votes lemma per inheriting contract: one copy in
`StakingVault.v`'s `_grantRole`-style chain, another in any future
`ERC20Votes` consumer that also inherits `Votes`. The two inheritors
share zero proof state — each must re-derive `_delegate` /
`_moveDelegateVotes` / `getPastVotes` walkers from scratch.

Pro: no abstraction overhead; everything is concrete at the call site.
Con: duplication grows linearly with the number of inheritors; a bug
in the Votes-specific reasoning has to be fixed in N places. For OZ-2
tier work we already pay the duplication tax on `nonReentrant` and
`_useCheckedNonce` because those don't carry storage state that varies
by inheritor; Votes carries three storage slots per inheritor, which
makes the duplication materially larger.

### Option 2 — Slot-agnostic helpers parameterized over slot indices (RECOMMENDED)
Hoist the Votes-specific reasoning into a standalone
`proofs/equivalence/Votes.v` whose section parameters are the three
slot indices `slot_delegatee`, `slot_delegate_ckpt`,
`slot_total_ckpt`. Each helper lemma states a property of the sim
(`mocks/Votes.v`) that is independent of where the inheritor lays out
the three slots in its storage list. The inheriting contract then
instantiates by passing concrete slot indices when it composes a
walker.

This matches the existing pattern in:

- `proofs/equivalence/Nonces.v` — abstract base, `with_useCheckedNonce`
  models the sequenced "check then body" call shape; sanity-check
  lemmas about the pure-Coq sim are stated independently of any
  concrete inheritor.
- `proofs/equivalence/EnumerableSet.v` — pure-function library, same
  shape: pure-Coq sanity-check lemmas + a documented expansion shape.
- `proofs/equivalence/Checkpoints.v` — Trace208 sanity-check
  proofs, no shallow form, mock-level only.

The Votes file lives one tier above all three: it depends on
`Nonces.v` (delegateBySig path), `Checkpoints.v` / `Trace208.v`
(per-delegate checkpoint history), and `mocks/Votes.v` (the
contract-level sim). The slot-agnostic helpers can compose against
*any* inheritor's projection so long as the projection lens (see (B))
is provided.

Pro: single source of truth for the Votes-specific reasoning. A bug
fix in `_moveDelegateVotes` reasoning lands once. Inheritor proofs
become "plug in the projection lens and the slot indices, the
abstract walker templates instantiate".
Con: slightly more abstraction to thread through; section parameters
add a small notation cost at call sites.

### Option 3 — Coq module functor over slot indices and projection lens
Same content as Option 2, but expressed as a `Module Type` / `Functor`
that the inheriting contract passes a projection module to. More
formal-looking, more orthogonal in principle.

In practice, no other file in this corpus uses functorial parametricity
this way — the established pattern is section parameters + opaque
`Parameter` declarations re-instantiated at call sites (see
`Guardian.v`'s role-bytes32 parameters, `AccessControlEnumerable.v`'s
re-import of `GuardianEquivalence`). Adopting a functor here would
introduce a new pattern for one file, raising the maintenance and
review cost of every subsequent Votes consumer.

### Decision: Option 2

The pattern is already proven on three abstract bases (Nonces,
EnumerableSet, Checkpoints). It composes downstream the way every
other file in `proofs/equivalence/` composes. Adopting it for Votes
keeps the corpus consistent and avoids inventing new infrastructure
for what is structurally the same problem.

If Option 1 or Option 3 turns out to be necessary when Phase 4 unparks
(e.g. if slot-aliasing constraints from the actual `StakingVault`
layout force the projection lens to be expressed differently), the
slot-agnostic helpers in `Votes.v` remain reusable — they're pure-Coq
sim properties. Only the walker templates / composition shape would
move.

## (B) The substorage lens

Each inheriting contract has its own `SimulatedStorage.t` list. Votes
contributes three slots to that list, but the inheritor decides where
they sit (Solc lays out storage in inheritance order; `StakingVault`
inherits `Votes` after `ERC20`, so the Votes slots come after the
ERC20 slots). The lens projects out the Votes sub-state:

```coq
Record votes_substorage_lens : Type := {
  read_delegatee     : SimulatedStorage.t -> Votes.Address -> Votes.Address;
  read_delegate_ckpt : SimulatedStorage.t -> Votes.Address -> Trace208.t;
  read_total_ckpt    : SimulatedStorage.t -> Trace208.t;
  read_voting_units  : SimulatedStorage.t -> Votes.Address -> Z;
  project            : SimulatedStorage.t -> Votes.State.t;
  lens_delegatee_correct :
    forall storage account,
      Votes.delegates (project storage) account = read_delegatee storage account;
  lens_delegate_ckpt_correct :
    forall storage account,
      (project storage).(Votes.State.delegate_ckpt) account
      = read_delegate_ckpt storage account;
  (* ... analogous correctness fields for total_ckpt, voting_units ... *)
}.
```

The `project` field is the lens — given an inheriting contract's
full simulated storage, it produces a Votes-side `State.t` with all
four/five fields populated (delegatee map, delegate-checkpoints map,
total-checkpoints, voting-units snapshot, clock). The first three are
genuine on-chain storage; `voting_units` is virtual — it's
`_getVotingUnits(account)` which is overridden by each inheritor
(ERC20Votes returns `balanceOf`; ERC721Votes returns `balanceOf` on
the token count). The lens captures both: the on-chain slots come
from the inheritor's projection, and `voting_units` is supplied by
the inheritor's own state (e.g. ERC20Votes' balance map).

For the methodology stub in `Votes.v`, we don't fix a concrete lens
— we declare it as a Section parameter and prove sim-level lemmas
that hold for any well-formed instantiation. The Section is closed
with the slot indices and lens still abstract; consumers re-open
and instantiate.

**Section parameter sketch (concrete code in `Votes.v`):**

```coq
Section VotesEquivalenceTemplate.
  (* Slot indices on the inheriting contract's SimulatedStorage. *)
  Variable slot_delegatee     : nat.
  Variable slot_delegate_ckpt : nat.
  Variable slot_total_ckpt    : nat.

  (* The projection lens — supplied by the inheritor. *)
  Variable project_votes : SimulatedStorage.t -> Votes.State.t.

  (* Lens correctness: the projection respects per-slot lookups. *)
  Hypothesis lens_reads_delegatee :
    forall storage account,
      Votes.delegates (project_votes storage) account =
      <delegatee-lookup at slot_delegatee>.
  (* ... analogous hypotheses for the other two slots ... *)

  (* Sim-level lemmas, walker templates, etc. *)
End VotesEquivalenceTemplate.
```

The `lens_reads_*` hypotheses are what each inheritor will discharge
when it instantiates the section — typically by `reflexivity` after
fixing its concrete `proj_sim` to put the Votes slots at known
indices.

## (C) Walker shapes per Votes operation

For each of the seven operations on the public Votes surface, the
walker decomposes into:

1. **Storage reads** at the three slots (the inheritor's
   `run_sload_*_at_proj_sim` lemmas, instantiated with the slot
   indices the lens identifies).
2. **Trace208 lookups / pushes** at the appropriate per-delegate
   checkpoint slot (the `Checkpoints.v` mock-level surface — already
   proved).
3. **Storage writes** at the slot(s) the operation mutates, using
   the wrapper-shape lemma the inheritor exposes (R040).
4. **Composition** of (1)-(3) into a single Hoare triple keyed by
   the pre/post state predicates.

For each operation we describe the abstract walker arms in comments
inside `Votes.v` — they cannot be made concrete because there is no
shallow form to point at — and supply sim-level helper lemmas that
each walker will reuse.

### View functions (read-only)

#### `delegates(account)` — 1 sload
Walker shape:

```
sload(<keccak(account, slot_delegatee)>)
  ↓ via R049 multi-slot Map2 sload bridge
Votes.delegates (project sim) account
```

Companion lemmas needed: lens correctness for `slot_delegatee` (one
of the `lens_reads_*` hypotheses above).

#### `getVotes(account)` — 1 sload + Trace208.latest
Walker shape:

```
sload(<keccak(account, slot_delegate_ckpt)>)   // load Trace208 storage
  ↓ Trace208.latest
Votes.getVotes (project sim) account
```

Companion lemmas needed: `delegate_ckpt_lens_correct`,
`Trace208.latest_after_<...>` (re-export from `Checkpoints.v`).

#### `getPastVotes(account, timepoint)` — 1 sload + Trace208.upperLookupRecent + revert path
Walker shape:

```
clock_check : if timepoint >= clock() then revert(ERC5805FutureLookup)
              else upperLookupRecent(_delegateCheckpoints[account], timepoint)
```

The clock comparison is a Yul `iszero(lt(...))` step. The revert
shape is documented but the walker proof can re-use the
abi-decoding revert sentinel pattern that `AbiEncoding.v` already
codifies (no new framework). For the success branch, the
`upperLookupRecent` step reuses
`Checkpoints.v::upper_lookup_below_first_is_zero` and its companion
lemmas.

Companion lemmas needed: a `getPastVotes_future_lookup_reverts` mock
sanity check; the success branch's `upperLookupRecent` discharge.

#### `getPastTotalSupply(timepoint)` — Same shape as `getPastVotes` at the total-checkpoints slot
Identical structure modulo the slot. Re-use the same revert-path
lemma. Companion lemmas needed: `total_ckpt_lens_correct`.

### Mutators

#### `_delegate(account, new_d)` — read-old + write-delegatee + moveDelegateVotes
Walker shape (three phases):

1. **Phase 1 (pre-state read):**
   ```
   old_d := sload(<keccak(account, slot_delegatee)>)
   units := <inheritor-virtual _getVotingUnits(account)>
   ```

2. **Phase 2 (delegatee sstore):**
   ```
   sstore(<keccak(account, slot_delegatee)>, new_d)
   ```
   This is a single-slot R040 wrapper-shape sstore.

3. **Phase 3 (_moveDelegateVotes composite):**
   See the next section. The composite migrates `units` from
   `old_d`'s checkpoint to `new_d`'s.

The composition theorem ties the three phases into a single Hoare
triple whose post-state matches `Votes.delegate sim account new_d`
under the lens.

Companion sim-level lemma the walker leverages:
`delegate_decomposes_via_moveDelegateVotes` — restates the mock's
`delegate` as "snapshot old delegate, sstore new delegate, then
`moveDelegateVotes`", which is exactly the Yul body shape (already
true by definition of `Votes.delegate` in the mock; the lemma is a
cosmetic re-expression that aligns the walker's intermediate states
with the mock's).

#### `_transferVotingUnits(from, to, amount)` — two conditional pushes + moveDelegateVotes
Walker shape:

```
if from == 0:  push(_totalCheckpoints, _add, amount)
if to   == 0:  push(_totalCheckpoints, _subtract, amount)
_moveDelegateVotes(delegates[from], delegates[to], amount)
```

The two conditional pushes against `_totalCheckpoints` are
distinct `sstore`s under R047 case-split (case-split before
`eexists`). Companion sim-level lemmas:

- `transferVotingUnits_mint_adds_to_total` (when `from = 0`):
  total checkpoint latest increases by `amount`.
- `transferVotingUnits_burn_subtracts_from_total` (when `to = 0`).
- `transferVotingUnits_pure_transfer_preserves_total` (when both
  `from` and `to` are nonzero).

These factor the case-split out of the walker proof — the walker
proves each branch, then re-assembles using a single observational
equivalence step.

#### `_moveDelegateVotes(from, to, amount)` — two conditional Trace208 pushes
Walker shape (the hardest one — it's the core voting-weight
migration):

```
if from != to and amount > 0:
  if from != 0:
    old_val := sload(<delegate_ckpt[from]>.latest_key)
    sstore(<delegate_ckpt[from]>, push_sub(old_val, amount))
  if to != 0:
    old_val := sload(<delegate_ckpt[to]>.latest_key)
    sstore(<delegate_ckpt[to]>, push_add(old_val, amount))
```

This is the composite of (a) a Trace208 read from one slot, (b) a
Trace208 push back to the same slot, (c) optionally the same pair
on the other slot. The two pushes share the same clock snapshot
(from the `clock()` external call, which in the inheritor is an
internal vm-clock read on `block.number`).

Companion sim-level lemmas (these are the executable ones in
`Votes.v`):

- `moveDelegateVotes_same_account_noop`: when `from = to`, the sim
  is unchanged.
- `moveDelegateVotes_zero_amount_noop`: when `amount = 0`, ditto.
- `moveDelegateVotes_other_delegates_untouched`: any delegate
  `c ∉ {from, to}` has its checkpoint history unchanged.
- `moveDelegateVotes_from_zero_skips_from_push`: when `from = 0`
  (mint path), no push against the from-delegate's checkpoint.
- `moveDelegateVotes_to_zero_skips_to_push`: dual.
- `getVotes_after_moveDelegateVotes_from`: `getVotes from` decreases
  by `amount` (when the from-branch fires).
- `getVotes_after_moveDelegateVotes_to`: dual increases.

These are all proved Qed against `mocks/Votes.v`; they're the
sim-side invariants the walker uses as post-state predicates.

### Where Phase 3's walker composition leverages Trace208

Both `_delegate` (via `_moveDelegateVotes`) and
`_transferVotingUnits` push into Trace208 storage. The walker arms
reduce each `Trace208.push` call site to `Checkpoints.v`'s sanity
lemmas, then chain through `Trace208.latest` for the
`getVotes`-side post-condition. The companion lemma surface in
`Votes.v` is exactly the bridge that turns Trace208-side facts into
Votes-side facts.

## (D) Parking realities and handoff

Concrete instantiation requires:

- A shallow form for an inheriting contract (StakingVault or a
  hypothetical pure-ERC20Votes consumer).
- A `proj_sim` for that contract that includes the three Votes slots
  at known indices.
- The contract's per-slot `run_sload_*_at_proj_sim` /
  `run_sstore_*_at_proj_sim` lemmas (per R049, R040).
- A discharge of the `lens_reads_*` hypotheses against the contract's
  `proj_sim`.

Both StakingVault (#256) and ReserveOptimisticGovernor (#244) are
Phase 4 parked. The methodology in `Votes.v` is therefore not yet
exercised against a concrete shallow form. The sim-level lemmas
(things provable against `mocks/Votes.v` alone) are closed with
Qed today; the walker templates are documented as comments referring
to the section parameters and the lens.

When Phase 4 unparks StakingVault, the next steps are (in order):

1. Generate `StakingVault_shallow.v` (currently blocked by R035 —
   switch-binding bug — and R046 — `sstore` drop). Both are
   upstream items in `shallow_embed.py`.
2. Author `proofs/equivalence/StakingVault.v` with the contract's
   own four-slot (or N-slot) `proj_sim`.
3. Instantiate `VotesEquivalence` with the three concrete slot
   indices and the projection lens, discharging the `lens_reads_*`
   hypotheses by `reflexivity` (or by a small `cbn; reflexivity`
   chain).
4. Compose the walker arms — every Votes call site in the
   StakingVault shallow form binds via the templates documented in
   the comments in `Votes.v`.

The R055/R059/R063 patterns (Guardian/AccessControl/staticcall)
compose orthogonally: where StakingVault inherits from both
`AccessControl` and `Votes`, the two abstract bases each instantiate
their own slot-agnostic helper file with their own slot indices,
and the inheritor's `proj_sim` carries the union of all required
slots.

## (E) Composition with other patterns

- **R049 (Map2 cons-to-front)** applies directly to the
  `_delegatee` mapping (single-level `address -> address`) and to
  each `_delegateCheckpoints[delegate]` after the per-delegate
  Trace208 storage is unfolded.
- **R055 (membership equivalence)** does *not* apply — Votes doesn't
  have a set-with-positions structure; the only addr-keyed mapping
  is `_delegatee` which is just a Map, not a Set.
- **R063 (staticcall)** does *not* apply to internal Votes
  call-sites — they're all inlined by Solc into the inheriting
  contract's runtime. Where the Governor calls Votes externally
  (e.g. `getPastVotes(token, ...)`), R063 will apply at the
  *Governor* side; the bridge proof re-uses Votes equivalence as a
  sub-Hoare-triple.
- **R046 (`sstore` drop)** affects every mutator path through Votes,
  including `_delegate`, `_transferVotingUnits`, and
  `_moveDelegateVotes`. The walker arms documented in `Votes.v`
  presume R046 is resolved upstream before any concrete walker is
  written.

## (F) Why this works without a shallow form today

The methodology is staged so the sim-level reasoning — which is the
hard part, structurally — closes today against the pure-Coq mock.
What remains for Phase 4 is wiring: hooking the walker into a
shallow-form-bound `run_sload_*_at_proj_sim` chain. That wiring is
mechanical once R035/R046 land and the inheritor's `proj_sim` is
chosen. The Votes-specific intuition (delegate-decrement + delegate-
increment migrates voting weight, the total-supply checkpoint moves
on mint/burn but not on transfer, `getPastVotes` is the
upper-bounded scan past a clock-checked timepoint) is already
captured in `mocks/Votes.v` and bridged in `proofs/equivalence/Votes.v`.

The companion lemma surface in `Votes.v` is the API future Phase 4
proofs will consume; nothing in those proofs needs to re-derive
Votes-side properties — they only have to discharge the projection
lens hypotheses.

## (G) Trust budget

The methodology adds no new axioms. The sim-level lemmas close
against `mocks/Votes.v` (`Votes.delegate`, `Votes.moveDelegateVotes`,
`Votes.getVotes`, `Votes.getPastVotes`) and the Trace208 surface
already proven in `mocks/Trace208.v`. `Print Assumptions` on any
closed lemma in `proofs/equivalence/Votes.v` shows only pre-existing
framework axioms (`Z`-arithmetic primitives carried by Coq's
standard library and the existing `keccak256_*_bound` axioms from
`Common.v`, neither of which are exercised by the sim-level lemmas
in this file).

When Phase 4 instantiates, the trust budget per inheriting contract
remains the standard R051 / R055 / R063 budget — 2-4 composite
axioms per mutator, same as every other equivalence file in the
corpus. The methodology in this file consumes no additional trust;
it just refactors the sim-side reasoning into a reusable layer.

## (H) Sizing

- `notes/votes_equivalence_methodology.md` (this file): ~340 lines.
- `proofs/equivalence/Votes.v`: 350-500 LOC. About 60% sim-level
  helper lemmas (Qed), 40% Section-parameter scaffolding +
  walker-template documentation (comments + section variable
  declarations, no Admitted).
- WISDOM section "Abstract-base-class equivalence": 30-40 lines.
- `_RocqProject` delta: 1 line.

Total under 1 000 LOC across all artifacts, well inside scope.
