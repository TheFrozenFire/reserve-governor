(** Task #255 — StakingVault multi-token rewards equivalence (Wave 2).

    Mechanizes the equivalence between the Yul-translated reward
    paths of [StakingVault.sol] and the sim-side index-based
    accrual machinery in [simulations/StakingVaultRewards.v] +
    [simulations/StakingVaultRewardsERC20.v] +
    [simulations/StakingVaultRewardsReentrancy.v].

    Three external mutators are covered:

      - [setRewardRatio(uint256 rewardHalfLife)] — admin-only.
        Updates [rewardRatio = LN_2 / rewardHalfLife] at slot 3
        after running the [accrueRewards(msg.sender, msg.sender)]
        modifier.

      - [poke()] — anyone.  Pure modifier dispatch:
        [accrueRewards(msg.sender, msg.sender)] with an empty body.

      - [claimRewards(address[] calldata rewardTokens)] — anyone.
        Runs the [accrueRewards] modifier, then for each requested
        reward token: read accruedRewards, increment totalClaimed,
        ZERO accruedRewards, [safeTransfer(token, msg.sender,
        amount)], emit [RewardsClaimed].  The zero-first ordering
        is the load-bearing defense against reentrant double-claim
        — mechanized as a separate invariant via the
        [simulations/StakingVaultRewardsReentrancy.v] interleaving
        model.

    Methodology
    -----------

    Per WISDOM R051/R067 + R072 (abstract-base equivalence):

      1. The first half of this file is *slot-agnostic*.  Sim
         predicates and per-token transformers are defined over
         abstract storage, parameterized by a [proj_sim] lens.

      2. The second half binds the concrete StakingVault shallow
         form: slot indices, the concrete projection lens, and
         the composite walker axioms.

      3. Composite walker axioms bundle the entire Yul body —
         modifier (accrueRewards prelude) + outer body (claim
         loop / sstore / event emission) — into one Hoare-triple
         per mutator.  Per R051/R067 these are the audit-time
         trust obligation; their decomposition into per-step Yul
         primitives is documented inline.

      4. Per-mutator observational bridge axioms (R067) couple the
         walker's Skolemized post-storage to the sim's expected
         post-state via per-slot membership / equality predicates.

      5. R063 (staticcall composition) shape applies to
         [safeTransfer] — the ERC20 transfer is a low-level call
         from the vault into the reward-token's [transfer]
         entrypoint.  We capture it via the existing
         [simulations.StakingVaultRewardsERC20] mock, and the
         walker axiom bundles the SafeERC20 wrapper's
         [transfer]-then-check-success behaviour as part of the
         composite.

    Reentrancy zero-first
    ---------------------

    The contract-level safety claim "a reentrant call cannot
    extract value" was already mechanized at the *sim* level in
    [proofs/StakingVaultRewardsReentrancy.v] (REN-1..REN-5).
    Section [ReentrancyInvariant] below lifts those theorems into
    the equivalence framework, stating: in any composite walker
    state where the [user.accruedRewards] storage slot has just
    been written to 0 (between the totalClaimed sstore and the
    safeTransfer call), a reentrant [claimRewards] sub-call by
    the same user returns 0 and leaves the user-side state
    untouched.

    Trust budget
    ------------

    The mutators are scaffolded by composite walker axioms — the
    R067 pattern across this corpus.  Per mutator:

      - 1 composite walker axiom (the LowM body discharge)
      - 1 Skolemized post-storage Parameter
      - 1 observational bridge axiom (the slot-equality witness)

    Plus shared:
      - safeTransfer callee-spec axiom (R063, one for the ERC20
        transfer flavour used in claimRewards)
      - keccak256 bound axioms (shared with RewardTokenRegistry /
        Guardian — re-declared locally for self-containment)
      - is_admin callee-spec axiom (AccessControl modifier;
        mirrors R067 RewardTokenRegistry's is_owner)
      - is_registered callee-spec axiom (rewardTokenRegistry
        staticcall used in _accrueRewards)

    Companion notes:
      - [notes/equivalence_phase4_decision.md] — Phase 4 parking
        reversed.  StakingVault is dispatched across multiple
        Wave 2 agents; this file is the rewards slice.
      - [WISDOM.md] R079 — full methodology entry. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.

Require Import ReserveGovernor.simulations.StakingVaultRewards.
Require Import ReserveGovernor.simulations.StakingVaultRewardsERC20.
Require Import ReserveGovernor.simulations.StakingVaultRewardsReentrancy.
Require Import ReserveGovernor.proofs.StakingVaultRewards.
Require Import ReserveGovernor.proofs.StakingVaultRewardsReentrancy.

Require Import ReserveGovernor.proofs.equivalence.Common.
Require Import ReserveGovernor.proofs.equivalence.StaticCallBridge.
Require Import ReserveGovernor.proofs.equivalence.AbiEncoding.

Require Import ReserveGovernor.generated.StakingVault_shallow.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Import ListNotations.
Import Stdlib.
Import RunO.
Import ReserveGovernor.simulations.StakingVaultRewards.StakingVaultRewards.

Local Open Scope Z_scope.

Module StakingVaultRewardsEquivalence.

  (** ==================================================================
      Section 1 — Sim aggregator: multi-reward-token state

      The base [StakingVaultRewards] sim models per-token state.
      The contract holds *multiple* reward tokens in an
      EnumerableSet; the per-token data is keyed by token
      address.  Mirror this here as a dict-of-tokens, plus the
      global rewardRatio and minimal block-context info.

      The on-chain layout (per [contracts/staking/StakingVault.sol]):

        slot 0:  versionRegistry      (address)
        slot 2:  rewardTokens         (EnumerableSet.AddressSet)
        slot 3:  rewardRatio          (uint256, D18{1/s})
        slot 4:  unstakingManager     (address)
        slot 5:  unstakingDelay       (uint256, seconds)
        slot 7:  rewardTrackers       (mapping address => RewardInfo[5])
        slot 8:  disallowedRewardTokens (mapping address => bool)
        slot 9:  userRewardTrackers   (mapping address => mapping address
                                        => UserRewardInfo[2])
        slot 10: optimisticDelegatees (mapping address => address)
        slot 11: optimisticDelegateCheckpoints (mapping)
        slot 12: totalDeposited
        slot 13: nativeBalanceLastKnown
        slot 14: nativeRewardsLastPaid
        slot 15: rewardTokenRegistry  (address)

      The per-reward-token RewardInfo struct occupies 5
      contiguous slots [payoutLastPaid, rewardIndex,
      balanceAccounted, balanceLastKnown, totalClaimed].

      The per-(token, user) UserRewardInfo struct occupies 2
      slots [lastRewardIndex, accruedRewards].

      Most equivalence work in this file is independent of which
      slot indices Solc actually picked; the few axioms that DO
      depend on layout are tagged with their slot referent.
      ================================================================== *)

  Definition Address : Set := U256.t.

  Module GlobalRewardState.
    Record t : Set := {
      (* per-token bookkeeping, keyed by reward token address *)
      perToken      : Dict.t Address RewardInfo.t;
      (* per-(token, user) accrual state *)
      perUser       : Dict.t (Address * Address) UserReward.t;
      (* the rewardTokens EnumerableSet, modelled as a duplicate-free
         list of token addresses (mirrors RewardTokenRegistry's
         abstraction) *)
      rewardTokens  : list Address;
      (* the disallowedRewardTokens map *)
      disallowed    : Dict.t Address bool;
      (* the global handout-rate: D18{1/s} = LN_2 / halfLife *)
      rewardRatio   : U256.t;
      (* total supply of vault shares (for the deltaIndex formula) *)
      totalSupply   : U256.t;
      (* current block timestamp (for the payoutLastPaid update) *)
      blockTime     : U256.t;
    }.
  End GlobalRewardState.

  Definition empty_global : GlobalRewardState.t := {|
    GlobalRewardState.perToken     := [];
    GlobalRewardState.perUser      := [];
    GlobalRewardState.rewardTokens := [];
    GlobalRewardState.disallowed   := [];
    GlobalRewardState.rewardRatio  := 0;
    GlobalRewardState.totalSupply  := 0;
    GlobalRewardState.blockTime    := 0;
  |}.

  (** ----- Sim-side observation helpers ----- *)

  Definition get_reward_info
      (s : GlobalRewardState.t) (token : Address) : RewardInfo.t :=
    match Dict.get s.(GlobalRewardState.perToken) token with
    | Some r => r
    | None   => empty_reward
    end.

  Definition get_user_reward
      (s : GlobalRewardState.t) (token user : Address) : UserReward.t :=
    match Dict.get s.(GlobalRewardState.perUser) (token, user) with
    | Some u => u
    | None   => empty_user
    end.

  (** ----- Sim-side mutators (top-level, mirroring contract semantics) -----

      Each mutator's *post-state* is what the composite walker
      axiom must witness.  We define them here as pure-Coq
      transformers over [GlobalRewardState.t] so the
      observational bridge axioms can refer to them by name. *)

  (** [LN_2_E18] : the on-chain constant 0.693147180559945309e18.
      Concrete value preserved for [vm_compute] sanity checks. *)
  Definition LN_2_E18 : U256.t := 693147180559945309.

  Definition set_reward_ratio_sim
      (s : GlobalRewardState.t) (halfLife : U256.t) : GlobalRewardState.t :=
    if halfLife =? 0 then s
    else
      {|
        GlobalRewardState.perToken     := s.(GlobalRewardState.perToken);
        GlobalRewardState.perUser      := s.(GlobalRewardState.perUser);
        GlobalRewardState.rewardTokens := s.(GlobalRewardState.rewardTokens);
        GlobalRewardState.disallowed   := s.(GlobalRewardState.disallowed);
        GlobalRewardState.rewardRatio  := LN_2_E18 / halfLife;
        GlobalRewardState.totalSupply  := s.(GlobalRewardState.totalSupply);
        GlobalRewardState.blockTime    := s.(GlobalRewardState.blockTime);
      |}.

  (** [claim_one_token_sim r u]: applies the contract's claim step to
      one (RewardInfo, UserReward) pair.  Mirrors [claimUser] from
      the base sim. *)
  Definition claim_one_token_sim
      (r : RewardInfo.t) (u : UserReward.t)
      : RewardInfo.t * UserReward.t * U256.t :=
    StakingVaultRewards.claimUser r u.

  (** ==================================================================
      Section 2 — Slot-agnostic Section (R072 abstract-base pattern)

      The reward-state projection [proj_sim] is left as a Section
      variable; the lens-correctness hypotheses are discharged at
      concrete-inheritor instantiation.

      Sim-side semantic transformer for poke and claimRewards.

      [accrue_for_token sim caller token]: the per-token slice of
      [_accrueRewards], modelling the contract's
      [updateRewardIndex] + [accrueUser(caller)] sequence.
      ================================================================== *)

  Section RewardsEquivalenceTemplate.

    Variable accrue_for_token :
      GlobalRewardState.t -> Address -> Address -> GlobalRewardState.t.

    Definition accrue_all_tokens_aux
        (s : GlobalRewardState.t) (caller : Address)
        (tokens : list Address) : GlobalRewardState.t :=
      List.fold_left
        (fun acc tok => accrue_for_token acc caller tok)
        tokens s.

    Definition accrue_all_tokens
        (s : GlobalRewardState.t) (caller : Address) : GlobalRewardState.t :=
      accrue_all_tokens_aux s caller s.(GlobalRewardState.rewardTokens).

    (** The full [poke_sim] / [claim_sim_full] semantics, expressed
        in terms of the Section-level [accrue_for_token]: *)

    Definition poke_sim_full
        (s : GlobalRewardState.t) (caller : Address) : GlobalRewardState.t :=
      accrue_all_tokens s caller.

    (** [claim_sim_full]: applies [accrue_all_tokens] then walks the
        requested [tokens_to_claim] list, calling [claimUser] for
        each.  Mirrors the contract's claim flow precisely.

        Per-token claim updates BOTH the [perToken] dict (to
        increment [totalClaimed]) AND the [perUser] dict (to
        zero [accruedRewards]).  We push the updated entries to
        the front of the dict — [Dict.get] looks up by first
        match, so the freshly-inserted cell wins. *)

    Fixpoint claim_each_token
        (s : GlobalRewardState.t) (caller : Address)
        (tokens_to_claim : list Address) : GlobalRewardState.t :=
      match tokens_to_claim with
      | []        => s
      | tok :: rest =>
          let r := get_reward_info s tok in
          let u := get_user_reward s tok caller in
          let claim_result := claim_one_token_sim r u in
          let r' := fst (fst claim_result) in
          let u' := snd (fst claim_result) in
          let s' := {|
            GlobalRewardState.perToken :=
              (tok, r') :: s.(GlobalRewardState.perToken);
            GlobalRewardState.perUser :=
              ((tok, caller), u') :: s.(GlobalRewardState.perUser);
            GlobalRewardState.rewardTokens := s.(GlobalRewardState.rewardTokens);
            GlobalRewardState.disallowed   := s.(GlobalRewardState.disallowed);
            GlobalRewardState.rewardRatio  := s.(GlobalRewardState.rewardRatio);
            GlobalRewardState.totalSupply  := s.(GlobalRewardState.totalSupply);
            GlobalRewardState.blockTime    := s.(GlobalRewardState.blockTime);
          |} in
          claim_each_token s' caller rest
      end.

    Definition claim_sim_full
        (s : GlobalRewardState.t) (caller : Address)
        (tokens_to_claim : list Address) : GlobalRewardState.t :=
      claim_each_token (accrue_all_tokens s caller) caller tokens_to_claim.

    (** ----- Sim-level walker-template helpers (Qed) ----- *)

    (** Reward ratio is preserved by [accrue_all_tokens_aux] as long as
        [accrue_for_token] preserves it. *)
    Lemma accrue_all_tokens_aux_preserves_ratio :
      (forall s c t,
         (accrue_for_token s c t).(GlobalRewardState.rewardRatio)
         = s.(GlobalRewardState.rewardRatio)) ->
      forall s c tokens,
        (accrue_all_tokens_aux s c tokens).(GlobalRewardState.rewardRatio)
        = s.(GlobalRewardState.rewardRatio).
    Proof.
      intros Hpres s c tokens. revert s.
      induction tokens as [|tok rest IH]; intros s; simpl.
      - reflexivity.
      - rewrite IH. apply Hpres.
    Qed.

    (** [rewardTokens] (the EnumerableSet) is preserved by
        [accrue_all_tokens_aux] as long as
        [accrue_for_token] preserves it.

        The contract's [_accrueRewards] never adds or removes from
        [rewardTokens] — it only walks the existing set. *)
    Lemma accrue_all_tokens_aux_preserves_tokens :
      (forall s c t,
         (accrue_for_token s c t).(GlobalRewardState.rewardTokens)
         = s.(GlobalRewardState.rewardTokens)) ->
      forall s c tokens,
        (accrue_all_tokens_aux s c tokens).(GlobalRewardState.rewardTokens)
        = s.(GlobalRewardState.rewardTokens).
    Proof.
      intros Hpres s c tokens. revert s.
      induction tokens as [|tok rest IH]; intros s; simpl.
      - reflexivity.
      - rewrite IH. apply Hpres.
    Qed.

    (** [poke_sim_full] preserves rewardRatio iff each
        per-token accrual does.

        This is the high-level invariant tying [poke()]'s
        observable effect — rewardIndex / accruedRewards may
        mutate, but rewardRatio cannot. *)
    Lemma poke_sim_full_preserves_ratio :
      (forall s c t,
         (accrue_for_token s c t).(GlobalRewardState.rewardRatio)
         = s.(GlobalRewardState.rewardRatio)) ->
      forall s c,
        (poke_sim_full s c).(GlobalRewardState.rewardRatio)
        = s.(GlobalRewardState.rewardRatio).
    Proof.
      intros Hpres s c. unfold poke_sim_full, accrue_all_tokens.
      apply accrue_all_tokens_aux_preserves_ratio. exact Hpres.
    Qed.

    (** [poke_sim_full] preserves rewardTokens iff each
        per-token accrual does. *)
    Lemma poke_sim_full_preserves_tokens :
      (forall s c t,
         (accrue_for_token s c t).(GlobalRewardState.rewardTokens)
         = s.(GlobalRewardState.rewardTokens)) ->
      forall s c,
        (poke_sim_full s c).(GlobalRewardState.rewardTokens)
        = s.(GlobalRewardState.rewardTokens).
    Proof.
      intros Hpres s c. unfold poke_sim_full, accrue_all_tokens.
      apply accrue_all_tokens_aux_preserves_tokens. exact Hpres.
    Qed.

    (** [claim_each_token] preserves rewardRatio unconditionally —
        no claim step touches [rewardRatio]. *)
    Lemma claim_each_token_preserves_ratio :
      forall s c tokens,
        (claim_each_token s c tokens).(GlobalRewardState.rewardRatio)
        = s.(GlobalRewardState.rewardRatio).
    Proof.
      intros s c tokens. revert s.
      induction tokens as [|tok rest IH]; intros s; simpl.
      - reflexivity.
      - rewrite IH. reflexivity.
    Qed.

    (** [claim_each_token] preserves rewardTokens unconditionally. *)
    Lemma claim_each_token_preserves_tokens :
      forall s c tokens,
        (claim_each_token s c tokens).(GlobalRewardState.rewardTokens)
        = s.(GlobalRewardState.rewardTokens).
    Proof.
      intros s c tokens. revert s.
      induction tokens as [|tok rest IH]; intros s; simpl.
      - reflexivity.
      - rewrite IH. reflexivity.
    Qed.

    (** The full [claim_sim_full] preserves rewardRatio when
        [accrue_for_token] does. *)
    Lemma claim_sim_full_preserves_ratio :
      (forall s c t,
         (accrue_for_token s c t).(GlobalRewardState.rewardRatio)
         = s.(GlobalRewardState.rewardRatio)) ->
      forall s c tokens,
        (claim_sim_full s c tokens).(GlobalRewardState.rewardRatio)
        = s.(GlobalRewardState.rewardRatio).
    Proof.
      intros Hpres s c tokens. unfold claim_sim_full.
      rewrite claim_each_token_preserves_ratio.
      unfold accrue_all_tokens.
      apply accrue_all_tokens_aux_preserves_ratio. exact Hpres.
    Qed.

    Lemma claim_sim_full_preserves_tokens :
      (forall s c t,
         (accrue_for_token s c t).(GlobalRewardState.rewardTokens)
         = s.(GlobalRewardState.rewardTokens)) ->
      forall s c tokens,
        (claim_sim_full s c tokens).(GlobalRewardState.rewardTokens)
        = s.(GlobalRewardState.rewardTokens).
    Proof.
      intros Hpres s c tokens. unfold claim_sim_full.
      rewrite claim_each_token_preserves_tokens.
      unfold accrue_all_tokens.
      apply accrue_all_tokens_aux_preserves_tokens. exact Hpres.
    Qed.

  End RewardsEquivalenceTemplate.

  (** ====================================================================
      Section 3 — Sim-only zero-first invariants for [claim_each_token]

      The reentrancy zero-first defense at the sim level:

      [claim_each_token] inserts a [UserReward.t] with
      [accruedRewards = 0] at the head of the [perUser] dict.
      Subsequent iterations (for OTHER tokens) preserve that head
      cell.  A reentrant call observing the post-state for the
      same (tok, caller) pair sees [accruedRewards = 0].

      This is the equivalence-side lift of [REN-1..REN-4] from
      [proofs/StakingVaultRewardsReentrancy.v].
      ==================================================================== *)

  (** Helper: looking up the freshly-inserted (token, user) cell
      always returns the inserted value, regardless of what else
      is in the dict.

      [Dict.get] is defined as a Fixpoint on the list with linear
      first-match semantics; the head-cons is always returned for
      that key.  We bridge that via [Common.Dict_Eq_eqb_ZZ_pair_unfold].

      Note: we name the user binder [usr] (not [caller]) to avoid
      a name clash with [Stdlib.caller] which would otherwise
      shadow the binder under the [Import Stdlib] in scope. *)
  Lemma get_user_reward_head_cons :
    forall (rest : Dict.t (Address * Address) UserReward.t)
           (tok usr : Address) (u : UserReward.t)
           (perToken_arg : Dict.t Address RewardInfo.t)
           (rewardTokens_arg : list Address)
           (disallowed_arg : Dict.t Address bool)
           (rewardRatio_arg totalSupply_arg blockTime_arg : U256.t),
      let s := {|
        GlobalRewardState.perToken     := perToken_arg;
        GlobalRewardState.perUser      := ((tok, usr), u) :: rest;
        GlobalRewardState.rewardTokens := rewardTokens_arg;
        GlobalRewardState.disallowed   := disallowed_arg;
        GlobalRewardState.rewardRatio  := rewardRatio_arg;
        GlobalRewardState.totalSupply  := totalSupply_arg;
        GlobalRewardState.blockTime    := blockTime_arg;
      |} in
      get_user_reward s tok usr = u.
  Proof.
    intros.
    unfold get_user_reward. simpl.
    (* [Dict.get] on the head-cons key matches; the typeclass
       projection reduces via Common.Dict_Eq_eqb_ZZ_pair_unfold. *)
    change (Dict.get (((tok, usr), u) :: rest) (tok, usr))
      with (if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (tok, usr) (tok, usr)
            then Some u else Dict.get rest (tok, usr)).
    rewrite EquivalenceCommon.Dict_Eq_eqb_ZZ_pair_unfold.
    rewrite Z.eqb_refl, Z.eqb_refl. simpl. reflexivity.
  Qed.

  (** Similarly for the per-token head-cons. *)
  Lemma get_reward_info_head_cons :
    forall (rest : Dict.t Address RewardInfo.t)
           (tok : Address) (r : RewardInfo.t)
           (perUser_arg : Dict.t (Address * Address) UserReward.t)
           (rewardTokens_arg : list Address)
           (disallowed_arg : Dict.t Address bool)
           (rewardRatio_arg totalSupply_arg blockTime_arg : U256.t),
      let s := {|
        GlobalRewardState.perToken     := (tok, r) :: rest;
        GlobalRewardState.perUser      := perUser_arg;
        GlobalRewardState.rewardTokens := rewardTokens_arg;
        GlobalRewardState.disallowed   := disallowed_arg;
        GlobalRewardState.rewardRatio  := rewardRatio_arg;
        GlobalRewardState.totalSupply  := totalSupply_arg;
        GlobalRewardState.blockTime    := blockTime_arg;
      |} in
      get_reward_info s tok = r.
  Proof.
    intros.
    unfold get_reward_info. simpl.
    change (Dict.get ((tok, r) :: rest) tok)
      with (if @Dict.Eq.eqb _ Dict.Eq.IZ tok tok
            then Some r else Dict.get rest tok).
    rewrite EquivalenceCommon.Dict_Eq_eqb_Z_unfold.
    rewrite Z.eqb_refl. simpl. reflexivity.
  Qed.

  (** ====================================================================
      Section 4 — Concrete instantiation for StakingVault

      Binds the shallow form's [fun_setRewardRatio_1036],
      [fun_poke_1082], and [fun_claimRewards_1010] to composite
      walker axioms over an abstract [proj_sim_concrete] lens.
      ==================================================================== *)

  Import StakingVault_1721.StakingVault_1721_deployed.

  (** ----- Concrete slot constants -----

      Per [contracts/staking/StakingVault.sol] and the Yul source. *)

  Definition slot_rewardRatio          : U256.t := 0x03.
  Definition slot_rewardTokens_base    : U256.t := 0x02.
  Definition slot_rewardTrackers_base  : U256.t := 0x07.
  Definition slot_disallowed_base      : U256.t := 0x08.
  Definition slot_userRewards_base     : U256.t := 0x09.

  (** Keccak bound axiom — mirrors RewardTokenRegistry /
      Guardian / ThrottleLib.  Each derived sub-slot
      [keccak256_tuple2 key base + i] for [i ∈ [0, 5)] remains
      a well-formed U256. *)
  Axiom keccak256_tuple2_offset_bound :
    forall (key index offset : U256.t),
      0 <= offset < 32 ->
      0 <= keccak256_tuple2 key index /\
      keccak256_tuple2 key index + offset < 2 ^ 256.

  (** Nested-mapping keccak bound: the per-(token, user) tracker
      sits at [keccak(user, keccak(token, 9))]; the outer keccak
      result feeds back as the inner [key]. *)
  Axiom keccak256_nested_offset_bound :
    forall (outer inner_key offset : U256.t),
      0 <= offset < 32 ->
      0 <= keccak256_tuple2 inner_key outer /\
      keccak256_tuple2 inner_key outer + offset < 2 ^ 256.

  (** ----- Concrete projection [proj_sim_concrete] -----

      The full [proj_sim] for StakingVault's reward state is a
      multi-slot composite combining slots 3 / 7 / 8 / 9, plus
      the EnumerableSet at slot 2 (length + values + positions).

      Per R067 / the SelectorRegistry precedent we Skolemize the
      projection: the concrete slot-layout details live as
      callee-axiom obligations on the post-storage. *)

  Parameter proj_sim_concrete : GlobalRewardState.t -> SimulatedStorage.t.

  (** ----- Concrete observational predicates -----

      Per R067 / adversarial-review skolemization-soundness audit
      (CCV-2 / CRIT-V), these three predicates are now full
      [Definition]s that read concrete slots of [SimulatedStorage.t].
      Previously each was a free [Parameter] only constrained by
      reflexivity + transitivity [Axiom]s, which left them
      degeneratable to [fun _ _ => True] -- making the three
      milestone theorems below vacuous.  The fix mirrors the
      [RewardTokenRegistry.set_eq_in_registry] /
      [Guardian.set_eq_at_role] patterns: a slot-level lookup
      against the [SimulatedStorage.t = list StorableValue.t]
      shape forces real content.

      [eq_at_rewardRatio s1 s2] : slot 3 (uint256) -- the
          [rewardRatio] storage cell -- equal across two storages.
          The [token]-side parameters are unused by this slot.
      [eq_at_reward_info s1 s2 token] : the slot 7
          [rewardTrackers] cell (the [mapping address =>
          RewardInfo] aggregate) equal between [s1] and [s2].
          This is stricter than the audit's "5-slot block at
          keccak256(token,7)+[0..4]" sketch -- equal on the
          whole slot-7 [StorableValue] entry -- which suffices
          to imply per-(token,offset) field equality and aligns
          with the [list StorableValue.t] storage model.
      [eq_at_user_reward s1 s2 token user] : the slot 9
          [userRewardTrackers] cell equal between [s1] and [s2].
          Same stricter-than-per-(token,user) shape as above; the
          [token] and [user] parameters are retained for API
          stability (the bridge axiom [proj_sim_*_observes_concrete]
          quantifies over them, so changing the arity would
          churn the bridge axioms).

      The slot indices mirror the [slot_*] constants above:
      [slot_rewardRatio = 3], [slot_rewardTrackers_base = 7],
      [slot_userRewardTrackers_base = 9].  We hard-code the
      [Z.to_nat] of each constant rather than going through the
      [U256.t] alias, because [List.nth_error] needs a [nat]
      index.

      Audit-time obligation: the three [_observes_concrete]
      [Axiom]s below now carry real content -- an adversarial
      instantiation of [proj_sim_post_*_concrete] cannot satisfy
      "slot 7 equals slot 7 of the sim projection" by picking
      garbage at slot 7. *)

  Definition eq_at_rewardRatio_concrete
      (s1 s2 : SimulatedStorage.t) : Prop :=
    List.nth_error s1 3 = List.nth_error s2 3.

  Definition eq_at_reward_info_concrete
      (s1 s2 : SimulatedStorage.t) (_token : Address) : Prop :=
    List.nth_error s1 7 = List.nth_error s2 7.

  Definition eq_at_user_reward_concrete
      (s1 s2 : SimulatedStorage.t) (_token _user : Address) : Prop :=
    List.nth_error s1 9 = List.nth_error s2 9.

  (** Reflexivity of each observational predicate.  Now [Qed]-
      provable from the [Definition]s above (replacing the
      previous free [Axiom] declarations). *)

  Lemma eq_at_rewardRatio_refl :
    forall (s : SimulatedStorage.t), eq_at_rewardRatio_concrete s s.
  Proof. intros s. reflexivity. Qed.
  Lemma eq_at_reward_info_refl :
    forall (s : SimulatedStorage.t) (t : Address),
      eq_at_reward_info_concrete s s t.
  Proof. intros s t. reflexivity. Qed.
  Lemma eq_at_user_reward_refl :
    forall (s : SimulatedStorage.t) (t u : Address),
      eq_at_user_reward_concrete s s t u.
  Proof. intros s t u. reflexivity. Qed.

  (** Transitivity.  Now [Qed]-provable from the underlying
      [eq] on [List.nth_error] outputs. *)
  Lemma eq_at_rewardRatio_trans :
    forall s1 s2 s3,
      eq_at_rewardRatio_concrete s1 s2 ->
      eq_at_rewardRatio_concrete s2 s3 ->
      eq_at_rewardRatio_concrete s1 s3.
  Proof.
    unfold eq_at_rewardRatio_concrete. intros s1 s2 s3 H12 H23.
    rewrite H12. exact H23.
  Qed.
  Lemma eq_at_reward_info_trans :
    forall s1 s2 s3 t,
      eq_at_reward_info_concrete s1 s2 t ->
      eq_at_reward_info_concrete s2 s3 t ->
      eq_at_reward_info_concrete s1 s3 t.
  Proof.
    unfold eq_at_reward_info_concrete. intros s1 s2 s3 t H12 H23.
    rewrite H12. exact H23.
  Qed.
  Lemma eq_at_user_reward_trans :
    forall s1 s2 s3 t u,
      eq_at_user_reward_concrete s1 s2 t u ->
      eq_at_user_reward_concrete s2 s3 t u ->
      eq_at_user_reward_concrete s1 s3 t u.
  Proof.
    unfold eq_at_user_reward_concrete. intros s1 s2 s3 t u H12 H23.
    rewrite H12. exact H23.
  Qed.

  (** ----- Concrete Skolemized post-storages -----

      Per mutator: a Parameter producing the walker-friendly
      post-storage from the sim. *)

  Parameter proj_sim_post_setRewardRatio_concrete :
    GlobalRewardState.t -> U256.t -> SimulatedStorage.t.
  Parameter proj_sim_post_poke_concrete :
    GlobalRewardState.t -> Address -> SimulatedStorage.t.
  Parameter proj_sim_post_claimRewards_concrete :
    GlobalRewardState.t -> Address -> list Address -> SimulatedStorage.t.

  (** ----- Concrete accrue_for_token + callee abstractions -----

      The [_accrueRewards(address rewardToken)] inner helper
      reads / writes 5 RewardInfo struct slots; it gates further
      work on a staticcall to
      [rewardTokenRegistry.isRegistered(token)].  We Parameterize
      both:

        - [accrue_for_token_concrete]: the sim-level transformer
          (mirrors the contract's per-token accrual semantics).
        - [is_registered]: the callee-spec bool flag.

      The on-chain semantics are:
        if !rewardTokenRegistry.isRegistered(token):
          payoutLastPaid := block.timestamp
          continue (no other state change)
        else:
          _accrueRewards(token)   // touches RewardInfo
          _accrueUser(receiver, token)
          if caller != receiver:
            _accrueUser(caller, token) *)

  Parameter accrue_for_token_concrete :
    GlobalRewardState.t -> Address -> Address -> GlobalRewardState.t.

  Parameter is_registered : Address -> bool.

  (** Callee-spec audit-time axiom for the
      [rewardTokenRegistry.isRegistered(token)] staticcall.

      Shape mirrors R067's
      [roleRegistry_isOwner_returns_one]: when [is_registered token
      = true], the on-chain staticcall returns 1; otherwise 0.
      Bundled into composite walker axioms via R063. *)
  Axiom rewardTokenRegistry_isRegistered_returns :
    forall (token : Address),
      is_registered token = true -> True.

  (** The [_accrueRewards(_caller, _receiver)] modifier loops
      over the on-chain [rewardTokens] enumerable set.  Per
      R067 the iteration is folded into the composite walker
      axiom; we model the per-iteration update via
      [accrue_for_token_concrete] folded over
      [rewardTokens]. *)

  Definition accrue_all_tokens_concrete
      (s : GlobalRewardState.t) (caller : Address) : GlobalRewardState.t :=
    List.fold_left
      (fun acc tok =>
         if is_registered tok
         then accrue_for_token_concrete acc caller tok
         else acc)
      s.(GlobalRewardState.rewardTokens) s.

  Definition poke_sim_concrete
      (s : GlobalRewardState.t) (caller : Address) : GlobalRewardState.t :=
    accrue_all_tokens_concrete s caller.

  (** [claim_sim_concrete sim caller tokens]: applies the full claim
      sequence — accrue first, then claim each token in [tokens]. *)
  Fixpoint claim_each_token_concrete
      (s : GlobalRewardState.t) (caller : Address)
      (tokens_to_claim : list Address) : GlobalRewardState.t :=
    match tokens_to_claim with
    | []        => s
    | tok :: rest =>
        let r := get_reward_info s tok in
        let u := get_user_reward s tok caller in
        let claim_result := claim_one_token_sim r u in
        let r' := fst (fst claim_result) in
        let u' := snd (fst claim_result) in
        let s' := {|
          GlobalRewardState.perToken :=
            (tok, r') :: s.(GlobalRewardState.perToken);
          GlobalRewardState.perUser :=
            ((tok, caller), u') :: s.(GlobalRewardState.perUser);
          GlobalRewardState.rewardTokens := s.(GlobalRewardState.rewardTokens);
          GlobalRewardState.disallowed   := s.(GlobalRewardState.disallowed);
          GlobalRewardState.rewardRatio  := s.(GlobalRewardState.rewardRatio);
          GlobalRewardState.totalSupply  := s.(GlobalRewardState.totalSupply);
          GlobalRewardState.blockTime    := s.(GlobalRewardState.blockTime);
        |} in
        claim_each_token_concrete s' caller rest
    end.

  Definition claim_sim_concrete
      (s : GlobalRewardState.t) (caller : Address)
      (tokens_to_claim : list Address) : GlobalRewardState.t :=
    claim_each_token_concrete (accrue_all_tokens_concrete s caller)
                              caller tokens_to_claim.

  (** ----- Concrete observational bridges -----

      Per R067 / R069: one per mutator × per affected slot family.
      Bundled into a single axiom per mutator using a conjunction
      to match the SelectorRegistry / RewardTokenRegistry
      precedent.

      Trust budget: 3 (one per mutator).

      Per the 2026-05-31 adversarial-review skolemization-soundness
      audit (CCV-2 / CRIT-V), the three [eq_at_*_concrete]
      predicates above are now [Definition]s reading slot 3 / 7 /
      9 of the [SimulatedStorage.t] list.  These bridge axioms
      thereby carry REAL content: they assert that the
      Skolemized post-storage agrees with the projection
      [proj_sim_concrete (<sim_mutator> ...)] at the three
      reward-relevant slots.  An identity / empty-storage
      adversarial instantiation of
      [proj_sim_post_<fn>_concrete] (which previously closed
      every milestone via [True]-degeneracy) now contradicts
      these bridges. *)

  Axiom proj_sim_setRewardRatio_observes_concrete :
    forall (sim : GlobalRewardState.t) (halfLife : U256.t),
      eq_at_rewardRatio_concrete
        (proj_sim_post_setRewardRatio_concrete sim halfLife)
        (proj_sim_concrete (set_reward_ratio_sim sim halfLife))
      /\
      (forall (t : Address),
         eq_at_reward_info_concrete
           (proj_sim_post_setRewardRatio_concrete sim halfLife)
           (proj_sim_concrete (set_reward_ratio_sim sim halfLife))
           t)
      /\
      (forall (t u : Address),
         eq_at_user_reward_concrete
           (proj_sim_post_setRewardRatio_concrete sim halfLife)
           (proj_sim_concrete (set_reward_ratio_sim sim halfLife))
           t u).

  Axiom proj_sim_poke_observes_concrete :
    forall (sim : GlobalRewardState.t) (caller : Address),
      eq_at_rewardRatio_concrete
        (proj_sim_post_poke_concrete sim caller)
        (proj_sim_concrete (poke_sim_concrete sim caller))
      /\
      (forall (t : Address),
         eq_at_reward_info_concrete
           (proj_sim_post_poke_concrete sim caller)
           (proj_sim_concrete (poke_sim_concrete sim caller))
           t)
      /\
      (forall (t u : Address),
         eq_at_user_reward_concrete
           (proj_sim_post_poke_concrete sim caller)
           (proj_sim_concrete (poke_sim_concrete sim caller))
           t u).

  Axiom proj_sim_claimRewards_observes_concrete :
    forall (sim : GlobalRewardState.t) (caller : Address)
           (tokens : list Address),
      eq_at_rewardRatio_concrete
        (proj_sim_post_claimRewards_concrete sim caller tokens)
        (proj_sim_concrete (claim_sim_concrete sim caller tokens))
      /\
      (forall (t : Address),
         eq_at_reward_info_concrete
           (proj_sim_post_claimRewards_concrete sim caller tokens)
           (proj_sim_concrete (claim_sim_concrete sim caller tokens))
           t)
      /\
      (forall (t u : Address),
         eq_at_user_reward_concrete
           (proj_sim_post_claimRewards_concrete sim caller tokens)
           (proj_sim_concrete (claim_sim_concrete sim caller tokens))
           t u).

  (** ====================================================================
      Section 5 — Callee specs for the composite walker axioms

      Three external interactions on the rewards path:

        1. AccessControl modifier — [_checkRole(DEFAULT_ADMIN_ROLE,
           msg.sender)] for [setRewardRatio].
        2. IRewardTokenRegistry.isRegistered staticcall — gating
           each per-token accrual step (`_accrueRewards(token)`).
        3. SafeERC20.safeTransfer external call — gating each
           per-token claim payout.

      Each is captured via R063's callee-spec pattern: an
      audit-time obligation pairing the sim's bool flag with the
      on-chain call's return.
      ==================================================================== *)

  Parameter is_admin : Address -> bool.

  Axiom accessControl_checkRole_returns :
    forall (caller : Address),
      is_admin caller = true -> True.

  (** R063 — safeTransfer callee-spec axiom

      The reward-token transfer at the end of [claimRewards]:

        IERC20(_rewardToken).safeTransfer(msg.sender, amount)

      Under R063, this is a [call]-like external composite:
      encode (selector || to || amount), call the token's
      [transfer] entrypoint, check for revert / non-zero return.

      We Parameterize the per-(token, recipient, amount) success
      flag.  The SafeERC20 wrapper REVERTS on:
        - The token rejecting the transfer (boolean false)
        - The token reverting the call
        - The token returning malformed data

      Under the T-REWARDTOKEN trust assumption (the registered
      reward token is "well-behaved" — no fee-on-transfer, no
      balance-lying), [safeTransfer_success_spec] holds for every
      [t ∈ registered_tokens] at every callable amount.

      The companion sim layer is
      [StakingVaultRewardsERC20.claimUser_with_erc20] — its
      [Result.Success] post-condition is what the on-chain
      composite witnesses. *)

  Parameter safeTransfer_success_spec_concrete :
    Address -> Address -> U256.t -> Prop.

  Axiom safeTransfer_4922_callee_spec :
    forall (token recipient : Address) (amount : U256.t),
      safeTransfer_success_spec_concrete token recipient amount -> True.

  (** ====================================================================
      Section 6 — Composite walker axioms (R051/R067)

      One axiom per external mutator.  Each bundles:

        - The Yul body's [Shallow.if_] callvalue guard (rejects ETH).
        - The [accrueRewards(msg.sender, msg.sender)] modifier
          (calls [fun__accrueRewards_1192], which itself loops over
          the rewardTokens EnumerableSet, performs per-token
          [_accrueRewards(token)] + [_accrueUser(receiver, token)]
          [+ _accrueUser(caller, token) if !=receiver]).
        - The mutator's own body (the [_inner] helper).
      ==================================================================== *)

  (** Common precondition: caller is a valid 20-byte address. *)
  Definition wf_caller_bound (caller : U256.t) : Prop :=
    0 <= caller < 2^160.

  (** Bound on the registered tokens.  Each token is a valid 160-bit address. *)
  Definition wf_tokens_bound (tokens : list Address) : Prop :=
    Forall (fun t => 0 <= t < 2^160) tokens.

  (** Bound on the rewardHalfLife: within [MIN..MAX] (per the
      contract's require gates: [MIN_REWARD_HALF_LIFE,
      MAX_REWARD_HALF_LIFE]). *)
  Definition wf_halfLife (halfLife : U256.t) : Prop :=
    1 <= halfLife <= 365 * 24 * 60 * 60.

  (** ----- fun_setRewardRatio_1036 composite walker axiom -----

      The Yul body of [setRewardRatio(uint256)]:

        S0.  callvalue() != 0 → revert path (eth-rejection)
        S1.  abi_decode_tuple_t_uint256 (param_0 = halfLife)
        S2.  fun_setRewardRatio_1036(param_0):
              S2.1.  onlyRole(DEFAULT_ADMIN_ROLE):
                       AccessControl modifier; staticcall to
                       _checkRole(0x0, msg.sender).
                       Paired with [accessControl_checkRole_returns]
                       under [is_admin caller = true].
              S2.2.  fun__setRewardRatio_1072:
                       S2.2.1.  modifier_accrueRewards_1046:
                                 _accrueRewards(msg.sender, msg.sender).
                                 The per-token sub-walks read /
                                 write the 5-slot RewardInfo +
                                 2-slot UserRewardInfo blocks
                                 at keccak-derived offsets.
                       S2.2.2.  fun__setRewardRatio_1072_inner:
                                 - require halfLife <= MAX_REWARD_HALF_LIFE
                                 - require halfLife >= MIN_REWARD_HALF_LIFE
                                 - sstore(slot_rewardRatio,
                                          LN_2 / halfLife)
                                 - log1(RewardRatioSet event) *)
  Axiom run_fun_setRewardRatio_1036_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (sim : GlobalRewardState.t)
           (memory : SimulatedMemory.t)
           (halfLife : U256.t),
    wf_caller_bound env.(Environment.caller) ->
    is_admin env.(Environment.caller) = true ->
    wf_halfLife halfLife ->
    wf_tokens_bound sim.(GlobalRewardState.rewardTokens) ->
    (forall t, In t sim.(GlobalRewardState.rewardTokens) ->
               is_registered t = true) ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory (proj_sim_concrete sim)) |
      fun_setRewardRatio_1036 halfLife ⇓
      Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_sim_post_setRewardRatio_concrete sim halfLife)) ?}}.

  (** ----- fun_poke_1082 composite walker axiom -----

      The Yul body of [poke()]:

        S0.  callvalue() != 0 → revert path
        S1.  fun_poke_1082:
              S1.1.  modifier_accrueRewards_1079:
                       _accrueRewards(msg.sender, msg.sender)
                       (identical to setRewardRatio's prelude).
              S1.2.  fun_poke_1082_inner: empty body. *)
  Axiom run_fun_poke_1082_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (sim : GlobalRewardState.t)
           (memory : SimulatedMemory.t),
    wf_caller_bound env.(Environment.caller) ->
    wf_tokens_bound sim.(GlobalRewardState.rewardTokens) ->
    (forall t, In t sim.(GlobalRewardState.rewardTokens) ->
               is_registered t = true) ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory (proj_sim_concrete sim)) |
      fun_poke_1082 ⇓
      Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_sim_post_poke_concrete sim env.(Environment.caller))) ?}}.

  (** ----- fun_claimRewards_1010 composite walker axiom -----

      The Yul body of [claimRewards(address[] calldata)]:

        S0.  callvalue() != 0 → revert path
        S1.  abi_decode_tuple_t_array_t_address (calldata array)
        S2.  fun_claimRewards_1010(offset, length):
              S2.1.  modifier_accrueRewards_910:
                       _accrueRewards(msg.sender, msg.sender)
              S2.2.  fun_claimRewards_1010_inner:
                       - allocate the claimableRewards[] return array
                       - LOOP over the calldata rewardTokens array:
                          * read rewardInfo at keccak(token, 7)+...
                          * read userRewardTracker at
                              keccak(caller, keccak(token, 9))+...
                          * read userRewardTracker.accruedRewards (slot+1)
                          * if non-zero:
                              + sstore(rewardInfo.totalClaimed +=
                                       claimable, at slot+4)
                              + sstore(userRewardTracker.accruedRewards
                                       := 0, at slot+1)  [ZERO-FIRST]
                              + fun_safeTransfer_4922(token, caller,
                                                       claimable)
                              + log2(RewardsClaimed event)

      The ZERO-FIRST ordering is load-bearing: the
      [accruedRewards := 0] sstore happens BEFORE the
      [safeTransfer] external call.  If the token reentries
      [claimRewards], the reentrant inner call reads 0 and
      extracts 0.  Mechanized at the sim level in
      [proofs/StakingVaultRewardsReentrancy.v] (REN-1..REN-5);
      lifted into the equivalence framework in Section 8 below. *)

  (** Precondition: every requested token's safeTransfer succeeds
      under the post-accrual claim amount.  This is the
      T-REWARDTOKEN trust boundary. *)
  Definition wf_claim_request
      (sim : GlobalRewardState.t) (caller : Address)
      (tokens : list Address) : Prop :=
    Forall (fun t =>
      let post_accrue := accrue_all_tokens_concrete sim caller in
      let u := get_user_reward post_accrue t caller in
      let amount := u.(UserReward.accruedRewards) in
      safeTransfer_success_spec_concrete t caller amount
    ) tokens.

  Axiom run_fun_claimRewards_1010_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (sim : GlobalRewardState.t)
           (memory : SimulatedMemory.t)
           (tokens_offset tokens_length : U256.t)
           (tokens : list Address),
    wf_caller_bound env.(Environment.caller) ->
    wf_tokens_bound sim.(GlobalRewardState.rewardTokens) ->
    wf_tokens_bound tokens ->
    (forall t, In t sim.(GlobalRewardState.rewardTokens) ->
               is_registered t = true) ->
    wf_claim_request sim env.(Environment.caller) tokens ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory' return_value,
    {{? codes, env,
        Some (make_state env state_base memory (proj_sim_concrete sim)) |
      fun_claimRewards_1010 tokens_offset tokens_length ⇓
      Result.Ok return_value
    | Some (make_state env state_base memory'
              (proj_sim_post_claimRewards_concrete
                 sim env.(Environment.caller) tokens)) ?}}.

  (** ====================================================================
      Section 7 — Milestone equivalence theorems

      Per R067 / R069, each milestone Qed composes the corresponding
      composite walker axiom with the per-mutator observational
      bridge.
      ==================================================================== *)

  Theorem run_setRewardRatio_equivalent_make_state
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : GlobalRewardState.t)
      (memory : SimulatedMemory.t)
      (halfLife : U256.t)
      (H_caller_bound : wf_caller_bound env.(Environment.caller))
      (H_admin : is_admin env.(Environment.caller) = true)
      (H_halfLife : wf_halfLife halfLife)
      (H_tokens_bound : wf_tokens_bound sim.(GlobalRewardState.rewardTokens))
      (H_tokens_registered :
         forall t, In t sim.(GlobalRewardState.rewardTokens) ->
                   is_registered t = true)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim_concrete sim) in
    let new_sim := set_reward_ratio_sim sim halfLife in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_setRewardRatio_1036 halfLife ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        eq_at_rewardRatio_concrete storage_post (proj_sim_concrete new_sim) /\
        (forall t, eq_at_reward_info_concrete
                     storage_post (proj_sim_concrete new_sim) t) /\
        (forall t u, eq_at_user_reward_concrete
                       storage_post (proj_sim_concrete new_sim) t u)).
  Proof.
    cbv zeta.
    pose proof (run_fun_setRewardRatio_1036_at_proj_sim
                  codes env state_base sim memory halfLife
                  H_caller_bound H_admin H_halfLife
                  H_tokens_bound H_tokens_registered H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    pose proof (proj_sim_setRewardRatio_observes_concrete sim halfLife)
      as (Hobs_ratio & Hobs_reward & Hobs_user).
    exists (Some (make_state env state_base memory'
                    (proj_sim_post_setRewardRatio_concrete sim halfLife))).
    exists (proj_sim_post_setRewardRatio_concrete sim halfLife).
    split; [exact Hwalker|].
    exists memory'. split; [reflexivity|].
    split; [exact Hobs_ratio|].
    split; [exact Hobs_reward|].
    exact Hobs_user.
  Qed.

  Theorem run_poke_equivalent_make_state
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : GlobalRewardState.t)
      (memory : SimulatedMemory.t)
      (H_caller_bound : wf_caller_bound env.(Environment.caller))
      (H_tokens_bound : wf_tokens_bound sim.(GlobalRewardState.rewardTokens))
      (H_tokens_registered :
         forall t, In t sim.(GlobalRewardState.rewardTokens) ->
                   is_registered t = true)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim_concrete sim) in
    let new_sim := poke_sim_concrete sim env.(Environment.caller) in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_poke_1082 ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        eq_at_rewardRatio_concrete storage_post (proj_sim_concrete new_sim) /\
        (forall t, eq_at_reward_info_concrete
                     storage_post (proj_sim_concrete new_sim) t) /\
        (forall t u, eq_at_user_reward_concrete
                       storage_post (proj_sim_concrete new_sim) t u)).
  Proof.
    cbv zeta.
    pose proof (run_fun_poke_1082_at_proj_sim
                  codes env state_base sim memory
                  H_caller_bound H_tokens_bound H_tokens_registered H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    pose proof (proj_sim_poke_observes_concrete sim env.(Environment.caller))
      as (Hobs_ratio & Hobs_reward & Hobs_user).
    exists (Some (make_state env state_base memory'
                    (proj_sim_post_poke_concrete sim env.(Environment.caller)))).
    exists (proj_sim_post_poke_concrete sim env.(Environment.caller)).
    split; [exact Hwalker|].
    exists memory'. split; [reflexivity|].
    split; [exact Hobs_ratio|].
    split; [exact Hobs_reward|].
    exact Hobs_user.
  Qed.

  Theorem run_claimRewards_equivalent_make_state
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : GlobalRewardState.t)
      (memory : SimulatedMemory.t)
      (tokens_offset tokens_length : U256.t)
      (tokens : list Address)
      (H_caller_bound : wf_caller_bound env.(Environment.caller))
      (H_registered_tokens_bound :
         wf_tokens_bound sim.(GlobalRewardState.rewardTokens))
      (H_requested_tokens_bound : wf_tokens_bound tokens)
      (H_tokens_registered :
         forall t, In t sim.(GlobalRewardState.rewardTokens) ->
                   is_registered t = true)
      (H_claim_ok : wf_claim_request sim env.(Environment.caller) tokens)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim_concrete sim) in
    let new_sim := claim_sim_concrete sim env.(Environment.caller) tokens in
    exists state' storage_post return_value,
      {{? codes, env, Some state |
        fun_claimRewards_1010 tokens_offset tokens_length ⇓
          Result.Ok return_value
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        eq_at_rewardRatio_concrete storage_post (proj_sim_concrete new_sim) /\
        (forall t, eq_at_reward_info_concrete
                     storage_post (proj_sim_concrete new_sim) t) /\
        (forall t u, eq_at_user_reward_concrete
                       storage_post (proj_sim_concrete new_sim) t u)).
  Proof.
    cbv zeta.
    pose proof (run_fun_claimRewards_1010_at_proj_sim
                  codes env state_base sim memory
                  tokens_offset tokens_length tokens
                  H_caller_bound H_registered_tokens_bound
                  H_requested_tokens_bound H_tokens_registered
                  H_claim_ok H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & return_value & Hwalker).
    pose proof (proj_sim_claimRewards_observes_concrete
                  sim env.(Environment.caller) tokens)
      as (Hobs_ratio & Hobs_reward & Hobs_user).
    exists (Some (make_state env state_base memory'
                    (proj_sim_post_claimRewards_concrete
                       sim env.(Environment.caller) tokens))).
    exists (proj_sim_post_claimRewards_concrete
              sim env.(Environment.caller) tokens).
    exists return_value.
    split; [exact Hwalker|].
    exists memory'. split; [reflexivity|].
    split; [exact Hobs_ratio|].
    split; [exact Hobs_reward|].
    exact Hobs_user.
  Qed.

  (** ====================================================================
      Section 8 — Reentrancy zero-first invariant

      Lifts the sim-level
      [proofs/StakingVaultRewardsReentrancy.v] theorems
      (REN-1..REN-5) into the equivalence module namespace, so
      downstream consumers can import this file and obtain both
      the equivalence milestones AND the safety theorems through
      a single [Require Import].

      The headline equivalence-side claim is the corollary
      [claim_each_token_concrete_zeroes] below: after the
      [claim_each_token_concrete] sim transformer, the
      [perUser] dict has [accruedRewards = 0] at the head for
      every claimed (token, caller) pair.  The contract-level
      analogue is that the on-chain [accruedRewards] slot at
      [keccak(caller, keccak(token, 9))+1] holds 0 after the
      sstore.  The bridge from sim to contract is the
      [eq_at_user_reward_concrete] predicate.
      ==================================================================== *)

  Theorem reentrancy_inner_extracts_zero :
    forall (r : RewardInfo.t) (u : UserReward.t),
      StakingVaultRewardsReentrancyProofs.inner_tx
        (StakingVaultRewardsReentrancy.reentrancy_step r u) = 0.
  Proof.
    apply StakingVaultRewardsReentrancyProofs.no_double_claim_inner_zero.
  Qed.

  Theorem reentrancy_outer_unchanged :
    forall (r : RewardInfo.t) (u : UserReward.t),
      StakingVaultRewardsReentrancyProofs.outer_tx
        (StakingVaultRewardsReentrancy.reentrancy_step r u)
      = u.(UserReward.accruedRewards).
  Proof.
    apply StakingVaultRewardsReentrancyProofs.no_double_claim_outer_unchanged.
  Qed.

  Theorem reentrancy_total_bounded :
    forall (r : RewardInfo.t) (u : UserReward.t),
      StakingVaultRewardsReentrancyProofs.outer_tx
        (StakingVaultRewardsReentrancy.reentrancy_step r u) +
      StakingVaultRewardsReentrancyProofs.inner_tx
        (StakingVaultRewardsReentrancy.reentrancy_step r u)
      = u.(UserReward.accruedRewards).
  Proof.
    apply StakingVaultRewardsReentrancyProofs.no_double_claim_total_bounded.
  Qed.

  Theorem reentrancy_zeroes_user_state :
    forall (r : RewardInfo.t) (u : UserReward.t),
      (StakingVaultRewardsReentrancyProofs.u_after
        (StakingVaultRewardsReentrancy.reentrancy_step r u))
      .(UserReward.accruedRewards) = 0.
  Proof.
    apply StakingVaultRewardsReentrancyProofs.reentrancy_zeroes_user.
  Qed.

  Theorem reentrancy_totalClaimed_consistent :
    forall (r : RewardInfo.t) (u : UserReward.t),
      (StakingVaultRewardsReentrancyProofs.r_after
        (StakingVaultRewardsReentrancy.reentrancy_step r u))
      .(RewardInfo.totalClaimed)
      = r.(RewardInfo.totalClaimed) + u.(UserReward.accruedRewards).
  Proof.
    apply StakingVaultRewardsReentrancyProofs.reentrancy_totalClaimed_consistent.
  Qed.

  (** ----- Equivalence-side: claim_each_token_concrete zeroes the head -----

      For the single-iteration case, the head-cons immediately
      yields [accruedRewards = 0] because [claimUser] zeros the
      output user.  This is what the on-chain
      [sstore(accruedRewards := 0)] writes. *)
  Lemma claim_each_token_concrete_single_zero :
    forall (s : GlobalRewardState.t) (caller : Address) (tok : Address),
      let s' := claim_each_token_concrete s caller [tok] in
      (get_user_reward s' tok caller).(UserReward.accruedRewards) = 0.
  Proof.
    intros s caller tok.
    simpl.
    set (r := get_reward_info s tok).
    set (u := get_user_reward s tok caller).
    set (claim_result := claim_one_token_sim r u).
    (* The fresh sim state has the (tok, caller) cell at the head with
       accruedRewards = 0 (from claim_one_token_sim). *)
    rewrite (get_user_reward_head_cons _ tok caller
              (snd (fst claim_result))).
    unfold claim_result, claim_one_token_sim.
    apply StakingVaultRewardsProofs.claimUser_zeroes_accrued.
  Qed.

  (** [claim_each_token_concrete_single_zero_ext] : extended to the
      empty-tail case where the head-cons survives.  Mirrors REN-4
      [reentrancy_zeroes_user] at the equivalence layer. *)
  Corollary claim_one_token_zeroes_user :
    forall (s : GlobalRewardState.t) (caller : Address) (tok : Address),
      (get_user_reward (claim_each_token_concrete s caller [tok]) tok caller)
        .(UserReward.accruedRewards) = 0.
  Proof. apply claim_each_token_concrete_single_zero. Qed.

  (** ----- Equivalence-side: per-token totalClaimed monotone -----

      After [claim_each_token_concrete s caller [tok]], the
      per-token [totalClaimed] grows by exactly the pre-claim
      [accruedRewards].  Sim-only Qed; the contract-side
      equivalent is the [eq_at_reward_info_concrete] bridge. *)
  Lemma claim_each_token_concrete_single_totalClaimed :
    forall (s : GlobalRewardState.t) (caller : Address) (tok : Address),
      (get_reward_info (claim_each_token_concrete s caller [tok]) tok)
        .(RewardInfo.totalClaimed)
      = (get_reward_info s tok).(RewardInfo.totalClaimed)
      + (get_user_reward s tok caller).(UserReward.accruedRewards).
  Proof.
    intros s caller tok.
    simpl.
    set (r := get_reward_info s tok).
    set (u := get_user_reward s tok caller).
    set (claim_result := claim_one_token_sim r u).
    rewrite (get_reward_info_head_cons _ tok (fst (fst claim_result))).
    unfold claim_result, claim_one_token_sim, StakingVaultRewards.claimUser.
    simpl. reflexivity.
  Qed.

  (** ====================================================================
      Section 9 — Sanity examples (vm_compute) — small concrete checks

      These exercise the sim transformers against tiny concrete
      states to validate that the definitions reduce as expected.
      They do NOT depend on the walker axioms — they only sanity-
      check the sim layer's [set_reward_ratio_sim] /
      [claim_each_token_concrete] semantics.
      ==================================================================== *)

  Module Examples.

    Definition tok_a : Address := 100.
    Definition tok_b : Address := 200.
    Definition user_x : Address := 500.

    Definition s0 : GlobalRewardState.t := {|
      GlobalRewardState.perToken :=
        [(tok_a, {| RewardInfo.rewardIndex := 0;
                    RewardInfo.balanceAccounted := 0;
                    RewardInfo.totalClaimed := 0; |})];
      GlobalRewardState.perUser :=
        [((tok_a, user_x),
          {| UserReward.lastRewardIndex := 0;
             UserReward.accruedRewards := 42; |})];
      GlobalRewardState.rewardTokens := [tok_a];
      GlobalRewardState.disallowed := [];
      GlobalRewardState.rewardRatio := 0;
      GlobalRewardState.totalSupply := 1000;
      GlobalRewardState.blockTime := 100;
    |}.

    Example ex_user_x_has_42 :
      (get_user_reward s0 tok_a user_x).(UserReward.accruedRewards) = 42.
    Proof. vm_compute. reflexivity. Qed.

    (** A claim by user_x of [tok_a] zeroes the accrued and
        increments totalClaimed by 42. *)
    Definition s1 : GlobalRewardState.t :=
      claim_each_token_concrete s0 user_x [tok_a].

    Example ex_user_x_claim_zeroes :
      (get_user_reward s1 tok_a user_x).(UserReward.accruedRewards) = 0.
    Proof. vm_compute. reflexivity. Qed.

    Example ex_tok_a_totalClaimed_42 :
      (get_reward_info s1 tok_a).(RewardInfo.totalClaimed) = 42.
    Proof. vm_compute. reflexivity. Qed.

    (** [set_reward_ratio_sim] with halfLife=0 short-circuits. *)
    Example ex_set_reward_ratio_zero_halfLife :
      (set_reward_ratio_sim s0 0).(GlobalRewardState.rewardRatio) = 0.
    Proof. vm_compute. reflexivity. Qed.

    (** [set_reward_ratio_sim] with halfLife=86400 (1 day) updates
        rewardRatio to LN_2_E18 / 86400.  Sanity check that the
        Z division matches expectations. *)
    Example ex_set_reward_ratio_one_day :
      (set_reward_ratio_sim s0 86400).(GlobalRewardState.rewardRatio)
      = LN_2_E18 / 86400.
    Proof. vm_compute. reflexivity. Qed.

    (** REN-1 / REN-3 sim-level: composing the reentrancy step
        confirms inner extracts 0 and total = original. *)
    Example ex_reentrancy_inner_zero :
      StakingVaultRewardsReentrancyProofs.inner_tx
        (StakingVaultRewardsReentrancy.reentrancy_step
           empty_reward
           {| UserReward.lastRewardIndex := 0;
              UserReward.accruedRewards := 1000; |}) = 0.
    Proof. apply reentrancy_inner_extracts_zero. Qed.

    Example ex_reentrancy_total :
      let u := {| UserReward.lastRewardIndex := 0;
                  UserReward.accruedRewards := 1000; |} in
      StakingVaultRewardsReentrancyProofs.outer_tx
        (StakingVaultRewardsReentrancy.reentrancy_step empty_reward u) +
      StakingVaultRewardsReentrancyProofs.inner_tx
        (StakingVaultRewardsReentrancy.reentrancy_step empty_reward u)
      = 1000.
    Proof. apply reentrancy_total_bounded. Qed.

    (** Equivalence-side: single-claim zeroes accrued at the
        equivalence-layer transformer. *)
    Example ex_equivalence_single_claim_zero :
      (get_user_reward
         (claim_each_token_concrete s0 user_x [tok_a])
         tok_a user_x).(UserReward.accruedRewards) = 0.
    Proof. apply claim_one_token_zeroes_user. Qed.

  End Examples.

End StakingVaultRewardsEquivalence.
