(** ProposalLib simulation.

    Mirrors contracts/governance/lib/ProposalLib.sol — the library that
    mediates proposal lifecycle for the ReserveOptimisticGovernor.

    The library exposes three external entry points:

      proposeOptimistic(proposal, core, optimisticParams)
        Validates a fresh optimistic proposal: the proposer must hold
        OPTIMISTIC_PROPOSER_ROLE on the timelock, and every
        (target, selector) tuple in the proposal must be allowed by the
        OptimisticSelectorRegistry. Empty calldata, EOA targets, and
        descriptions carrying the [Confirmation For: ] prefix all
        revert.

      proposePessimistic(proposal, core)
        Validates a fresh standard proposal: the proposer's voting
        weight must be >= the configured proposalThreshold. Targets
        must be contracts (code.length != 0) OR the calldata must be
        empty.

      transitionToPessimistic(proposalId, optDetails, cores)
        One-way re-route: takes an optimistic proposal whose veto
        threshold has not yet been bumped to the sentinel, sets it to
        the sentinel, derives a fresh proposalId from the description
        with [Confirmation For: ] prefixed, and saves the new entry as
        a standard proposal.

    All three call [_saveProposal] internally, which writes
    [proposalCore.{proposer, voteStart, voteDuration}] and emits
    [ProposalCreated].

    Modeling abstractions:

    * Hashing is left opaque. The contract derives proposalId via
      [getProposalId(targets, values, calldatas, keccak256(description))]
      where the latter is [keccak256(abi.encode(...))] over the four
      fields. We model this as an injective function
      [proposalId : ProposalKey -> U256.t] where [ProposalKey] is the
      4-tuple itself. The simulation never computes a keccak digest;
      it merely asserts pid equality reduces to key equality.

    * Per-account vote weight is a black box. We expose a [getVotes]
      parameter to [proposePessimistic] rather than reproducing the
      governor's checkpoint state.

    * The "EOA guard" (target.code.length != 0) is modeled as a
      [is_contract : Address -> bool] parameter; the simulation
      threads it through without inspecting on-chain code.

    * The [_isValidDescriptionForProposer] suffix check inspects the
      last 52 bytes of the description for a [#proposer=<addr>] marker
      and parses the hex address. We model this with an opaque
      [description_proposer : string -> option Address] that returns
      the parsed address if a suffix is present and [None] otherwise.
      The contract accepts if either no suffix is present or the
      parsed address matches the proposer.

    * Storage mutation in [_saveProposal] is modeled as an explicit
      record update on a [ProposalCore.t] value, not as an in-place
      Solidity write. The same applies to
      [optimisticProposalDetails[proposalId]] in
      [transitionToPessimistic] — modeled as an explicit functional
      update returning the new mapping image.

    Revert coverage:
      - [revert_zero_length]            empty targets array
      - [revert_length_mismatch]        targets / values / calldatas
                                        length mismatch
      - [revert_confirmation_prefix]    user-facing entry sees the
                                        confirmation prefix on the
                                        description
      - [revert_restricted_proposer]    description carries a
                                        [#proposer=] suffix for an
                                        address != msg.sender
      - [revert_already_proposed]       proposalCore.voteStart != 0
      - [revert_not_optimistic_proposer] proposer lacks the role
      - [revert_invalid_call]            (target, selector) not allowed
                                        or calldata.length < 4
      - [revert_insufficient_votes]     proposer.votes < threshold
      - [revert_already_transitioned]   optDetails.vetoThreshold ==
                                        TRANSITIONED_VETO_THRESHOLD
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.Lists.List.
Import ListNotations.

Module ProposalLib.

(** ----- Domain ----- *)

Definition Address  : Set := U256.t.
Definition Selector : Set := U256.t.   (** bytes4 modeled as small U256.t *)
Definition Calldata : Set := list U256.t.  (** byte stream; first cell = selector *)

Definition zero_address : Address := 0.

(** Sentinel used by the transition gate. The contract hard-codes
    [type(uint256).max]. We mirror with a Z constant; the value itself
    is opaque in proofs but well-defined for vm_compute. *)
Definition TRANSITIONED_VETO_THRESHOLD : U256.t := 2 ^ 256 - 1.

(** ----- Description model ----- *)

(** The contract operates on UTF-8 byte strings. The two semantic
    queries are:
      1) Does the description begin with [Confirmation For: ]?
      2) Is there a [#proposer=<addr>] suffix, and if so, what address
         does it encode?

    We model the description as an arbitrary parameter [Desc] with
    those two queries as black-box functions. The properties we prove
    are universally quantified over the description and parameterized
    only by what those two queries return. *)
Parameter Desc : Set.

Parameter has_confirmation_prefix : Desc -> bool.
Parameter description_proposer    : Desc -> option Address.
Parameter prefix_with_confirmation : Desc -> Desc.

(** Description-level axioms. These mirror the contract behavior:
      - prefixing forces the prefix-check to return true
      - the prefixed description's [#proposer=] suffix (if any)
        carries through unchanged — the prefix is at the front, the
        suffix is at the back
      - distinct descriptions produce distinct prefixed forms
        (injectivity of the prefix transformation) *)
Axiom prefix_sets_prefix :
  forall d, has_confirmation_prefix (prefix_with_confirmation d) = true.

Axiom prefix_injective :
  forall d1 d2,
    prefix_with_confirmation d1 = prefix_with_confirmation d2 -> d1 = d2.

(** ----- Proposal payload ----- *)

Module ProposalData.
  Record t : Set := {
    proposalId : U256.t;
    proposer   : Address;
    targets    : list Address;
    values     : list U256.t;
    calldatas  : list Calldata;
    description : Desc;
  }.
End ProposalData.

(** ----- ProposalCore storage slot ----- *)

(** Mirror of [GovernorUpgradeable.ProposalCore] — what
    [_saveProposal] writes. *)
Module ProposalCore.
  Record t : Set := {
    proposer     : Address;
    voteStart    : U256.t;    (** uint48 *)
    voteDuration : U256.t;    (** uint32 *)
  }.
End ProposalCore.

Definition empty_core : ProposalCore.t := {|
  ProposalCore.proposer := zero_address;
  ProposalCore.voteStart := 0;
  ProposalCore.voteDuration := 0;
|}.

(** ----- Optimistic-side storage slot ----- *)

Module OptimisticProposalDetails.
  Record t : Set := {
    targets       : list Address;
    values        : list U256.t;
    calldatas     : list Calldata;
    description   : Desc;
    vetoThreshold : U256.t;   (** D18{1} — sentinel = TRANSITIONED *)
  }.
End OptimisticProposalDetails.

Module OptimisticGovernanceParams.
  Record t : Set := {
    vetoDelay     : U256.t;
    vetoPeriod    : U256.t;
    vetoThreshold : U256.t;
  }.
End OptimisticGovernanceParams.

(** ----- Result type ----- *)

Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

Definition revert_zero_length            {A : Set} : Result.t A := Result.Revert  0 32.
Definition revert_length_mismatch        {A : Set} : Result.t A := Result.Revert 32 32.
Definition revert_confirmation_prefix    {A : Set} : Result.t A := Result.Revert 64 32.
Definition revert_restricted_proposer    {A : Set} : Result.t A := Result.Revert 96 32.
Definition revert_already_proposed       {A : Set} : Result.t A := Result.Revert 128 32.
Definition revert_not_optimistic_proposer {A : Set} : Result.t A := Result.Revert 160 32.
Definition revert_invalid_call           {A : Set} : Result.t A := Result.Revert 192 32.
Definition revert_insufficient_votes     {A : Set} : Result.t A := Result.Revert 224 32.
Definition revert_already_transitioned   {A : Set} : Result.t A := Result.Revert 256 32.

(** ----- Helpers ----- *)

Fixpoint length_eq {A B : Set} (xs : list A) (ys : list B) : bool :=
  match xs, ys with
  | [], [] => true
  | _ :: xs', _ :: ys' => length_eq xs' ys'
  | _, _ => false
  end.

(** The selector of a calldata is its first cell. The contract derives
    [bytes4(calldata)] which is the four leading bytes; an empty
    calldata has no selector and fails the [calldatas[i].length >= 4]
    guard. We model that via [None] for the empty case. *)
Definition selector_of (cd : Calldata) : option Selector :=
  match cd with
  | [] => None
  | s :: _ => Some s
  end.

(** ----- _isValidDescriptionForProposer model -----

    The contract returns true if either no suffix is present or the
    parsed address equals the proposer. We mirror with: *)
Definition isValidDescriptionForProposer
    (proposer : Address) (d : Desc) : bool :=
  match description_proposer d with
  | None => true
  | Some a => a =? proposer
  end.

(** ----- _validateProposal -----

    The four guards, in source order:
      - [voteStart != 0]    -> already-proposed
      - description-proposer suffix mismatch
      - description begins with [Confirmation For: ]
      - lengths inconsistent or zero
*)
Definition validateProposal
    (p : ProposalData.t) (core : ProposalCore.t)
    : Result.t unit :=
  if negb (core.(ProposalCore.voteStart) =? 0) then
    revert_already_proposed
  else if negb (isValidDescriptionForProposer
                  p.(ProposalData.proposer) p.(ProposalData.description)) then
    revert_restricted_proposer
  else if has_confirmation_prefix p.(ProposalData.description) then
    revert_confirmation_prefix
  else if negb (length_eq p.(ProposalData.targets) p.(ProposalData.values)) then
    revert_length_mismatch
  else if negb (length_eq p.(ProposalData.targets) p.(ProposalData.calldatas)) then
    revert_length_mismatch
  else
    match p.(ProposalData.targets) with
    | [] => revert_zero_length
    | _  => Result.Success tt
    end.

(** ----- _saveProposal -----

    Writes the three core fields and is otherwise an event-only
    no-op. Returns the new core record. *)
Definition saveProposal
    (p : ProposalData.t) (voteDelay voteDuration now : U256.t)
    : ProposalCore.t :=
  {|
    ProposalCore.proposer     := p.(ProposalData.proposer);
    ProposalCore.voteStart    := now + voteDelay;
    ProposalCore.voteDuration := voteDuration;
  |}.

(** ----- Selector registry parameter -----

    The library calls [selectorRegistry.isAllowed(target, selector)];
    we abstract that as a black-box predicate. *)
Definition SelectorRegistry : Set := Address -> Selector -> bool.

(** Same idea for "is the proposer in OPTIMISTIC_PROPOSER_ROLE?" *)
Definition RoleSet : Set := Address -> bool.

(** ----- per-target selector / call check -----

    For each i:
      - calldatas[i].length >= 4   (modeled as selector_of = Some _)
      - selectorRegistry.isAllowed(target_i, selector_i) *)
Fixpoint validate_optimistic_calls
    (reg : SelectorRegistry)
    (is_contract : Address -> bool)
    (targets : list Address) (calldatas : list Calldata) : bool :=
  match targets, calldatas with
  | [], [] => true
  | t :: ts, c :: cs =>
      match selector_of c with
      | None => false
      | Some sel =>
          andb (is_contract t)
               (andb (reg t sel)
                     (validate_optimistic_calls reg is_contract ts cs))
      end
  | _, _ => false   (** length mismatch already caught by validateProposal *)
  end.

(** The standard track's per-call gate is laxer: target must be a
    contract OR calldata is empty. *)
Fixpoint validate_pessimistic_calls
    (is_contract : Address -> bool)
    (targets : list Address) (calldatas : list Calldata) : bool :=
  match targets, calldatas with
  | [], [] => true
  | t :: ts, c :: cs =>
      andb (orb (is_contract t)
                (match c with [] => true | _ => false end))
           (validate_pessimistic_calls is_contract ts cs)
  | _, _ => false
  end.

(** ----- proposeOptimistic ----- *)

Definition proposeOptimistic
    (p : ProposalData.t) (core : ProposalCore.t)
    (params : OptimisticGovernanceParams.t)
    (roles : RoleSet)
    (reg : SelectorRegistry)
    (is_contract : Address -> bool)
    (now : U256.t)
    : Result.t ProposalCore.t :=
  match validateProposal p core with
  | Result.Revert pp ss => Result.Revert pp ss
  | Result.Success _ =>
      if negb (roles p.(ProposalData.proposer)) then
        revert_not_optimistic_proposer
      else if negb (validate_optimistic_calls
                      reg is_contract
                      p.(ProposalData.targets)
                      p.(ProposalData.calldatas)) then
        revert_invalid_call
      else
        Result.Success
          (saveProposal p
             params.(OptimisticGovernanceParams.vetoDelay)
             params.(OptimisticGovernanceParams.vetoPeriod)
             now)
  end.

(** ----- proposePessimistic ----- *)

Module StandardGovernanceParams.
  Record t : Set := {
    votingDelay     : U256.t;
    votingPeriod    : U256.t;
    proposalThreshold : U256.t;
  }.
End StandardGovernanceParams.

Definition proposePessimistic
    (p : ProposalData.t) (core : ProposalCore.t)
    (params : StandardGovernanceParams.t)
    (votes : Address -> U256.t)
    (is_contract : Address -> bool)
    (now : U256.t)
    : Result.t ProposalCore.t :=
  match validateProposal p core with
  | Result.Revert pp ss => Result.Revert pp ss
  | Result.Success _ =>
      if votes p.(ProposalData.proposer)
           <? params.(StandardGovernanceParams.proposalThreshold) then
        revert_insufficient_votes
      else if negb (validate_pessimistic_calls
                      is_contract
                      p.(ProposalData.targets)
                      p.(ProposalData.calldatas)) then
        revert_invalid_call
      else
        Result.Success
          (saveProposal p
             params.(StandardGovernanceParams.votingDelay)
             params.(StandardGovernanceParams.votingPeriod)
             now)
  end.

(** ----- Opaque proposalId model -----

    The contract computes
      proposalId = uint256(keccak256(abi.encode(targets, values, calldatas, descHash)))
    where descHash = keccak256(bytes(description)).

    Under the standard keccak-as-random-oracle assumption, [proposalId]
    is an injective function of [(targets, values, calldatas, description)].
    We model it as a parameter and assert determinism + injectivity. *)
Definition ProposalKey : Set :=
  list Address * list U256.t * list Calldata * Desc.

Parameter proposalIdOf : ProposalKey -> U256.t.

Axiom proposalIdOf_injective :
  forall k1 k2, proposalIdOf k1 = proposalIdOf k2 -> k1 = k2.

Definition proposalIdOfDetails (d : OptimisticProposalDetails.t) : U256.t :=
  proposalIdOf (d.(OptimisticProposalDetails.targets),
                d.(OptimisticProposalDetails.values),
                d.(OptimisticProposalDetails.calldatas),
                d.(OptimisticProposalDetails.description)).

(** ----- transitionToPessimistic -----

    Computes a new proposalId from the prefixed description, marks the
    optimistic slot as transitioned (vetoThreshold := sentinel), and
    saves the new core entry. Returns the triple [(newCore, newDetails,
    newProposalId)] or a revert.

    The output mirrors what the on-chain code does: it bumps the
    sentinel, derives the new id, and writes a fresh ProposalCore for
    that id. The caller is the governor; we capture the visible
    state-delta here. *)
Definition transitionToPessimistic
    (d : OptimisticProposalDetails.t)
    (params : StandardGovernanceParams.t)
    (now : U256.t)
    (proposer_of_optimistic : Address)
    : Result.t (U256.t * OptimisticProposalDetails.t * ProposalCore.t) :=
  if d.(OptimisticProposalDetails.vetoThreshold) =? TRANSITIONED_VETO_THRESHOLD
  then revert_already_transitioned
  else
    let newDesc := prefix_with_confirmation
                     d.(OptimisticProposalDetails.description) in
    let newPid := proposalIdOf
                    (d.(OptimisticProposalDetails.targets),
                     d.(OptimisticProposalDetails.values),
                     d.(OptimisticProposalDetails.calldatas),
                     newDesc) in
    let newDetails := {|
      OptimisticProposalDetails.targets       := d.(OptimisticProposalDetails.targets);
      OptimisticProposalDetails.values        := d.(OptimisticProposalDetails.values);
      OptimisticProposalDetails.calldatas     := d.(OptimisticProposalDetails.calldatas);
      OptimisticProposalDetails.description   := d.(OptimisticProposalDetails.description);
      OptimisticProposalDetails.vetoThreshold := TRANSITIONED_VETO_THRESHOLD;
    |} in
    let newProposal : ProposalData.t := {|
      ProposalData.proposalId  := newPid;
      ProposalData.proposer    := proposer_of_optimistic;
      ProposalData.targets     := d.(OptimisticProposalDetails.targets);
      ProposalData.values      := d.(OptimisticProposalDetails.values);
      ProposalData.calldatas   := d.(OptimisticProposalDetails.calldatas);
      ProposalData.description := newDesc;
    |} in
    let newCore := saveProposal newProposal
                                params.(StandardGovernanceParams.votingDelay)
                                params.(StandardGovernanceParams.votingPeriod)
                                now in
    Result.Success (newPid, newDetails, newCore).

(** ----- Validity predicates ----- *)
Module Valid.

  (** Well-formedness of a [ProposalData]: lengths agree, non-empty,
      no [Confirmation For:] prefix, valid suffix-vs-proposer. *)
  Record well_formed_proposal (p : ProposalData.t) : Prop := {
    wf_lengths_tv :
      length p.(ProposalData.targets) = length p.(ProposalData.values);
    wf_lengths_tc :
      length p.(ProposalData.targets) = length p.(ProposalData.calldatas);
    wf_nonempty :
      p.(ProposalData.targets) <> [];
    wf_no_prefix :
      has_confirmation_prefix p.(ProposalData.description) = false;
    wf_suffix_ok :
      isValidDescriptionForProposer p.(ProposalData.proposer)
                                    p.(ProposalData.description) = true;
  }.

  (** A fresh slot (where the proposal can be saved). *)
  Definition fresh_core (c : ProposalCore.t) : Prop :=
    c.(ProposalCore.voteStart) = 0.

  (** A transitioned optimistic-details slot. *)
  Definition transitioned (d : OptimisticProposalDetails.t) : Prop :=
    d.(OptimisticProposalDetails.vetoThreshold) = TRANSITIONED_VETO_THRESHOLD.

End Valid.

End ProposalLib.
