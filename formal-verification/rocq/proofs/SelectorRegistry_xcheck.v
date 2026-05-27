(** OptimisticSelectorRegistry simulation × CAS witness cross-check.

    Evaluates the [SelectorRegistry] simulation on the same scenarios
    used by [cas/selector_registry/membership_consistency.gp] and
    asserts identical outcomes.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.SelectorRegistry.
Require Import Coq.Lists.List.
Import ListNotations.

Module SelectorRegistryXCheck.

Import SelectorRegistry.

(** Calibration mirrors the CAS script. *)
Definition self_addr     : Address := 1.
Definition gov_addr      : Address := 2.
Definition timelock_addr : Address := 3.
Definition token_addr    : Address := 4.
Definition forbidden     : list Address := [self_addr; gov_addr; timelock_addr; token_addr].

(** ----- INV-1: add idempotence. ----- *)
Definition inv1_after_first : State.t :=
  match addSelector empty_state forbidden 10 1000 with
  | Result.Success s => s
  | _ => empty_state
  end.

Lemma xcheck_first_add_state :
  inv1_after_first.(State.targets) = [10]
  /\ allowed_for inv1_after_first.(State.allowedSelectors) 10 = [1000].
Proof. vm_compute. split; reflexivity. Qed.

Lemma xcheck_duplicate_add_noop :
  addSelector inv1_after_first forbidden 10 1000 = Result.Success inv1_after_first.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-2: cross-invariant across a mixed sequence.
    Reproduces the CAS event log:
      add(10, 1000); add(10, 1001); add(20, 2000);
      remove(10, 1000); remove(10, 1001);   -- wipes target 10
      add(30, 3000).
    Final targets list (in some order) should be {20, 30}. ----- *)
Definition inv2_final : State.t :=
  match addSelector empty_state forbidden 10 1000 with
  | Result.Success s1 =>
    match addSelector s1 forbidden 10 1001 with
    | Result.Success s2 =>
      match addSelector s2 forbidden 20 2000 with
      | Result.Success s3 =>
        match removeSelector s3 10 1000 with
        | Result.Success s4 =>
          match removeSelector s4 10 1001 with
          | Result.Success s5 =>
            match addSelector s5 forbidden 30 3000 with
            | Result.Success s6 => s6
            | _ => empty_state
            end
          | _ => empty_state
          end
        | _ => empty_state
        end
      | _ => empty_state
      end
    | _ => empty_state
    end
  | _ => empty_state
  end.

Lemma xcheck_inv2_target_10_gone :
  list_contains inv2_final.(State.targets) 10 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv2_target_20_present :
  list_contains inv2_final.(State.targets) 20 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv2_target_30_present :
  list_contains inv2_final.(State.targets) 30 = true.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-4: add then remove restores the prior set. ----- *)
Definition inv4_s0 : State.t :=
  match addSelector empty_state forbidden 10 1000 with
  | Result.Success s => s
  | _ => empty_state
  end.

Definition inv4_s1 : State.t :=
  match addSelector inv4_s0 forbidden 20 2000 with
  | Result.Success s => s
  | _ => empty_state
  end.

Definition inv4_s2 : State.t :=
  match removeSelector inv4_s1 20 2000 with
  | Result.Success s => s
  | _ => empty_state
  end.

Lemma xcheck_add_then_remove_restores :
  inv4_s2 = inv4_s0.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-6: revert paths. ----- *)
Lemma xcheck_add_forbidden_reverts :
  addSelector empty_state forbidden gov_addr 1000 = revert_invalid_target.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_add_zero_selector_reverts :
  addSelector empty_state forbidden 10 0 = revert_invalid_selector.
Proof. vm_compute. reflexivity. Qed.

End SelectorRegistryXCheck.
