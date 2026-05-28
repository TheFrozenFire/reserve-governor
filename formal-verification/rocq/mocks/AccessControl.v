(** OpenZeppelin AccessControl / AccessControlEnumerable mock.

    Captures the surface of OZ's role-based access control that the
    Reserve Governor's Guardian / VersionRegistry / RewardTokenRegistry
    contracts inherit. Each contract currently models its own role
    sets locally (per-call Parameter predicates or boolean flags);
    this mock provides a shared, faithful representation.

    Production semantics (OZ v5 `AccessControl.sol`):

      - State: `mapping(bytes32 role => RoleData) _roles`, where
        `RoleData = { members : EnumerableSet<address>; adminRole :
        bytes32 }`. Roles whose adminRole isn't set explicitly
        default to DEFAULT_ADMIN_ROLE.

      - `grantRole(role, account)`: callable by holders of
        `getRoleAdmin(role)`. Idempotent on existing members.

      - `revokeRole(role, account)`: callable by holders of
        `getRoleAdmin(role)`. Idempotent on non-members.

      - `renounceRole(role, callerConfirmation)`: requires
        `callerConfirmation == msg.sender`; removes msg.sender from
        the role.

      - `_setRoleAdmin(role, adminRole)`: internal, sets the admin
        relation. Not all contracts use this; the default is
        DEFAULT_ADMIN_ROLE for every role.

    Modeling abstractions:

      - Roles are opaque `bytes32` hashes. We represent them as
        `U256.t` for compatibility with the existing simulation
        convention.

      - The `_roles` map is encoded as a [list (Role * RoleEntry)],
        with no-duplicate-keys discipline enforced by [Valid.t].

      - The per-role members set is a `list Address` with no-dup
        discipline, mirroring how the existing Guardian simulation
        already models its role sets locally.

      - The admin-of-admin chain is encoded directly in `RoleEntry.admin`.
        Roles not present in `_roles` are treated as having
        admin = `DEFAULT_ADMIN_ROLE`.

    What is NOT modeled:

      - The EnumerableSet enumerable-index methods
        (`getRoleMember(role, idx)`, `getRoleMemberCount(role)`).
        Set-membership semantics are sufficient for every audit-
        narrative claim that consumes this mock.

      - Per-role event emission. The Guardian and other domains
        emit role events but no proof currently depends on the
        emission semantics; events can be added if/when a
        downstream proof needs them.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Local Open Scope Z_scope.

Module AccessControl.

(** Opaque role identifier and address. *)
Definition Role : Set := U256.t.
Definition Address : Set := U256.t.

(** DEFAULT_ADMIN_ROLE is the keccak256 of the empty string, which
    OZ pins as 0x00...00. We model it as 0. *)
Definition DEFAULT_ADMIN_ROLE : Role := 0.

(** Per-role storage: holders list + admin role. *)
Record RoleEntry : Set := {
  members : list Address;
  admin   : Role;
}.

(** The `_roles` mapping, modeled as a list of (role, entry) pairs
    with the no-duplicate-keys invariant. *)
Record State : Set := {
  roles : list (Role * RoleEntry);
}.

Definition empty_state : State := {| roles := [] |}.

(** Result type matches the project convention. *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert  {_}.
End Result.

Definition revert_missing_role     {A : Set} : Result.t A := Result.Revert 0   32.
Definition revert_not_self_caller  {A : Set} : Result.t A := Result.Revert 32  32.

(** ===== Lookups ===== *)

(** Membership check helpers, mirroring the existing per-domain
    [addr_in] discipline. *)
Fixpoint addr_in (lst : list Address) (a : Address) : bool :=
  match lst with
  | []     => false
  | h :: t => if h =? a then true else addr_in t a
  end.

Fixpoint find_entry
    (rs : list (Role * RoleEntry)) (role : Role)
    : option RoleEntry :=
  match rs with
  | [] => None
  | (r, e) :: rest => if r =? role then Some e else find_entry rest role
  end.

Definition getRoleEntry (s : State) (role : Role) : RoleEntry :=
  match find_entry s.(roles) role with
  | Some e => e
  | None   => {| members := []; admin := DEFAULT_ADMIN_ROLE |}
  end.

Definition hasRole (s : State) (role : Role) (account : Address) : bool :=
  addr_in (getRoleEntry s role).(members) account.

Definition getRoleAdmin (s : State) (role : Role) : Role :=
  (getRoleEntry s role).(admin).

(** ===== Updates ===== *)

(** [add_member lst a]: insert if absent, mirroring OZ's
    [EnumerableSet.add]. *)
Definition add_member (lst : list Address) (a : Address) : list Address :=
  if addr_in lst a then lst else a :: lst.

(** [remove_member lst a]: remove the first occurrence (under
    NoDup, the only occurrence). *)
Fixpoint remove_member (lst : list Address) (a : Address) : list Address :=
  match lst with
  | []     => []
  | h :: t => if h =? a then remove_member t a else h :: remove_member t a
  end.

(** Update a role's entry in [roles], inserting a fresh one if the
    role is absent. *)
Fixpoint set_entry
    (rs : list (Role * RoleEntry)) (role : Role) (e : RoleEntry)
    : list (Role * RoleEntry) :=
  match rs with
  | [] => [(role, e)]
  | (r, ee) :: rest =>
      if r =? role
      then (r, e) :: rest
      else (r, ee) :: set_entry rest role e
  end.

(** ===== Authorization-gated operations =====

    OZ's [grantRole], [revokeRole], [renounceRole] all check
    `hasRole(getRoleAdmin(role), msg.sender)` (or `msg.sender ==
    callerConfirmation` for renounce). The mock takes [caller]
    explicitly. *)

Definition grantRole
    (s : State) (caller : Address) (role : Role) (account : Address)
    : Result.t State :=
  let adm := getRoleAdmin s role in
  if negb (hasRole s adm caller) then revert_missing_role
  else
    let e := getRoleEntry s role in
    let e' := {|
      members := add_member e.(members) account;
      admin   := e.(admin);
    |} in
    Result.Success {| roles := set_entry s.(roles) role e' |}.

Definition revokeRole
    (s : State) (caller : Address) (role : Role) (account : Address)
    : Result.t State :=
  let adm := getRoleAdmin s role in
  if negb (hasRole s adm caller) then revert_missing_role
  else
    let e := getRoleEntry s role in
    let e' := {|
      members := remove_member e.(members) account;
      admin   := e.(admin);
    |} in
    Result.Success {| roles := set_entry s.(roles) role e' |}.

(** OZ's [renounceRole(role, callerConfirmation)] requires
    [callerConfirmation == msg.sender]. The mock takes both
    explicitly. *)
Definition renounceRole
    (s : State) (caller : Address) (role : Role) (callerConfirmation : Address)
    : Result.t State :=
  if negb (caller =? callerConfirmation) then revert_not_self_caller
  else
    let e := getRoleEntry s role in
    let e' := {|
      members := remove_member e.(members) caller;
      admin   := e.(admin);
    |} in
    Result.Success {| roles := set_entry s.(roles) role e' |}.

(** Internal setter for the admin chain. Mirrors OZ's
    [_setRoleAdmin], which is `internal` and not callable
    externally. We expose it for simulation use only. *)
Definition setRoleAdmin
    (s : State) (role : Role) (adminRole : Role) : State :=
  let e := getRoleEntry s role in
  let e' := {|
    members := e.(members);
    admin   := adminRole;
  |} in
  {| roles := set_entry s.(roles) role e' |}.

(** ===== Validity invariant =====

    Storage discipline:
      - No duplicate role keys in [roles].
      - Every role's members list is duplicate-free.
      - The zero address is not a holder of any role.
*)
Module Valid.
  Definition no_dup_roles (s : State) : Prop :=
    NoDup (map fst s.(roles)).

  Definition no_dup_members (s : State) : Prop :=
    Forall (fun e => NoDup (snd e).(members)) s.(roles).

  Definition no_zero_members (s : State) : Prop :=
    Forall (fun e => Forall (fun a => a <> 0) (snd e).(members)) s.(roles).

  Record state (s : State) : Prop := {
    roles_nd     : no_dup_roles s;
    members_nd   : no_dup_members s;
    members_nz   : no_zero_members s;
  }.

  Lemma empty_valid : state empty_state.
  Proof.
    constructor; unfold no_dup_roles, no_dup_members, no_zero_members; simpl;
      [apply NoDup_nil | apply Forall_nil | apply Forall_nil].
  Qed.
End Valid.

(** ===== Headline lemmas =====

    Just enough to prove the mock is well-formed; the per-domain
    integration proofs cite specific operations as needed. *)

Lemma add_member_idempotent :
  forall lst a, addr_in lst a = true -> add_member lst a = lst.
Proof. intros lst a Hin. unfold add_member. rewrite Hin. reflexivity. Qed.

Lemma add_member_inserts :
  forall lst a, addr_in lst a = false -> addr_in (add_member lst a) a = true.
Proof.
  intros lst a Hin. unfold add_member. rewrite Hin.
  simpl. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma remove_member_idempotent_on_absent :
  forall lst a, addr_in lst a = false -> remove_member lst a = lst.
Proof.
  intros lst a Hin.
  induction lst as [|h t IH]; simpl; [reflexivity|].
  destruct (h =? a) eqn:Hha.
  - simpl in Hin. rewrite Hha in Hin. discriminate.
  - simpl in Hin. rewrite Hha in Hin. rewrite (IH Hin). reflexivity.
Qed.

(** After [setRoleAdmin role newAdmin], a query of
    [getRoleAdmin role] returns [newAdmin]. *)
Lemma setRoleAdmin_updates_admin :
  forall (s : State) (role newAdmin : Role),
    getRoleAdmin (setRoleAdmin s role newAdmin) role = newAdmin.
Proof.
  intros s role newAdmin.
  unfold getRoleAdmin, getRoleEntry, setRoleAdmin.
  cbn -[Z.eqb find_entry set_entry].
  (* find_entry on (set_entry (roles s) role e') role = Some e' *)
  assert (Hfind :
    find_entry (set_entry s.(roles) role
                {| members := (getRoleEntry s role).(members);
                   admin   := newAdmin |}) role
    = Some {| members := (getRoleEntry s role).(members);
              admin   := newAdmin |}).
  { induction s.(roles) as [|hd rest IH].
    - cbn -[Z.eqb]. rewrite Z.eqb_refl. reflexivity.
    - destruct hd as [r e]. cbn -[Z.eqb].
      destruct (r =? role) eqn:Hr.
      + cbn -[Z.eqb]. rewrite Hr. reflexivity.
      + cbn -[Z.eqb]. rewrite Hr. exact IH. }
  rewrite Hfind. reflexivity.
Qed.

End AccessControl.
