(** OpenZeppelin ERC4626 mock — tokenized vault standard (EIP-4626).

    Mirrors the surface of
      @openzeppelin/contracts/token/ERC20/extensions/ERC4626.sol
      (OZ v5.4.0).

    ERC4626 is an *abstract* contract that extends [ERC20]: the
    "shares" are an ERC20 token of which the vault contract is the
    issuer, and the "assets" are an external ERC20 token referenced
    by the immutable [_asset] address.  Four conversion functions
    bridge the two tokens, mediated by a [_decimalsOffset()] virtual
    that defends against the first-depositor inflation attack.

    OZ semantics (v5.4.0 — paraphrased):

      abstract contract ERC4626 is ERC20, IERC4626 {
        IERC20 private immutable _asset;
        uint8  private immutable _underlyingDecimals;

        function asset()        public view returns (address);
        function totalAssets()  public view returns (uint256) {
          return IERC20(asset()).balanceOf(address(this));
        }
        function _convertToShares(uint256 assets, Math.Rounding r)
            internal view virtual returns (uint256) {
          return assets.mulDiv(
            totalSupply() + 10 ** _decimalsOffset(),
            totalAssets() + 1,
            r);
        }
        function _convertToAssets(uint256 shares, Math.Rounding r)
            internal view virtual returns (uint256) {
          return shares.mulDiv(
            totalAssets() + 1,
            totalSupply() + 10 ** _decimalsOffset(),
            r);
        }
        function _deposit(...)  { transferFrom(caller -> vault); _mint(receiver, shares); }
        function _withdraw(...) { _spendAllowance(if caller != owner); _burn(owner, shares); transfer(vault -> receiver); }
        function _decimalsOffset() internal view virtual returns (uint8) { return 0; }
      }

    [_decimalsOffset] is the **inflation-attack defense**: virtual
    shares = [10^offset], virtual assets = 1.  The first-depositor
    attack inflates the share price by donating assets directly to
    the vault before the first user deposits; the defense caps the
    inflation by ensuring that the attacker's donation is matched by
    [10^offset] virtual shares the attacker did not mint.  See the
    @dev block at the top of ERC4626.sol for the rigorous analysis.

    Rounding directions (OZ Math.Rounding enum):
      - Floor : round toward -infinity (favors vault)
      - Ceil  : round toward +infinity (favors vault, against user)
      - Trunc : round toward 0 (= Floor for non-negative)
      - Expand: round away from 0 (= Ceil for non-negative)

    The four public conversions select their rounding to **always
    favor the vault** — i.e., shares are floor on deposit/convert,
    ceil on withdraw; assets are floor on redeem/convert, ceil on
    mint.  This is the "user pays the rounding tax" rule and is
    how OZ keeps the vault solvent across many deposit / withdraw
    cycles.  The pairings are:
      - previewDeposit  -> _convertToShares (Floor)
      - previewMint     -> _convertToAssets (Ceil)
      - previewWithdraw -> _convertToShares (Ceil)
      - previewRedeem   -> _convertToAssets (Floor)

    Modeling choices:

      - The **asset address** [_asset] is modeled as an opaque
        [Address] field in the state.  We do NOT compose the external
        ERC20's storage into the vault sim; instead, [totalAssets]
        is carried as a [U256.t] state field — a *snapshot* of the
        external asset balance at the vault's address.  This mirrors
        the approach taken in mocks/Votes.v with [voting_units]:
        carry the virtual-view's value as state, defer the binding
        to the external token to the equivalence/integration layer.
        See `proofs/equivalence/ERC4626.v` for the staticcall bridge
        (R063) that closes the gap when an inheritor concretely
        composes against a deployed ERC20.

      - The **shares ERC20** is composed by inclusion: the vault's
        own state carries a full [ERC20.State] for the shares token.
        [totalSupply] is read from this nested record.  Mint and burn
        on the shares side are direct calls to [ERC20.mint] / [ERC20.burn].

      - The **decimals offset** is a state field rather than a virtual
        because the offset is fixed at construction (OZ:
        [_underlyingDecimals + _decimalsOffset()] is the public
        decimals).  Inheritors fix the offset at deploy time; we
        model it as a constant carried in state.

      - **mulDiv with rounding**: OZ's [Math.mulDiv] is exact 512-bit
        arithmetic with a final rounding bump.  Since we model values
        in unbounded [Z], the formula simplifies to ordinary
        Euclidean division with a +1 bump when rounding up and the
        remainder is non-zero.  Concrete formula:
          floor(x*y/d)  = (x*y) / d                      [Z.div]
          ceil(x*y/d)   = (x*y + d - 1) / d              [non-zero numer]
          round-trunc   = floor for non-neg inputs
          round-expand  = ceil  for non-neg inputs

      - **Reverts**: deposit / withdraw / mint / redeem revert when
        the caller exceeds the per-receiver max.  The base contract
        defaults [maxDeposit] / [maxMint] to [type(uint256).max], and
        [maxWithdraw] / [maxRedeem] to the user's balance-derived
        cap.  We model the max-checks via a result-monad revert
        sentinel (mirroring Votes.v's [revert_future_lookup] pattern).

      - **Reentrancy**: OZ ERC4626 deliberately does NOT add a
        nonReentrant guard at the base level (the OZ docs argue
        that the canonical asset transfer ordering — transfer-before-mint
        on deposit, burn-before-transfer on withdraw — is reentrancy-safe
        absent ERC-777 callbacks).  The mock matches: no reentrancy
        state, no guard.  Inheritors layering reentrancy guards on
        top compose them at the call site.

      - **Allowance spend on withdraw**: when [caller != owner],
        [_withdraw] decrements the [owner -> caller] allowance by
        [shares].  We use [ERC20.transferFrom_tracked]-style
        allowance accounting on the shares ERC20.

    What is NOT modeled:

      - The asset's ERC20 ledger.  We carry [totalAssets] as a state
        field and update it monotonically on deposit (+= assets) and
        withdraw (-= assets).  An inheritor that wants to bind to a
        deployed ERC20's storage composes the StaticCallBridge
        (R063) at the equivalence-proof layer.
      - The asset-side [decimals()] staticcall.  The mock carries
        [underlying_decimals] as a [U256.t] field; the inheritor
        supplies a concrete value at deploy time, and the equivalence
        bridges the staticcall.
      - ERC-777 callback hooks on the asset.  OZ comments warn about
        them; the mock assumes a vanilla ERC20.
      - The exact ABI-revert selectors (we use opaque [Result.Revert]
        sentinels — same convention as Votes.v / Nonces.v).

    Used by:
      - This file's companion [proofs/equivalence/ERC4626.v].
      - Future StakingVault equivalence (#256) — StakingVault
        inherits ERC4626 + ERC20Votes; the ERC4626 sim provides the
        share-asset conversion reasoning.
      - Any future tokenized-vault binding that re-uses the OZ
        ERC4626 abstract base.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.mocks.ERC20.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Local Open Scope Z_scope.

Module ERC4626.

(** Address model — same opaque [U256.t] convention as ERC20.v. *)
Definition Address : Set := U256.t.
Definition zero_address : Address := 0.

(** ----- Rounding modes (port of OZ Math.Rounding) -----

    OZ enum ordering: Floor=0, Ceil=1, Trunc=2, Expand=3.  For
    non-negative inputs (which is the only mode ERC4626 ever uses
    since uint256 values are >= 0):

      Floor  ~ Trunc       (round toward 0 / -infinity for non-neg are the same)
      Ceil   ~ Expand      (round toward +infinity / away from 0 for non-neg are the same)

    The "unsignedRoundsUp" predicate (OZ Math.sol:746) returns
    [uint8(rounding) % 2 == 1]: Ceil(1) and Expand(3) round up,
    Floor(0) and Trunc(2) round down. *)
Inductive Rounding : Set :=
  | Floor
  | Ceil
  | Trunc
  | Expand.

Definition rounds_up (r : Rounding) : bool :=
  match r with
  | Floor | Trunc => false
  | Ceil  | Expand => true
  end.

(** ----- Multiplication-then-division with rounding -----

    OZ's [Math.mulDiv(x, y, d, r)] computes [floor(x*y/d)] plus an
    optional +1 bump when [r] rounds up and [(x*y) mod d != 0].

    For unbounded [Z] (our mock domain), this reduces to the simple
    expression below.  Reverts (denominator = 0) are caller's
    responsibility — ERC4626 always passes [totalAssets + 1] or
    [totalSupply + 10^offset] which is always [>= 1].
*)
Definition muldiv (x y d : Z) (r : Rounding) : Z :=
  if Z.eqb d 0 then 0  (* placeholder; ERC4626 never reaches this *)
  else
    let q := (x * y) / d in
    let m := (x * y) mod d in
    if andb (rounds_up r) (negb (Z.eqb m 0)) then q + 1 else q.

(** ----- Power of ten (used for [10^_decimalsOffset()]) -----

    OZ writes [10 ** _decimalsOffset()].  For our mock we treat the
    offset as a small natural number (0-18 typical) and compute the
    power inductively.  An [_decimalsOffset = 0] gives a virtual-share
    multiplier of [10^0 = 1] (the OZ default).
*)
Fixpoint pow10 (n : nat) : Z :=
  match n with
  | O   => 1
  | S k => 10 * pow10 k
  end.

Lemma pow10_pos : forall n, 0 < pow10 n.
Proof.
  induction n as [|k IH].
  - cbn. lia.
  - cbn -[Z.mul]. apply Z.mul_pos_pos; [lia | exact IH].
Qed.

Lemma pow10_nonzero : forall n, pow10 n <> 0.
Proof. intros n. pose proof (pow10_pos n). lia. Qed.

(** ----- ERC4626 contract storage -----

    The vault carries:
      - The shares ERC20 ledger (composed by inclusion).
      - The opaque asset address.
      - A snapshot of the asset balance held at the vault's address
        ([totalAssets()]).
      - The decimals-offset constant ([_decimalsOffset()]).
      - The underlying-asset decimals (cached at construction).
      - The vault contract's own address (used as the [address(this)]
        in [totalAssets] and as the [from] in [transferFrom(caller,this,...)]
        on deposit).
*)
Record State : Set := {
  (** The shares ERC20 ledger.  [totalSupply] is read from this. *)
  shares             : ERC20.State;
  (** The opaque asset address — the external ERC20 the vault holds. *)
  asset_address      : Address;
  (** Snapshot of the asset balance the vault contract holds.  In OZ
      this is [IERC20(asset()).balanceOf(address(this))]; we carry
      it explicitly to avoid composing the external ERC20's storage
      at this layer. *)
  total_assets       : U256.t;
  (** The decimals-offset (a small natural number — OZ default 0). *)
  decimals_offset    : nat;
  (** The cached underlying-asset decimals (OZ caches this at
      construction; we keep it for [decimals()] readback). *)
  underlying_decimals : U256.t;
  (** The vault contract's own address (= [address(this)] in OZ).
      Used as the destination of [transferFrom] on deposit and as the
      source of [transfer] on withdraw. *)
  vault_address       : Address;
}.

(** Convenience constructor. *)
Definition empty_state
    (asset_addr vault_addr : Address)
    (offset : nat)
    (under_dec : U256.t) : State :=
  {| shares              := ERC20.empty_state 0;
     asset_address       := asset_addr;
     total_assets        := 0;
     decimals_offset     := offset;
     underlying_decimals := under_dec;
     vault_address       := vault_addr;
  |}.

(** ----- Result-monad with reverts -----

    Mirrors ERC20.Result.t.  Reverts encode the four
    [ERC4626ExceededMax*] errors defined at OZ:55-72.
*)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

Definition revert_exceeded_max_deposit  {A : Set} : Result.t A := Result.Revert 0 32.
Definition revert_exceeded_max_mint     {A : Set} : Result.t A := Result.Revert 32 32.
Definition revert_exceeded_max_withdraw {A : Set} : Result.t A := Result.Revert 64 32.
Definition revert_exceeded_max_redeem   {A : Set} : Result.t A := Result.Revert 96 32.

(** ===== View functions =====

    Direct ports of the OZ ERC4626 view-function surface.  Each is
    a pure projection of state; reverts are confined to the public
    mutator surface.
*)

(** [asset()] — the opaque asset address.  OZ:111-113. *)
Definition asset (s : State) : Address := s.(asset_address).

(** [totalAssets()] — the cached asset-balance snapshot.  OZ:116-118
    reads this via [IERC20(asset()).balanceOf(address(this))]; we
    return the cached snapshot.  See top-of-file modeling notes. *)
Definition totalAssets (s : State) : U256.t := s.(total_assets).

(** [totalSupply()] — delegates to the shares ERC20 ledger.
    Equivalent to [ERC20.totalSupply(s.shares)] but exposed as a
    direct field for syntactic match with OZ. *)
Definition totalSupply (s : State) : U256.t :=
  s.(shares).(ERC20.totalSupply).

(** [balanceOf(account)] — shares balance.  Delegates to ERC20.
    The vault contract's own balanceOf is the share token's
    balanceOf. *)
Definition balanceOf (s : State) (account : Address) : U256.t :=
  ERC20.balanceOf s.(shares) account.

(** [decimals()] — [_underlyingDecimals + _decimalsOffset()].
    OZ:106-108.  Caller may want this as a U256; we cast through Z. *)
Definition decimals (s : State) : U256.t :=
  s.(underlying_decimals) + Z.of_nat s.(decimals_offset).

(** ===== Internal conversions =====

    The two core arithmetic primitives.  All four public conversions
    delegate to these with a fixed rounding mode.  OZ:225-234.

    Formulas:
      shares = mulDiv(assets,
                      totalSupply + 10^offset,
                      totalAssets + 1,
                      rounding)
      assets = mulDiv(shares,
                      totalAssets + 1,
                      totalSupply + 10^offset,
                      rounding)

    Note the **virtual shares** ([10^offset]) and **virtual assets** (1)
    in the denominators.  These are the inflation-attack defense:
    they ensure the first depositor cannot get an arbitrary number
    of shares from a tiny deposit even if the attacker has donated
    assets to inflate [totalAssets].
*)
Definition _convertToShares
    (s : State) (assets : U256.t) (r : Rounding) : U256.t :=
  muldiv assets
         (totalSupply s + pow10 s.(decimals_offset))
         (totalAssets s + 1)
         r.

Definition _convertToAssets
    (s : State) (shares_amt : U256.t) (r : Rounding) : U256.t :=
  muldiv shares_amt
         (totalAssets s + 1)
         (totalSupply s + pow10 s.(decimals_offset))
         r.

(** [convertToShares(assets)] — Floor-rounded.  OZ:121-123. *)
Definition convertToShares (s : State) (assets : U256.t) : U256.t :=
  _convertToShares s assets Floor.

(** [convertToAssets(shares)] — Floor-rounded.  OZ:126-128. *)
Definition convertToAssets (s : State) (shares_amt : U256.t) : U256.t :=
  _convertToAssets s shares_amt Floor.

(** ===== Max view functions =====

    The base contract sets these to [type(uint256).max] for deposit /
    mint, and to the user's balance-derived cap for withdraw /
    redeem.  We use a generous sentinel value [U256.max] for the
    "unbounded" cases, exposing it as a constant.  Inheritors that
    cap deposits / mints override these.
*)
Definition u256_max : U256.t := 2^256 - 1.

(** [maxDeposit(receiver)] — OZ:131-133. *)
Definition maxDeposit (s : State) (_receiver : Address) : U256.t :=
  let _ := s in
  u256_max.

(** [maxMint(receiver)] — OZ:136-138. *)
Definition maxMint (s : State) (_receiver : Address) : U256.t :=
  let _ := s in
  u256_max.

(** [maxWithdraw(owner)] — OZ:141-143.  The Floor rounding here is
    intentional: maxWithdraw is the **floor** of the user's share
    balance translated to assets — the user can withdraw at most
    this many assets and still hold non-negative shares. *)
Definition maxWithdraw (s : State) (owner : Address) : U256.t :=
  _convertToAssets s (balanceOf s owner) Floor.

(** [maxRedeem(owner)] — OZ:146-148. *)
Definition maxRedeem (s : State) (owner : Address) : U256.t :=
  balanceOf s owner.

(** ===== Preview functions =====

    These compute what a deposit / mint / withdraw / redeem would
    return, with the **vault-favoring** rounding direction.  OZ:151-168.
*)

(** [previewDeposit(assets)] — Floor.  User receives at most this
    many shares for [assets]. *)
Definition previewDeposit (s : State) (assets : U256.t) : U256.t :=
  _convertToShares s assets Floor.

(** [previewMint(shares)] — Ceil.  User pays at least this many
    assets to mint [shares]. *)
Definition previewMint (s : State) (shares_amt : U256.t) : U256.t :=
  _convertToAssets s shares_amt Ceil.

(** [previewWithdraw(assets)] — Ceil.  User burns at least this many
    shares to withdraw [assets]. *)
Definition previewWithdraw (s : State) (assets : U256.t) : U256.t :=
  _convertToShares s assets Ceil.

(** [previewRedeem(shares)] — Floor.  User receives at most this
    many assets for [shares]. *)
Definition previewRedeem (s : State) (shares_amt : U256.t) : U256.t :=
  _convertToAssets s shares_amt Floor.

(** ===== Internal mutators =====

    [_deposit(caller, receiver, assets, shares)] — OZ:239-251.
    Implements: transfer-from caller to vault, then mint shares to
    receiver.  We do NOT model the asset's external ERC20 ledger
    here — we model the asset accounting on the vault side by
    bumping [total_assets] by [assets].  An inheritor's equivalence
    proof binds this to the actual external transfer via R063
    (staticcall bridge).

    The mock's variant takes the precomputed shares amount (matching
    OZ's signature); the public [deposit] computes shares from assets
    via [previewDeposit] before calling [_deposit].
*)
Definition _deposit
    (s : State) (caller receiver : Address) (assets shares_amt : U256.t)
    : State :=
  let _ := caller in
  let s_shares_after := ERC20.mint s.(shares) receiver shares_amt in
  {| shares              := s_shares_after;
     asset_address       := s.(asset_address);
     total_assets        := s.(total_assets) + assets;
     decimals_offset     := s.(decimals_offset);
     underlying_decimals := s.(underlying_decimals);
     vault_address       := s.(vault_address);
  |}.

(** [_withdraw(caller, receiver, owner, assets, shares)] — OZ:256-277.
    Implements: spend allowance (if caller != owner), burn shares from
    owner, transfer assets from vault to receiver.

    The mock returns a [Result.t] because the burn can revert on
    insufficient balance (delegated to ERC20.burn), and the allowance
    spend can revert on insufficient allowance.
*)
Definition _withdraw
    (s : State) (caller receiver owner : Address) (assets shares_amt : U256.t)
    : Result.t State :=
  let _ := receiver in
  (* Allowance spend on the shares token (only if caller != owner). *)
  let allowance_ok :=
    if Z.eqb caller owner then true
    else (negb (ERC20.allowance s.(shares) owner caller <? shares_amt))
  in
  if negb allowance_ok then Result.Revert 0 32
  else
    let shares_after_alw :=
      if Z.eqb caller owner then s.(shares)
      else
        let cur := ERC20.allowance s.(shares) owner caller in
        ERC20.approve s.(shares) owner caller (cur - shares_amt)
    in
    match ERC20.burn shares_after_alw owner shares_amt with
    | ERC20.Result.Revert p q => Result.Revert p q
    | ERC20.Result.Success s_after_burn =>
        Result.Success
          {| shares              := s_after_burn;
             asset_address       := s.(asset_address);
             total_assets        := s.(total_assets) - assets;
             decimals_offset     := s.(decimals_offset);
             underlying_decimals := s.(underlying_decimals);
             vault_address       := s.(vault_address);
          |}
    end.

(** ===== Public mutator surface =====

    Each delegates to [_deposit] / [_withdraw] with the appropriate
    preview computation and max-cap check.  OZ:171-220.

    Convention: we take the [caller] (= msg.sender) as an explicit
    argument.  The equivalence layer binds this to [Stdlib.caller].
*)

(** [deposit(assets, receiver)] — OZ:171-181.  Returns [(state', shares)]. *)
Definition deposit
    (s : State) (caller receiver : Address) (assets : U256.t)
    : Result.t (State * U256.t) :=
  let max_a := maxDeposit s receiver in
  if max_a <? assets then revert_exceeded_max_deposit
  else
    let shares_amt := previewDeposit s assets in
    let s' := _deposit s caller receiver assets shares_amt in
    Result.Success (s', shares_amt).

(** [mint(shares, receiver)] — OZ:184-194.  Returns [(state', assets)]. *)
Definition mint
    (s : State) (caller receiver : Address) (shares_amt : U256.t)
    : Result.t (State * U256.t) :=
  let max_s := maxMint s receiver in
  if max_s <? shares_amt then revert_exceeded_max_mint
  else
    let assets := previewMint s shares_amt in
    let s' := _deposit s caller receiver assets shares_amt in
    Result.Success (s', assets).

(** [withdraw(assets, receiver, owner)] — OZ:197-207.  Returns [(state', shares)]. *)
Definition withdraw
    (s : State) (caller receiver owner : Address) (assets : U256.t)
    : Result.t (State * U256.t) :=
  let max_a := maxWithdraw s owner in
  if max_a <? assets then revert_exceeded_max_withdraw
  else
    let shares_amt := previewWithdraw s assets in
    match _withdraw s caller receiver owner assets shares_amt with
    | Result.Revert p q => Result.Revert p q
    | Result.Success s' => Result.Success (s', shares_amt)
    end.

(** [redeem(shares, receiver, owner)] — OZ:210-220.  Returns [(state', assets)]. *)
Definition redeem
    (s : State) (caller receiver owner : Address) (shares_amt : U256.t)
    : Result.t (State * U256.t) :=
  let max_s := maxRedeem s owner in
  if max_s <? shares_amt then revert_exceeded_max_redeem
  else
    let assets := previewRedeem s shares_amt in
    match _withdraw s caller receiver owner assets shares_amt with
    | Result.Revert p q => Result.Revert p q
    | Result.Success s' => Result.Success (s', assets)
    end.

(** ===== Validity invariant =====

    The cross-state invariant that an inheritor's proofs lean on.
    Two facts:

      (a) The shares ERC20 is itself valid (sum of balances =
          totalSupply, balances non-negative, totalSupply within
          uint256).
      (b) [total_assets] is non-negative and within uint256.
      (c) [decimals_offset] is "reasonable" (we leave this as
          [decimals_offset <= 77]: the largest [10^77] still fits
          in 256 bits, since [10^77 < 2^256 < 10^78]).
*)
Module Valid.
  Record t (s : State) : Prop := {
    shares_valid     : ERC20.Valid.t s.(shares);
    total_assets_nn  : 0 <= s.(total_assets);
    total_assets_u256: U256.Valid.t s.(total_assets);
    offset_bounded   : (s.(decimals_offset) <= 77)%nat;
  }.

  Lemma empty_valid :
    forall asset_addr vault_addr offset under_dec,
      U256.Valid.t under_dec ->
      (offset <= 77)%nat ->
      t (empty_state asset_addr vault_addr offset under_dec).
  Proof.
    intros asset_addr vault_addr offset under_dec Hu Hoff.
    constructor; cbn.
    - apply ERC20.Valid.empty_valid.
      + unfold U256.Valid.t. lia.
      + reflexivity.
    - lia.
    - unfold U256.Valid.t. lia.
    - exact Hoff.
  Qed.
End Valid.

(** ===== Headline mock-level lemmas =====

    The cheap pure-Coq facts every equivalence/integration proof reuses.
    These are stated against the bare mock so the equivalence file's
    sim-level Qed lemmas can cite them without re-deriving. *)

(** [muldiv] zero numerator: [muldiv 0 y d r = 0]. *)
Lemma muldiv_zero_x : forall y d r, muldiv 0 y d r = 0.
Proof.
  intros y d r. unfold muldiv.
  destruct (Z.eqb d 0) eqn:Hd; [reflexivity|].
  apply Z.eqb_neq in Hd.
  rewrite Z.mul_0_l.
  rewrite Zdiv_0_l. rewrite Zmod_0_l.
  rewrite Z.eqb_refl.
  destruct (rounds_up r); cbn [andb negb]; reflexivity.
Qed.

(** [muldiv x 0 d r = 0] dually. *)
Lemma muldiv_zero_y : forall x d r, muldiv x 0 d r = 0.
Proof.
  intros x d r. unfold muldiv.
  destruct (Z.eqb d 0) eqn:Hd; [reflexivity|].
  apply Z.eqb_neq in Hd.
  rewrite Z.mul_0_r.
  rewrite Zdiv_0_l. rewrite Zmod_0_l.
  rewrite Z.eqb_refl.
  destruct (rounds_up r); cbn [andb negb]; reflexivity.
Qed.

(** [muldiv] of an exact-divisible product equals the quotient regardless
    of rounding mode (no rounding bump fires when the remainder is 0). *)
Lemma muldiv_exact :
  forall x y d r,
    d <> 0 ->
    (x * y) mod d = 0 ->
    muldiv x y d r = (x * y) / d.
Proof.
  intros x y d r Hd Hm.
  unfold muldiv.
  destruct (Z.eqb d 0) eqn:Hdb.
  - apply Z.eqb_eq in Hdb. contradiction.
  - rewrite Hm. rewrite Z.eqb_refl.
    destruct (rounds_up r); cbn [andb]; reflexivity.
Qed.

(** [convertToShares 0 = 0]: depositing zero assets yields zero shares. *)
Lemma convertToShares_zero :
  forall s, convertToShares s 0 = 0.
Proof.
  intros s. unfold convertToShares, _convertToShares.
  apply muldiv_zero_x.
Qed.

(** [convertToAssets 0 = 0]: redeeming zero shares yields zero assets. *)
Lemma convertToAssets_zero :
  forall s, convertToAssets s 0 = 0.
Proof.
  intros s. unfold convertToAssets, _convertToAssets.
  apply muldiv_zero_x.
Qed.

(** [previewDeposit 0 = 0]. *)
Lemma previewDeposit_zero : forall s, previewDeposit s 0 = 0.
Proof. intros s. apply muldiv_zero_x. Qed.

(** [previewMint 0 = 0]. *)
Lemma previewMint_zero : forall s, previewMint s 0 = 0.
Proof. intros s. apply muldiv_zero_x. Qed.

(** [previewWithdraw 0 = 0]. *)
Lemma previewWithdraw_zero : forall s, previewWithdraw s 0 = 0.
Proof. intros s. apply muldiv_zero_x. Qed.

(** [previewRedeem 0 = 0]. *)
Lemma previewRedeem_zero : forall s, previewRedeem s 0 = 0.
Proof. intros s. apply muldiv_zero_x. Qed.

(** ===== _convertToShares / _convertToAssets denominator positivity ===== *)

(** The shares-conversion denominator is always >= 1 (since
    [totalAssets + 1 >= 1]).  This is the safety property that
    [_convertToShares] never divides by zero. *)
Lemma convertToShares_denom_pos :
  forall s, 0 <= totalAssets s -> 0 < totalAssets s + 1.
Proof. intros s H. lia. Qed.

(** The assets-conversion denominator is always >= [10^offset] >= 1.
    Even with totalSupply = 0, the virtual-shares term keeps the
    denominator positive — this is the *inflation-attack defense*. *)
Lemma convertToAssets_denom_pos :
  forall s,
    0 <= totalSupply s ->
    0 < totalSupply s + pow10 s.(decimals_offset).
Proof.
  intros s Hns. pose proof (pow10_pos s.(decimals_offset)). lia.
Qed.

(** Specialization for offset = 0 (OZ default): the denominator
    bottoms out at 1.  This is the well-known shape of the
    "no virtual share padding" base case. *)
Lemma convertToAssets_denom_pos_default :
  forall s,
    s.(decimals_offset) = O ->
    0 <= totalSupply s ->
    0 < totalSupply s + pow10 s.(decimals_offset).
Proof.
  intros s Hoff Hns. rewrite Hoff. cbn. lia.
Qed.

(** ===== _deposit accounting ===== *)

(** [_deposit] bumps [total_assets] by exactly [assets]. *)
Lemma deposit_increases_total_assets :
  forall s caller receiver assets shares_amt,
    (_deposit s caller receiver assets shares_amt).(total_assets)
    = s.(total_assets) + assets.
Proof.
  intros. unfold _deposit. cbn. reflexivity.
Qed.

(** [_deposit] preserves the asset address. *)
Lemma deposit_preserves_asset_address :
  forall s caller receiver assets shares_amt,
    (_deposit s caller receiver assets shares_amt).(asset_address)
    = s.(asset_address).
Proof.
  intros. unfold _deposit. cbn. reflexivity.
Qed.

(** [_deposit] preserves the decimals offset. *)
Lemma deposit_preserves_offset :
  forall s caller receiver assets shares_amt,
    (_deposit s caller receiver assets shares_amt).(decimals_offset)
    = s.(decimals_offset).
Proof.
  intros. unfold _deposit. cbn. reflexivity.
Qed.

(** [_deposit] preserves vault address. *)
Lemma deposit_preserves_vault_address :
  forall s caller receiver assets shares_amt,
    (_deposit s caller receiver assets shares_amt).(vault_address)
    = s.(vault_address).
Proof. intros. unfold _deposit. cbn. reflexivity. Qed.

(** [_deposit] grows shares.totalSupply by [shares_amt] (modulo
    the [shares_amt = 0] case, which is a no-op). *)
Lemma deposit_grows_totalSupply :
  forall s caller receiver assets shares_amt,
    0 < shares_amt ->
    totalSupply (_deposit s caller receiver assets shares_amt)
    = totalSupply s + shares_amt.
Proof.
  intros s caller receiver assets shares_amt Hpos.
  unfold totalSupply, _deposit. cbn.
  rewrite ERC20.mint_increases_totalSupply by exact Hpos. reflexivity.
Qed.

(** [_deposit] adds [shares_amt] to receiver's balance (modulo
    zero-amount short-circuit). *)
Lemma deposit_credits_receiver :
  forall s caller receiver assets shares_amt,
    0 < shares_amt ->
    balanceOf (_deposit s caller receiver assets shares_amt) receiver
    = balanceOf s receiver + shares_amt.
Proof.
  intros s caller receiver assets shares_amt Hpos.
  unfold balanceOf, _deposit. cbn.
  unfold ERC20.balanceOf. cbn.
  unfold ERC20.mint.
  destruct (Z.eqb shares_amt 0) eqn:Hsh.
  - apply Z.eqb_eq in Hsh. lia.
  - cbn.
    fold (ERC20.balanceOf s.(shares) receiver).
    apply ERC20.balance_lookup_set_balance_eq.
Qed.

(** ===== _withdraw accounting (success path) ===== *)

(** [_withdraw] success path: [total_assets] drops by exactly [assets]. *)
Lemma withdraw_decreases_total_assets :
  forall s s' caller receiver owner assets shares_amt,
    _withdraw s caller receiver owner assets shares_amt
      = Result.Success s' ->
    s'.(total_assets) = s.(total_assets) - assets.
Proof.
  intros s s' caller receiver owner assets shares_amt Hok.
  unfold _withdraw in Hok.
  destruct (negb _) eqn:Halw; [discriminate|].
  destruct (ERC20.burn _ _ _) eqn:Hburn; [|discriminate].
  injection Hok as Hs'. subst s'. cbn. reflexivity.
Qed.

(** [_withdraw] success preserves the asset address. *)
Lemma withdraw_preserves_asset_address :
  forall s s' caller receiver owner assets shares_amt,
    _withdraw s caller receiver owner assets shares_amt
      = Result.Success s' ->
    s'.(asset_address) = s.(asset_address).
Proof.
  intros s s' caller receiver owner assets shares_amt Hok.
  unfold _withdraw in Hok.
  destruct (negb _); [discriminate|].
  destruct (ERC20.burn _ _ _); [|discriminate].
  injection Hok as Hs'. subst s'. cbn. reflexivity.
Qed.

(** [_withdraw] success preserves the offset. *)
Lemma withdraw_preserves_offset :
  forall s s' caller receiver owner assets shares_amt,
    _withdraw s caller receiver owner assets shares_amt
      = Result.Success s' ->
    s'.(decimals_offset) = s.(decimals_offset).
Proof.
  intros s s' caller receiver owner assets shares_amt Hok.
  unfold _withdraw in Hok.
  destruct (negb _); [discriminate|].
  destruct (ERC20.burn _ _ _); [|discriminate].
  injection Hok as Hs'. subst s'. cbn. reflexivity.
Qed.

(** ===== Inflation-attack defense bound =====

    The headline safety property of the [_decimalsOffset] virtual
    in OZ ERC4626.  Informally: even if an attacker donates
    [donation] assets to inflate [totalAssets] before the first
    deposit, the first depositor's share-to-asset ratio is bounded
    by [10^offset / 1 = 10^offset] virtual-share units of dilution.

    Formally: for any state [s] with [totalSupply = 0] (the empty
    vault), and any [donation >= 0], the first depositor of
    [assets] receives
      [assets * 10^offset / (totalAssets + 1)]
    shares (Floor).

    The defense ensures that, even with totalAssets inflated, the
    numerator [10^offset] cannot be reduced below the static
    virtual-shares constant, capping the attacker's gain.

    Note: this is a *floor* characterization — at offset = 0, the
    bound is the trivial [assets / (totalAssets + donation + 1)],
    which can be 0 for small [assets].  The defense's strength
    scales exponentially with [offset]. *)
Lemma inflation_attack_floor_shares :
  forall s assets,
    totalSupply s = 0 ->
    convertToShares s assets
    = muldiv assets (pow10 s.(decimals_offset)) (totalAssets s + 1) Floor.
Proof.
  intros s assets Hzero.
  unfold convertToShares, _convertToShares.
  rewrite Hzero. cbn. reflexivity.
Qed.

(** Specialization at offset = 0: empty vault first-depositor formula
    is simply [assets / (totalAssets + 1)] (floor). *)
Lemma inflation_attack_default_offset :
  forall s assets,
    totalSupply s = 0 ->
    s.(decimals_offset) = O ->
    convertToShares s assets
    = assets / (totalAssets s + 1).
Proof.
  intros s assets Hts Hoff.
  rewrite inflation_attack_floor_shares by exact Hts.
  rewrite Hoff. cbn.
  unfold muldiv. cbn.
  destruct (Z.eqb (totalAssets s + 1) 0) eqn:Hd.
  - apply Z.eqb_eq in Hd. lia.
  - rewrite Z.mul_1_r.
    destruct (Z.eqb (assets mod (totalAssets s + 1)) 0); cbn; reflexivity.
Qed.

(** ===== Roundtrip rounding-direction sanity =====

    Floor-then-Floor: depositing [assets] yields [shares = floor(...)],
    and then withdrawing [shares] yields [assets' = floor(... shares ...)],
    and [assets' <= assets].  The user pays the rounding tax.

    The cleanest closed form is the **floor preserves order on
    multiplication / division**, which we use as a building block.
*)
Lemma muldiv_floor_le_exact :
  forall x y d,
    0 < d ->
    0 <= x ->
    0 <= y ->
    muldiv x y d Floor * d <= x * y.
Proof.
  intros x y d Hd Hx Hy. unfold muldiv.
  destruct (Z.eqb d 0) eqn:Hdb.
  - apply Z.eqb_eq in Hdb. lia.
  - cbn [rounds_up andb].
    pose proof (Z.mul_div_le (x*y) d Hd) as Hle. lia.
Qed.

(** Dual: ceil times denom >= numerator (with the +1 bump on
    non-exact divides).  Useful for symmetry. *)
Lemma muldiv_ceil_ge_exact :
  forall x y d,
    0 < d ->
    0 <= x ->
    0 <= y ->
    x * y <= muldiv x y d Ceil * d.
Proof.
  intros x y d Hd Hx Hy. unfold muldiv.
  destruct (Z.eqb d 0) eqn:Hdb.
  - apply Z.eqb_eq in Hdb. lia.
  - apply Z.eqb_neq in Hdb.
    cbn [rounds_up].
    pose proof (Z_div_mod_eq_full (x*y) d) as Heq.
    assert (Hdgt : d > 0) by lia.
    pose proof (Z_mod_lt (x*y) d Hdgt) as [Hmlo Hmhi].
    destruct (Z.eqb ((x*y) mod d) 0) eqn:Hm.
    + apply Z.eqb_eq in Hm. cbn [andb negb]. lia.
    + cbn [andb negb].
      assert (Hq : ((x*y)/d + 1) * d = (x*y)/d * d + d) by lia.
      rewrite Hq. lia.
Qed.

(** ===== vm_compute sanity examples =====

    Smoke tests.  Each closes by [vm_compute; reflexivity] over a
    concrete state; serves as a check that the mock evaluates
    end-to-end. *)
Module Examples.

  Definition asset_addr  : Address := 100.
  Definition vault_addr  : Address := 200.
  Definition alice       : Address := 1.
  Definition bob         : Address := 2.

  (** Empty vault, offset = 0.  First-depositor scenario. *)
  Definition s0 : State :=
    empty_state asset_addr vault_addr 0 18.

  (** Alice deposits 100 assets at the empty vault. *)
  Example ex_first_deposit_default_offset :
    convertToShares s0 100 = 100.
  Proof. vm_compute. reflexivity. Qed.

  (** [convertToAssets 0 = 0] at empty vault. *)
  Example ex_convert_zero_assets : convertToAssets s0 0 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** [convertToShares 0 = 0]. *)
  Example ex_convert_zero_shares : convertToShares s0 0 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Empty vault with offset = 6 ("virtual shares" defense): first-depositor
      of 100 assets gets [100 * 10^6 / 1 = 10^8] shares.  This is the
      large dilution that makes the inflation attack uneconomic. *)
  Definition s_off6 : State :=
    empty_state asset_addr vault_addr 6 18.

  Example ex_first_deposit_offset_6 :
    convertToShares s_off6 100 = 100000000.
  Proof. vm_compute. reflexivity. Qed.

  (** maxRedeem at empty vault for alice is 0 (no shares yet). *)
  Example ex_maxRedeem_empty : maxRedeem s0 alice = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Successful deposit by alice: 100 assets -> 100 shares. *)
  Example ex_deposit_alice :
    match deposit s0 alice alice 100 with
    | Result.Success (s', sh) =>
        sh = 100 /\
        totalSupply s' = 100 /\
        totalAssets s' = 100 /\
        balanceOf s' alice = 100
    | _ => False
    end.
  Proof. vm_compute. repeat split. Qed.

  (** Empty state is valid. *)
  Example ex_s0_valid : Valid.t s0.
  Proof.
    apply Valid.empty_valid.
    - unfold U256.Valid.t. lia.
    - lia.
  Qed.

  (** previewDeposit and previewMint round in opposite directions:
      at the empty vault with no totalAssets and offset 0, the
      forward conversion (deposit) and reverse (mint) coincide
      because the formulas are exact for the empty case. *)
  Example ex_preview_pair_default :
    previewDeposit s0 100 = 100 /\ previewMint s0 100 = 100.
  Proof. vm_compute. split; reflexivity. Qed.

End Examples.

End ERC4626.
