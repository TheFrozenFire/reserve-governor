# Equivalence-proof methodology — survey of available precedents

Output of Phase 0.1 (task #166). Reviews two candidate
precedents — the upstream `rocq-of-solidity` repo and the sibling
`protocol/` repo — and records what to copy, what to skip, and what
gaps in our own pipeline that survey surfaces.

## TL;DR

- **The expected protocol-repo precedent does not exist.** The
  protocol repo's Rocq tree has the same Caveat-5 gap we do.
  Zero files there reference `make_state`, `SimulatedStorage`,
  `generated.`, `contracts.tutorial`, or anything else from the
  upstream equivalence apparatus. We cannot use that repo as a
  guide; it has not done equivalence proofs.
- **The only real precedent is the upstream itself.** The tutorial
  (`contracts/tutorial/`) and erc20 (`contracts/erc20/`) examples in
  rocq-of-solidity contain the full pattern.
- **Our pipeline is missing one step.** The upstream's equivalence
  proofs run against a *shallow*-embedded form of the contract
  produced by `rocq/scripts/shallow_embed.py`. Our `generated/`
  outputs are the deep-embedded form straight out of `--ir-rocq`.
  Before any equivalence proof can plausibly close, we either run
  `shallow_embed.py` over our outputs or change the methodology to
  prove directly against the deep embedding (much harder, no upstream
  tactics).
- **The upstream's apparatus rests on a non-trivial admitted base.**
  Roughly two-thirds of the lemmas in
  `rocq/RocqOfSolidity/proofs/RocqOfSolidity.v` are `Admitted`,
  including `run_mload`, `run_mstore`, `run_sload_u256`,
  `run_sstore_u256`, `run_keccak256_tuple2`, and the
  `CanonizeState.*` rewriting laws. Any equivalence proof we ship
  inherits those axioms. Disclosed honestly, that's still a useful
  result — it reduces "trust the hand-written sim matches Solidity"
  to "trust the upstream's hand-written Stdlib semantics matches the
  EVM" — but it's not zero-axiom.

## The candidate precedents

### 1. The protocol repo — empty result

Path: `~/git/reserve/formal-verification/protocol/formal-verification/rocq/`.

Directory tree: `Audit.v`, `WISDOM.md`, `README.md`, `_RocqProject`,
plus `proofs/` and `simulations/`. **No `generated/`. No
`equivalence/`. No `contracts/`.** The `_RocqProject` is purely
sim+proofs+xcheck files, identical in shape to our own.

Confirmation greps:

```
grep -rEl 'make_state|SimulatedStorage|SimulatedMemory' \
  ~/git/reserve/formal-verification/protocol/formal-verification/rocq
# → 0 matches

grep -rEl 'generated\.|contracts\.tutorial|RocqOfSolidity\.contracts' \
  ~/git/reserve/formal-verification/protocol/formal-verification/rocq
# → 0 matches
```

The protocol repo's Caveat-5 analog is documented in its `Audit.v`
the same way ours is; nobody has gone further. So `task #166` ends
with a "no precedent there" verdict — we cannot learn methodology
from sibling work.

### 2. The upstream rocq-of-solidity — the authoritative pattern

Path: `~/git/reserve/formal-verification/rocq-of-solidity/rocq/`.

Two example contracts are fully fleshed out:

| Path | Files | Total LOC |
|---|---|---|
| `RocqOfSolidity/contracts/tutorial/` | `contract.v`, `shallow.v`, `model.v` | 677 |
| `RocqOfSolidity/contracts/erc20/` | `contract.v`, `shallow.v`, `simulations/contract.v`, `proofs/contract.v` | ~2 350 |

The tutorial is the minimum-viable shape — an `add(a,b)` function
with overflow check. The erc20 is the realistic shape — full ERC20
storage layout, transfer / approve / mint / burn semantics,
mapping-of-mapping allowance keys.

We will treat the **erc20 example** as the canonical precedent. The
tutorial is too small to surface the storage-projection patterns we
actually need.

## How the upstream structures an equivalence proof

### Stage layout: four files per contract

For a contract named `Foo`, the upstream produces and maintains
four files under `contracts/foo/`:

| File | Source | Role |
|---|---|---|
| `contract.v` | `solc --ir-rocq` | Deep-embedded Yul IR — emitted mechanically. Uses `M.declare`, `M.call_function`, `M.get_var`, etc. Hard to read, harder to reason about directly. |
| `shallow.v` | `rocq/scripts/shallow_embed.py contract.v` | Shallow-embedded form of the same contract — the deep `M.*` combinators get folded into ordinary Gallina-monadic shape (`let~`, `M.pure`, `Shallow.if_`). Mechanical, but the right level for proofs. |
| `simulations/contract.v` | Hand-written | Pure Gallina model of the contract's behaviour at the level of business logic. The reference semantics the equivalence proof links to. |
| `proofs/contract.v` | Hand-written | The equivalence statement and proof. For each external function `f`, states a lemma `run_f` that ties `shallow.v`'s definition of `f` to `simulations/contract.v`'s pure-function model. |

The deep `contract.v` is referenced by name in the shallow `shallow.v`
(via the `Code.t` record's `hex_name` field) but the *proofs* never
unfold `contract.v` directly. Only `shallow.v` shows up in the proof
file's `Require Import` list. This matters: it means the trust path is
`Solidity source → solc-rocq → contract.v → shallow_embed.py →
shallow.v → equivalence proof`, with the `shallow_embed.py` step
being trusted-but-not-machine-checked.

### Stage A: the `--ir-rocq` deep embedding (we already have this)

Example from `contracts/tutorial/contract.v`:

```coq
Module Contract.
  Definition code : Code.t := {|
    Code.name := "Contract_16";
    Code.hex_name := 0x436f6e74726163745f3136...0000;
    Code.functions := [ ];
    Code.body :=
      M.scope (
        do! ltac:(M.monadic (
          M.scope (
            do! ltac:(M.monadic (
              M.declare (|
                ["_1"],
                Some (M.call_function (|
                  "memoryguard",
                  [ [Literal.number 0x80] ]
                |))
              |)
            )) in ...
```

That's almost-isomorphic to the Yul IR — heavy ltac-wrapped
expressions, every Yul statement an `M.*` constructor. This is
what `--ir-rocq` produces for every contract in our `generated/`
directory. It is **not** the form the upstream proves against.

### Stage B: shallow embedding (we don't have this)

`shallow_embed.py` mechanically rewrites `contract.v` into
`shallow.v`. Example from `contracts/tutorial/shallow.v`:

```coq
Definition checked_add_t_uint256 (x : U256.t) (y : U256.t) : M.t U256.t :=
  let~ '(_, (sum, x, y)) :=
    let sum := 0 in
    let~ x := [[ cleanup_t_uint256 ~(| x |) ]] in
    let~ y := [[ cleanup_t_uint256 ~(| y |) ]] in
    let~ sum := [[ add ~(| x, y |) ]] in
    let_state~ 'tt := [[
      Shallow.if_ (|
        gt ~(| x, sum |),
        do~ [[ panic_error_0x11 ~(||) ]] in
        M.pure (BlockUnit.Tt, tt),
        tt
      |)
    ]] default~ (sum, x, y) in
    M.pure (BlockUnit.Tt, (sum, x, y))
  in
  M.pure sum.
```

This is the same `checked_add` semantics, but each operation is now
an ordinary monadic `let~`/`M.pure` term that the upstream's tactics
can step through. The trick of `shallow_embed.py` is to know which
`M.declare`/`M.call_function` patterns can be inlined as Gallina
binders and which need to remain as opaque calls (e.g., panics,
reverts, external calls).

**Action required for our pipeline:** invoke
`/Users/jmart/git/reserve/formal-verification/rocq-of-solidity/rocq/scripts/shallow_embed.py`
over each `generated/<Name>.v` before any equivalence proof can be
plausibly stated. Phase 0.4 task should pick this up.

### Stage C: hand-written Gallina simulation

The upstream's `contracts/erc20/simulations/contract.v` shows the
pattern:

```coq
Module Storage.
  Record t := {
    balances : Dict.t Address.t U256.t;
    allowances : Dict.t (Address.t * Address.t) U256.t;
    total_supply : U256.t;
  }.
End Storage.

Definition _transfer (from to : Address.t) (value : U256.t) (s : Storage.t)
  : Result.t Storage.t := ...
```

That's the same style our own `simulations/<Name>.v` files already
use — a record for storage, a pure transition function for each
contract operation, an explicit `Result.t` for revert / success.
**Our existing simulations need essentially no rewriting** to fit
the upstream pattern; we just need to make sure storage layouts are
expressed in fields that have a corresponding `StorableValue.t`
representation (see "constraints" below).

### Stage D: the equivalence proof

Example from `contracts/erc20/proofs/contract.v`:

```coq
Lemma run_body codes environment state :
  environment.(Environment.callvalue) = 0 ->
  environment.(Environment.caller) <> 0 ->
  let storage' := [
    StorableValue.Map
      (Dict.declare_or_assign []
        environment.(Environment.caller)
        20);
    StorableValue.Map [];
    StorableValue.U256 20
  ] in
  exists memory',
  {{? codes, environment,
      Some (make_state environment state SimulatedMemory.init SimulatedStorage.init) |
    Erc20_403.body ⇓
    Result.Return 128 32
  | Some (make_state environment state memory' storage') ?}}.
```

Read that as: "starting from the canonical initial state, the
contract's `body` (constructor in this case) terminates with a
specific return value AND ends in a state where storage contains
exactly the projection of the sim's post-state". The judgment
`{{? codes, env, pre_state | expr ⇓ result | post_state ?}}` is the
upstream's propositional Hoare triple — defined in
`simulations/RocqOfSolidity.v`'s `RunO` module.

The proof body is the named-tactics dance:

```coq
Proof.
  eexists.
  unfold Erc20_403.body.
  l. { l. { c. { p. } p. } ...
       c. { apply_run_mstore. } CanonizeState.execute. p.
       ...
       c. { apply_run_sload_u256. } s.
       c. { apply run_checked_add_uint256. }
       c. { apply_run_sstore_u256. } CanonizeState.execute. p.
       ...
  }
Qed.
```

There's no automation magic — it's a step-by-step walk through the
shallow `body` definition, dispatching each combinator with the
matching named tactic. Long but mechanical.

## Relation between Yul-runtime state and simulation state

The upstream's `make_state` is the canonical "lift the sim's state
view into the runtime's state view":

```coq
Definition make_state environment state
    (memory : SimulatedMemory.t) (storage : SimulatedStorage.t) : State.t :=
  State.with_current_storage environment
    (state <| State.memory := Memory.of_u256_list memory |>)
    (Storage.of_storable_values storage).
```

with the supporting types:

```coq
Module SimulatedMemory.
  Definition t : Set := list U256.t.    (* 32-byte word stream *)
  Definition init : t := [0; 0; 0; 0; 0].
End SimulatedMemory.

Module SimulatedStorage.
  Definition t : Set := list StorableValue.t.   (* slot-indexed *)
End SimulatedStorage.

Module StorableValue.
  Inductive t : Set :=
  | U256 (value : U256.t)
  | Map  (value : Dict.t U256.t U256.t)
  | Map2 (value : Dict.t (U256.t * U256.t) U256.t).
End StorableValue.
```

Three things to highlight, because they constrain what we can
verify:

1. **Storage is a list keyed by slot index** (not by hash). Slot 0
   = `nth 0 storage`, slot 1 = `nth 1 storage`. The upstream
   pre-arranges the order to match the contract's declared field
   order. For `StakingVault` and similar OZ-derived contracts with
   namespaced storage (`bytes32 location`-based slots), this mapping
   gets non-trivial — we have to compute the actual EIP-7201 slot for
   the `INeumannSelectorRegistry.storageLocation()`-style location
   and map our sim's record fields into that index.
2. **`StorableValue` has exactly three variants**: a single `U256`
   value, a 1-deep `U256→U256` map, or a 2-deep
   `(U256×U256)→U256` map. No first-class support for:
   - **Structs in storage** (e.g., `UnstakingManager.locks[id] =
     struct {owner, startTime, endTime, amount}` — would need
     decomposition into 4 separate `U256` slots and manual keying via
     `keccak256` arithmetic).
   - **Dynamic arrays** (e.g., `_selectors[target]` in
     `OptimisticSelectorRegistry` — would need slot-index pointer +
     length + keccak-derived element slots, all hand-modeled).
   - **Packed uintN** (`uint48 startTime + uint48 endTime + ...`
     packed into a single `U256` slot — addressable via `and`/`shr`
     masking but no `StorableValue` variant carries the layout).
   - **Maps with bytes32 / address keys** (we'd need a typed adapter
     — `Address.t` is defined in the upstream as `U256.t` with a
     validity predicate, so addresses degrade cleanly; `bytes32` would
     similarly).
3. **`Dict.t` is the abstract finite map** at the simulation
   level — no operational semantics for it; just `Dict.get`,
   `Dict.declare_or_assign`, `Dict.Valid.t`. The runtime side
   compiles dictionary operations to the canonical
   `sload (keccak256_tuple2 key index)` shape via
   `Storage.run_sload_map_u256` and friends. Each access through
   the equivalence proof produces a `keccak256_tuple2 key index`
   term that has to be matched syntactically by the tactic — there's
   no semantic-level rewrite step.

### Implication for our planned targets

For ThrottleLib (Phase 1, the proof-of-method target): the storage
is two `U256` packed values (`lastFullChargeBlock`,
`unusedProposals`), no maps. **Storage layout fits cleanly into
`SimulatedStorage.t = [StorableValue.U256 last; StorableValue.U256
used]`.** Phase 1 should close without `StorableValue` extension.

For UnstakingManager (Phase 2): storage is `mapping(uint256 id =>
Lock)` with `Lock = {owner, startTime, endTime, amount}`. Cleanest
representation: decompose into multiple `StorableValue.Map`s, one
per field, all keyed by lock id. This is more verbose than the
production layout but provably equivalent if we model the contract's
slot arithmetic (`mapping`'s baseSlot + `keccak256(id, baseSlot)` +
field offset).

For VersionRegistry, RewardTokenRegistry (Phase 3): owner-gated
registries, mostly `U256` and `Address` slots plus a single
`mapping(address => uint256)`. Fits `SimulatedStorage.t` cleanly.

For Guardian (Phase 3): two `bytes32` role identifiers and a
`mapping(bytes32 => RoleData)` from OZ AccessControl. The
`RoleData` struct (`{members: mapping(address => bool), adminRole:
bytes32}`) is itself nested. We'd either model this as two layered
`Map`s (one for adminRole per role, one Map2 for member-set
indicator-bool), or punt to a high-level abstraction of the
AccessControl bookkeeping. Decision deferred to Phase 3.

For StakingVault / Governor / ProposalLib (the heavy targets that
Phase 4 will decide whether to attempt): packed structs everywhere,
namespaced-storage layouts, dynamic checkpoint history. Even
representing the storage layout faithfully under `StorableValue.t` is
multi-week work. The Phase 4 decision is real and should be
respected.

## Helper lemmas / tactics that get reused

### Named single-letter tactics (from `simulations/RocqOfSolidity.v:2192–2201`)

Every equivalence proof on shallow code is dispatched with the same
8 tactics:

| Tactic | Definition | Use |
|---|---|---|
| `p`  | `apply RunO.Pure` | Discharge a `M.pure …` leaf |
| `pe` | `apply RunO.PureEq` | Discharge a `M.pure (val₁ , val₂)`-with-equality leaf |
| `pr` | `eapply RunO.Primitive; [reflexivity ｜]` | Step through a `Stdlib.*` primitive whose first argument equality is by `reflexivity` |
| `l`  | `eapply RunO.Let` | Step through a `let~ x := e₁ in e₂` |
| `lu` | `apply RunO.LetUnfold` | Same as `l` but where the binding form is `let_state~` (state-threading) |
| `c`  | `eapply RunO.Call` | Step into a function call |
| `cu` | `apply RunO.CallUnfold` | Same as `c` but where the call needs the arg-tuple unfolded first |
| `s`  | `fold @LowM.let_; simpl_goal` | Canonicalise the goal after a step — folds reified `let_`, runs a lightweight `simpl` |

These are tiny but essential. Without them in scope a proof file
becomes ~10× longer. The proof file `proofs/contract.v` must
`Require Import simulations.RocqOfSolidity` to get them.

### Tactic templates for memory / storage operations

From `proofs/RocqOfSolidity.v:339–433`. These are `Ltac` macros that
recognise the `make_state … memory … storage` shape and dispatch the
appropriate axiom:

| Tactic | Discharges |
|---|---|
| `apply_run_mload` | `Stdlib.mload offset` from the runtime-level `make_state memory` |
| `apply_run_mstore` | `Stdlib.mstore offset value` |
| `apply_run_sload_u256` | `Stdlib.sload slot` against a `StorableValue.U256` slot |
| `apply_run_sstore_u256` | `Stdlib.sstore slot value` against a `StorableValue.U256` slot |
| `apply_run_sload_map_u256` | `Stdlib.sload (keccak256_tuple2 key slot)` against a `StorableValue.Map` slot |
| `apply_run_sstore_map_u256` | `Stdlib.sstore (keccak256_tuple2 key slot) value` against a `StorableValue.Map` slot |
| `apply_run_sload_map2_u256` | doubly-keccak'd 2-key map lookup |
| `apply_run_sstore_map2_u256` | doubly-keccak'd 2-key map update |
| `apply_run_keccak256_tuple2` | `Stdlib.keccak256 ptr 64` over a 2-word memory region |
| `apply_memory_update_at index word` | rewrite `make_state memory storage` after writing `word` into `memory[index]` |
| `CanonizeState.execute` | normalise repeated `with_current_storage` and `state <| memory := … |>` updates back into a canonical `make_state` form |

Pattern in proof bodies: after each storage-/memory-touching
combinator, call `apply_run_*`, then `CanonizeState.execute` to put
the post-state back in `make_state` shape, then `p` (or `s`) to
move on. Every `sload`/`sstore` in the contract's shallow form
costs ~3 lines of proof.

### The `Memory.update_at` rewrite

`proofs/RocqOfSolidity.v:36–64` defines a non-trivial *provable*
rewrite that lets the proof author replace `state.(State.memory)`
with the post-store memory inside a Hoare triple. This is the only
non-admitted lemma in the file beyond `Address.Valid.t` arithmetic
helpers and is reused everywhere.

### The `Stdlib` primitive primitives are admitted

What we depend on as axioms (these are the trust assumptions any
equivalence proof inherits):

- `Memory.of_u256_list : list U256.t → Memory.t` — Admitted
  abstract function. Its only "spec" lives in
  `Memory.run_mload` / `Memory.run_mstore` (also Admitted) which
  claim that the i'th 32-byte word maps to `nth_error i words`.
- `Storage.of_storable_values : list StorableValue.t → Storage.t` —
  Admitted abstract function. Spec lives in
  `Storage.run_sload_u256`, `Storage.run_sstore_u256`,
  `Storage.run_sload_map_u256`, etc. — all Admitted.
- `State.get_current_storage_with_current_storage_eq` — Admitted
  ring-equation for the state-getter / state-setter.
- `CanonizeState.update_memory_eq`,
  `CanonizeState.update_storage_eq`,
  `CanonizeState.with_current_storage_twice_eq` — Admitted
  canonicalisation laws.
- `run_keccak256_tuple2` — Admitted axiom that a 2-word `keccak256`
  call from the right memory layout returns
  `keccak256_tuple2 a b` (and the keccak primitive itself is left
  abstract via `Opaque StdlibAux.keccak256`).
- `Address.implies_and_mask` — Admitted constructive fact that
  any valid 160-bit address equals itself AND'd with the 160-bit
  mask.

Of the ~30 top-level lemmas in `proofs/RocqOfSolidity.v`, only
`Memory.update_at` is fully proved. The rest are scaffolding.

That's a substantial bundle of axioms to inherit. It is the
*correct* set for a verification effort — the alternative is to
re-derive the EVM-semantics axioms from the rocq-of-solidity runtime
itself, which would be a multi-PhD-thesis project — but we should be
explicit in `Audit.v` Caveat-5 about what trust path each equivalence
proof rests on.

## Tactic recipe for our own proofs (digest)

Per-contract per-operation, the proof skeleton is:

```coq
Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.     (* lu/cu/p/s/pe/l/c/pr *)
Require Import proofs.RocqOfSolidity.          (* apply_run_sload_u256 etc. *)
Require Import ReserveGovernor.generated.<Name>.   (* deep embedding *)
Require Import ReserveGovernor.generated.<Name>_shallow.  (* future: shallow form *)
Require Import ReserveGovernor.simulations.<Name>.

Module <Name>Equivalence.
  Lemma run_<operation> codes environment state
      <args> <storage_args>
      (H_<precondition_1> : ...)
      (H_<precondition_2> : ...) :
    let sim_pre  := <project storage to sim shape> in
    let sim_post := ReserveGovernor.simulations.<Name>.<operation>
                      <args> sim_pre in
    let storage' := <project sim_post back to StorableValue.t list> in
    {{? codes, environment,
        Some (make_state environment state SimulatedMemory.init <storage_pre>) |
      <Name>.<operation_in_shallow_form> ⇓
      Result.Ok <reified_return_value>
    | Some (make_state environment state SimulatedMemory.init storage') ?}}.
  Proof.
    unfold <Name>.<operation_in_shallow_form>.
    (* repeat (lu || cu || p || s || ...) for view operations *)
    (* For mutators: l → c → apply_run_sstore_u256 → CanonizeState.execute → p, per step *)
  Qed.
End <Name>Equivalence.
```

The `<project storage to sim shape>` and `<project sim_post back to
StorableValue.t list>` functions are the contract-specific glue —
roughly the `proj : YulStorage → SimState` and its inverse mentioned
in the planning notes (`rocq/proofs/equivalence/README.md`).

## What this changes about the work plan

1. **Phase 0.2 (probe RocqOfSolidity runtime)** must additionally
   account for the `shallow_embed.py` step in our pipeline. The
   task as written assumes we'll work against the deep
   `generated/<Name>.v` outputs; that's not what the upstream does
   and not the path of least resistance.
2. **Phase 0.4 (settle methodology decisions)** has its biggest
   open question pre-answered: we will use the upstream's 4-file
   layout, the `make_state` + `StorableValue.t` model, the
   `RunO` judgment, and the named tactics. The genuinely open
   question is whether we run `shallow_embed.py` to populate
   `generated/<Name>_shallow.v` or attempt the riskier direct-on-deep
   approach.
3. **Phase 0.5 (toy proof on a trivial function)** should target
   the actual ThrottleLib `_getProposalsAvailable` view function
   (single arithmetic operation, no storage writes) — that's the
   minimum thing meaningfully larger than the upstream's
   `checked_add_t_uint256` example.
4. **Phase 1.* (ThrottleLib)** is reasonably scoped. Two `U256`
   slots, one `+` operation, one `min` clamp. The sim already
   matches; the storage layout fits `[U256; U256]` exactly. The
   proof of `consumeProposalCharge` will look very similar to the
   tutorial's `run_checked_add_uint256` proof — maybe 30–50 lines.
5. **Phase 2.* (UnstakingManager)** likely needs `StorableValue`
   extension (or careful encoding) for the struct-valued mapping.
   This is non-trivial and warrants a dedicated investigation in
   Phase 2.1 before any proof attempts.
6. **Phase 3.* (registries + Guardian)** the OZ AccessControl
   modelling in Guardian is the biggest unknown. The other two
   registries are about as complex as ThrottleLib.
7. **Phase 4 decision is real.** Modelling StakingVault's
   delegation history (`Trace208`-style checkpoint arrays) and
   Governor's full state machine in `StorableValue.t` form is a
   multi-month effort each; the smart move is to leave Caveat-5
   partially open for those contracts and document what would close
   it rather than committing.

## Phase 0.2 addendum — runtime library probe

What follows extends the Phase 0.1 survey with the runtime-level
details Phase 0.2 (`task #167`) asked for: the `M.t` monad shape,
the `RunO` and `RunP` judgments, the `Stdlib` primitive surface, and
the `Code.t` record. Sources:
`rocq-of-solidity/rocq/RocqOfSolidity/RocqOfSolidity.v` (top of file)
and `rocq-of-solidity/rocq/RocqOfSolidity/simulations/RocqOfSolidity.v`
(lines 2100–2300 — the judgment and tactics).

### The `M.t` monad — really `LowM.t`

`M.t A` in generated code is a notation for `LowM.t A`, a deep-embedded
free monad with 9 constructors:

```coq
Inductive LowM.t (A : Set) : Set :=
| Pure        (output : A)
| Primitive   {B : Set} (primitive : Primitive.t B) (k : B -> t A)
| CallFunction (name : string) (arguments : list U256.t)
              (k : Result.t (list U256.t) -> t A)
| Loop        {In Out : Set} (init : In) (body : In -> t Out)
              (break_with : Out -> In + Out) (k : Out -> t A)
| CallContract (address : U256.t) (value : U256.t) (input : list Z)
              (is_static : bool) (is_delegate : bool)
              (k : U256.t -> t A)
| Let         {B : Set} (e1 : t B) (k : B -> t A)    (* proof marker *)
| Call        {B : Set} (e : t B) (k : B -> t A)     (* proof marker *)
| Impossible  (message : string).
```

`Let` and `Call` are *proof markers* — they're operationally equivalent
to a flattened sequence, but their explicit presence in the term lets
the `l` and `c` tactics step through one construct at a time. The
monadic bind `let_ : t A → (A → t B) → t B` is defined by structural
recursion at the top level, and the tactic `s := fold @LowM.let_;
simpl_goal` folds reified bind forms back into `let_` so each proof
step re-canonicalises the goal.

### `Primitive.t B` — the 30-primitive Yul/EVM surface

`Primitive.t` is the inductive of "impure operations that touch state":

- Scoping: `OpenScope`, `CloseScope`
- Locals: `GetVar`, `DeclareVars`, `AssignVars`
- Memory: `MLoad`, `MStore`
- Storage: `SLoad`, `SStore`, `TLoad`, `TStore`, `RLoad`, `RStore`
- Gas / block: `GetGas`, `GetBlockNumber`, `GetBlockTimestamp`
- Logging: `Log`
- Environment / accounts: `GetEnvironment`, `GetNonce`, `GetCodedata`,
  `GetCodeBytes`, `GetBalance`, `AccountExists`
- Account lifecycle: `CreateAccount`, `UpdateCodeForDeploy`,
  `UpdateCodeBytesForDeploy`, `Selfdestruct`
- Immutables: `LoadImmutable`, `SetImmutable`
- Debug: `CallStackPush`, `CallStackPop`

The interpretation function `eval_primitive : Environment.t →
Primitive.t B → State.t → (B + …) × State.t` lives in the same file but
is largely Admitted at the leaves where it touches the abstract
`Memory.t` and `Storage.t` (per Phase 0.1 finding).

### `Environment.t` and `State.t`

```coq
Module Environment.
  Record t : Set := {
    caller    : U256.t;     (* msg.sender at the current call *)
    callvalue : U256.t;     (* msg.value *)
    calldata  : list Z;     (* msg.data, byte-list *)
    address   : U256.t;     (* address(this) *)
    code_name : U256.t;     (* hex-encoded name of the executing code *)
  }.
End Environment.
```

`State.t` is a record holding `State.memory : Memory.t`, `State.accounts
: list (U256.t * Account.t)` (account map), plus transient storage,
self-destructed accounts list, and log accumulator. The per-account
`Account.t` carries `Account.storage : Storage.t`, `Account.code`,
`Account.nonce`, etc.

### Two judgments — `RunO` and `RunP`

`RunO` is the **exact-result Hoare triple**:

```coq
Reserved Notation "{{? codes , environment , state | e ⇓ output | state' ?}}"
  (* expanded to RunO.t codes environment output state e state' *).
```

You state "starting from `state`, expression `e` converges to *this
specific* `output` and ends in *this specific* `state'`." This is what
the tutorial and erc20 proofs use. The supporting tactics
`p/pn/pe/pr/prn/l/lu/c/cu/s` each correspond to a single `RunO`
constructor: `p = Pure`, `pe = PureEq`, `pr = Primitive`, `l = Let`,
`lu = LetUnfold`, `c = Call`, `cu = CallUnfold`, plus `s` for goal
canonicalisation after each step.

`RunP` is the **predicate-transformer Hoare triple**:

```coq
Reserved Notation "{{{ codes , environment , state | e ⇓ P_output_state' }}}".
```

The condition is "exists some final `(output, state')` such that
`P_output_state' output state'` holds." Same shape constructors
(`Pure`, `Primitive`, `CallFunction`, `Let`, `Call`) but parameterised
on a predicate over the result. Useful when the equivalence we want is
"the post-state preserves invariant I" rather than "the post-state
equals exactly this projection of the sim". Tactic `RunP.apply_pure`
exists; the rest mirrors the `RunO` style.

For our planned equivalence proofs in Phase 1+ I'd default to `RunO` —
the sim already computes the exact post-state, so why not use that
exact projection. `RunP` is the right choice if/when we extend
equivalence to **validity** statements (e.g., "any execution of
`createLock` from a valid state ends in a valid state, regardless of
the exact lock id assigned").

### `Code.t` and the function-call resolution

```coq
Module Code.
  Record t : Set := {
    name      : string;
    hex_name  : U256.t;      (* keccak-style hex-encoded name *)
    functions : list <fn>;   (* list of named in-contract Yul fns *)
    body      : M.t unit;    (* the top-level contract entry-point body *)
  }.
End Code.
```

A generated `.v` file emits a `Module Foo. Definition code : Code.t :=
…` for each compilation unit. `body` is the Yul-translated function
that runs when the code is invoked (constructor or selector
dispatcher). `functions` is the list of named Yul helpers, looked up
at call time via `Codes.get_function codes environment name` (the
`Codes.t` table is the cross-contract function registry; populated
from the `codes` parameter that every `RunO` triple carries).

A `LowM.CallFunction "fun_add_15" args k` term resolves at proof
time by looking up the function body in `Codes.t` and stepping into
its `M.t` value via the `c` tactic. The shallow form sidesteps this
by translating `LowM.CallFunction "fn_name" args` into a direct
Gallina call `fn_name args`, which is what makes shallow-proof much
shorter than deep-proof.

### Sound-vs-Admitted scorecard for the apparatus

`simulations/RocqOfSolidity.v` (2906 lines): definitions of `LowM.t`,
`Primitive.t`, `RunO`, `RunP`, plus the named tactics. The interpreter
`eval` exists but its soundness lemma `eval_is_run` is *commented out*
(lines 2252–2298) — that is, even the link between the executable
interpreter and the propositional `RunO` judgment is left open. Proofs
that target `RunO` directly don't depend on `eval`, so this gap doesn't
bite us, but it does mean we cannot get a "run the interpreter and
inspect the output" sanity check for free.

`proofs/RocqOfSolidity.v` (433 lines): ~30 lemmas, of which only
`Memory.update_at` (~30 lines) is fully proved. The rest — every
memory and storage axiom, every canonicalisation rewrite — is
`Admitted`. Every equivalence proof inherits this admitted base.

The trust path our equivalence proofs would establish:

```
Solidity source
  → solc-rocq (rocq-of-solidity fork; trusted: ~16k LoC of C++)
  → rocq/generated/<Name>.v  (deep embedding; trusted: --ir-rocq pipeline)
  → rocq/generated/<Name>_shallow.v  (shallow embedding; trusted: shallow_embed.py, ~500 LoC Python)
  → rocq/proofs/equivalence/<Name>.v  (equivalence proof; assumes upstream RocqOfSolidity admitted axioms)
  → rocq/simulations/<Name>.v  (Gallina sim; this is what audit_* theorems quantify over)
```

Every step contributes axioms; the closest we can get to "Audit.v
theorems hold over the Solidity contract" is "Audit.v theorems hold
over the Solidity contract, assuming:
- solc-rocq emits a faithful deep embedding,
- shallow_embed.py preserves operational semantics in shallow form,
- the RocqOfSolidity Stdlib axioms (mload / mstore / sload / sstore /
  keccak256_tuple2 / state-canonicalisation laws) correctly capture
  EVM semantics."

That's a strictly stronger guarantee than "theorems hold over the
hand-written sim" (Caveat-5 today) but it isn't zero-axiom and Audit.v
should say so explicitly.

### Implication for naming our own equivalence files

Given the upstream's `contracts/<Name>/{contract.v, shallow.v,
simulations/contract.v, proofs/contract.v}` layout, our directory tree
should mirror it as:

```
rocq/generated/<Name>.v             (already produced — deep embedding)
rocq/generated/<Name>_shallow.v     (new — produced by shallow_embed.py)
rocq/simulations/<Name>.v           (already exists — Gallina sim)
rocq/proofs/equivalence/<Name>.v    (new — equivalence proof)
```

The `_shallow` suffix avoids file-name collisions in the same directory
while making the relationship to the deep `<Name>.v` obvious. The
shallow file's module path inside Coq would be
`ReserveGovernor.generated.<Name>_shallow`, parallel to the existing
`ReserveGovernor.generated.<Name>`.

## Phase 0.3 addendum — ThrottleLib generated-output inspection

Output of `task #168`. Confirms the shape of the smallest target
(`ThrottleLib`) and uncovers two methodology questions that need
answering before Phase 0.4 closes.

### File shape

`rocq/generated/ThrottleLib.v` is **2 930 lines / 91 KB**. Structure:

```
Module ThrottleLib.
  Definition code : Code.t := {| ...constructor body... |}.   (* lines 6–156 *)
  Module deployed.
    Definition code : Code.t := {| ...runtime body... |}.     (* lines 158–2916 *)
  End deployed.
End ThrottleLib.

Import Ltac2.
Definition codes : list Code.t :=
  ltac2:(let codes := Code.get_codes () in exact $codes).      (* line 2922 *)
```

The "multi-`Definition codes` collision" the prior planning notes
warned about is a multi-contract issue. ThrottleLib emitted *alone*
has exactly one `Definition codes` and a clean two-module nest. The
ltac2 footer is the universal one-per-file pattern: an
implicitly-registered code list. **`coqc ThrottleLib.v` should
succeed once `RocqOfSolidity.RocqOfSolidity` is in the load path.**
(Has not been validated yet; Phase 0.5 will exercise this.)

### Storage shape — library-style, slot is an argument

The key Yul function for our proof targets:

```
Code.Function.make (
  "fun_consumeProposalCharge",
  ["var_proposalThrottle_slot"; "var_account"],   (* arguments *)
  [],                                              (* return values *)
  M.scope ( ... ) )
```

The function takes `var_proposalThrottle_slot` as its first
argument and reads/writes storage at offsets relative to that slot.
In Solidity terms: it is the compiled form of

```solidity
library ThrottleLib {
  function consumeProposalCharge(ProposerThrottle storage self,
                                  address account) internal { ... }
}
```

— i.e., the `storage self` reference is passed by slot number, not
derived from `address(this)` via EIP-7201. **Implication for the
equivalence proof:** abstract over the base slot. The lemma shape
becomes

```coq
Lemma run_consumeProposalCharge codes environment state
    (base_slot : U256.t) (account : Address.t)
    (sim_pre  : ProposerThrottle.t)
    (now      : U256.t)
    (H_state  : <storage at base_slot..base_slot+1 encodes sim_pre>)
    (H_time   : <block.timestamp lookups return now>)
    (H_sim    : ProposerThrottle.consumeProposalCharge now account sim_pre = sim_post) :
  exists memory',
  {{? codes, environment, Some <pre_state with sim_pre at base_slot> |
    ThrottleLib.deployed.fun_consumeProposalCharge base_slot account ⇓
    Result.Ok tt
  | Some <post_state with sim_post at base_slot, memory := memory'> ?}}.
```

The base slot stays symbolic; we never have to commit to a specific
EIP-7201 location. This is **easier**, not harder, than a contract
with `this`-rooted storage.

### Primitive footprint of `fun_consumeProposalCharge`

From a `grep` over the full file:

- **2 `sload`** calls (read packed `(lastFullChargeBlock,
  unusedProposals)` slot, possibly twice for re-validation)
- **1 `sstore`** call (write back the updated packed slot)
- **2 `timestamp`** calls (one in the available-charge computation,
  one in the post-write update — **flagged below**)
- **2 `and`** + **2 `shr`** ops in the consume path (packed-uint
  extraction: `(slot >> offset) & mask`)
- **4 `checked_*` arithmetic helpers** (`checked_add_uint256`,
  `checked_sub_uint256`, `checked_mul_uint256`, `checked_div_uint256`)
  — all reduce to ordinary `Z` arithmetic with a bounds check that
  reverts on overflow
- **0 `number`** calls — confirms block-number-free / time-only
  semantics (matches our existing `simulations/ProposerThrottle.v`)

That's roughly 15 storage- or primitive-touching steps in the
`fun_consumeProposalCharge` body. Each step costs ~3 lines of
named-tactic proof (`c. { apply_run_X. } CanonizeState.execute.
p.`), plus the arithmetic helpers are factored into their own lemmas
once and reused. Net proof size estimate: **150–250 lines of shallow
proof** for `fun_consumeProposalCharge`, including the storage
projection definitions, lemmas about packed-uint encoding, and the
top-level theorem.

### Two new methodology questions surfaced by Phase 0.3

**Question A — packed-uint storage decoding.** The Solidity `struct
ProposerThrottle { uint64 lastFullChargeBlock; uint192
unusedProposals; }` (or similar) is packed into a single `U256` slot
via `(unusedProposals << 64) | lastFullChargeBlock`. The upstream's
`StorableValue.U256` variant carries a single 256-bit word with no
field layout; the equivalence proof has to express the field-level
sim state by encoding/decoding masks on `U256.t` values.

The clean approach is to add a `StorableValue.Packed (fields : list
(nat * U256.t))` variant — or, more concretely for our case, define
a *contract-specific projection* outside `StorableValue.t`:

```coq
Definition encode_throttle (s : ProposerThrottle.t) : U256.t :=
  s.(ProposerThrottle.lastFullChargeBlock)
  + 2^64 * s.(ProposerThrottle.unusedProposals).

Definition project_storage (sim : ProposerThrottle.t)
    : SimulatedStorage.t :=
  [ StorableValue.U256 (encode_throttle sim) ].
```

Then the equivalence proof bridges the `(shr; and)` extract
operations on the `U256.t` to the field projections on
`ProposerThrottle.t`. No `StorableValue.t` extension needed; the
encode/decode obligation is contract-local.

**Question B — `block.timestamp` is read twice.** The Yul body
invokes `timestamp` twice (lines 1998 and 2398 in the generated
file). In real execution both reads return the same value (an
`Environment.t` field), but the `RunP.Primitive` constructor
permits the proof author to instantiate `value` independently for
each `Primitive` step. So the proof needs an additional assumption
forcing both reads to agree:

```coq
H_timestamp_constant :
  forall st, eval_primitive env Primitive.GetBlockTimestamp st = inl (now, st).
```

Or, cleaner, use the `RunO` form and have both `pr` steps
discharge to the same `now` variable. Either works. The honest doc
note is "we assume `eval_primitive` for `GetBlockTimestamp` is
state-pure" — true semantically, but not provable from the upstream
apparatus alone.

The same argument applies to `block.number`, `address`, `caller`,
`callvalue` — all are notionally constant within one external call.
For our equivalence proofs we'll bundle these as a single
`EnvConstants` predicate the lemma takes as a hypothesis.

### Recommendation for Phase 1

ThrottleLib is the right Phase 1 target. The contract is small
(2 030 lines of generated runtime code excluding header / Definitions
list / constructor), library-style (no `this`-rooted storage to
worry about), uses only the 12-or-so primitives the upstream's
infrastructure already covers, and the sim already matches the
field-level semantics. The two new questions above are
ThrottleLib-specific only inasmuch as they surfaced here; both
patterns will recur on every contract we touch, so resolving them
now sets up a reusable approach.

The proof-of-method (Phase 0.5) should target
`fun_getProposalsAvailable` — pure view function, no `sstore`,
single arithmetic computation, fewest moving parts. Then Phase 1.3
tackles `fun_consumeProposalCharge` (the mutator), which is the
real proof of method.

## Phase 0.4 — Methodology decisions

Output of `task #169`. With the upstream's apparatus surveyed and
ThrottleLib's actual shape known, the methodology choices are mostly
forced. Each decision is stated with its rationale; subsequent
equivalence proofs cite this section.

### D1. Equivalence-relation shape — `RunO` for "exact result", `RunP` for "any reached state satisfies P"

**Decision.** Use the upstream's `RunO.t` propositional Hoare-triple
judgment as the default. For each Yul function we prove a lemma of
the form

```coq
Lemma run_<op> ... :
  <sim_pre_holds> ->
  <env_constants_hold> ->
  sim_op sim_pre = sim_post ->
  {{? codes, env, Some <make_state with proj sim_pre> |
    shallow.<op> args ⇓ Result.Ok <reified_return>
  | Some <make_state with proj sim_post> ?}}.
```

For validity-style claims that need to hold across all reachable
post-states (e.g., "any execution of `createLock` from a valid state
ends in a valid state"), switch to `RunP.t`:

```coq
Lemma createLock_preserves_validity ... :
  Valid.t sim_pre ->
  {{{ codes, env, <pre_state> |
    shallow.createLock args ⇓ fun output state' =>
      exists sim_post, <state' is make_state with proj sim_post> /\
                       Valid.t sim_post /\
                       output = ...
  }}}.
```

**Rationale.** `RunO` is concrete enough that the proof body can
syntactically rewrite to the sim's post-state at every step (cheap,
mechanical, matches the upstream's tutorial / erc20 style). `RunP`
is the right tool only when "exact post-state" is overspecified — for
generic validity lifts, the upstream uses `RunP` (see
`RunP.apply_pure`'s shape: `fun output state' => output = _ /\ state'
= _`, which is `RunP` instantiated to a `RunO`-style point predicate
and therefore proves the same statement).

We do **not** pursue a deeper notion like bisimulation or trace
equivalence. The upstream apparatus doesn't support those naturally,
and per-operation refinement is enough to lift every `audit_*`
theorem we have written so far.

### D2. Storage projection — per-contract `proj_sim` and the inverse stays implicit

**Decision.** Each `proofs/equivalence/<Name>.v` defines a
`proj_sim : <Name>.Storage.t -> SimulatedStorage.t` function that
encodes the sim's storage record into the
`list StorableValue.t` form the upstream expects. The reverse
direction (`SimulatedStorage.t -> <Name>.Storage.t`) is **not**
defined explicitly. Instead, the equivalence theorem says "the
runtime's final storage equals `proj_sim sim_post`" — the sim post
is the witness, and we never recover sim state from runtime state.

For packed slots (multiple fields in one `U256` word), `proj_sim` is
the composition of:

```coq
Definition encode_<struct> (s : <struct>.t) : U256.t :=
  s.(field0) +
  2 ^ <offset_1> * s.(field1) +
  2 ^ <offset_2> * s.(field2) +
  ...

Definition proj_sim (s : <Name>.Storage.t) : SimulatedStorage.t :=
  [ StorableValue.U256 (encode_<struct> s.(<field>));
    ...
  ].
```

**Rationale.** Cheaper than a bijective sim ↔ runtime witness. The
sim is the source of truth; runtime state is a "view" of it through
the projection. This matches the tutorial / erc20 style exactly —
the `run_body` lemma's `storage'` value is constructed forward from
the desired sim post-state, not extracted backward from runtime state.

Per-contract decode obligations (e.g., that `(packed_u256 >> 64) &
2^192 - 1` returns the high field) are stated and proved as
contract-local *encode/decode* lemmas alongside the main proof,
**without** extending the upstream's `StorableValue.t` inductive.

### D3. Revert alignment — one sub-lemma per revert reason

**Decision.** For each revert path in the simulation, state a
separate `run_<op>_reverts_<reason>` lemma:

```coq
Lemma run_consumeProposalCharge_reverts_no_proposals codes env state
    base_slot account sim_pre :
  sim_pre.(unusedProposals) = 0 ->
  sim_pre.(lastFullChargeBlock) + refillPeriod > now ->
  ...
  {{? codes, env, Some <make_state with proj sim_pre> |
    shallow.fun_consumeProposalCharge base_slot account ⇓
    Result.Revert <ptr> <size>
  | Some <state with revert flag> ?}}.
```

The main "success" lemma `run_consumeProposalCharge` carries
preconditions ruling out every revert path:

```coq
Lemma run_consumeProposalCharge codes env state ... :
  sim_pre.(unusedProposals) > 0 \/
  sim_pre.(lastFullChargeBlock) + refillPeriod <= now ->
  ...
  Result.Ok tt
  ...
```

**Rationale.** Two reasons. First, this matches the simulation's
shape — our `simulations/*.v` files already enumerate revert reasons
via `revert_arithmetic`, `revert_invalid_target`, etc., each
returning a distinct `(p, size)` pair. Second, it keeps the success
proof clean — without the precondition split, every success proof
would need to discharge `sim_pre` is not in a revert state at every
step, which doubles the proof size.

Cross-contract: the sim-side `Result.t` variant from our existing
`simulations/*.v` (`Result.Revert p s`) maps 1:1 to the upstream's
`Result.t` `Revert p s` constructor at the runtime level. Same
revert codes, same memory layout for the revert data.

### D4. Operation-level granularity — one Yul function = one equivalence lemma

**Decision.** Equivalence lemmas are stated **per-Yul-function**,
where each Solidity external function compiles to one `fun_<name>`
helper. The dispatcher-level (`body` with the selector switch) gets
its own thin lemma that case-splits on the selector and calls into
the per-function lemmas.

We do not state sequence-level equivalence theorems directly. A
property like "calling A then B equals calling B then A under
condition X" is *derived* from the per-operation lemmas, not stated
against the runtime.

**Rationale.** Per-Yul-function granularity matches the upstream
exactly (every `Lemma run_*` in the erc20 example is per-function),
and it's the smallest unit that has a self-contained pre/post-state.
Going coarser invites dispatch-pattern complexity into every proof;
going finer (per Yul statement) loses the named-tactics' leverage.

### D5. Shallow vs deep — use the shallow form

**Decision.** Run `rocq-of-solidity/rocq/scripts/shallow_embed.py`
over each `rocq/generated/<Name>.v` to produce
`rocq/generated/<Name>_shallow.v`. State all equivalence proofs
against the shallow form. The deep `<Name>.v` is built but never
referenced in proofs.

Scripts to add:

1. Extend `formal-verification/scripts/ir-rocq-coverage` (or add
   `scripts/shallow-embed-sweep`) to invoke `shallow_embed.py`
   after each successful `--ir-rocq` run, emitting the shallow
   form alongside the deep one.
2. Both `<Name>.v` and `<Name>_shallow.v` go into
   `rocq/generated/` and are gitignored. The regen script becomes
   the source of truth for both.

**Rationale.** The upstream's named tactics (`lu/cu/p/s/pe/l/c/pr`)
all target the shallow form's `let~` / `M.pure` / `Shallow.if_`
shape. Proving against the deep form would mean re-deriving every
unfolding step ourselves — multiple orders of magnitude more work
with no payoff. The `shallow_embed.py` script is mechanical; we
trust it the same way we trust `solc --ir-rocq` itself.

The trust delta is small. `shallow_embed.py` is ~500 lines of
Python; if it ever rewrites deep operational semantics incorrectly,
the resulting shallow proof would still be a proof — just not of
the contract we thought we were verifying. Mitigation: spot-check a
handful of cases by hand-translating the deep form back from the
shallow and confirming they reduce to the same `LowM.t` term.

### D6. Environment-constant assumption — one bundled predicate

**Decision.** Every equivalence lemma takes a hypothesis
`H_env : EnvConstants env now block_num` where

```coq
Definition EnvConstants (env : Environment.t) (now block_num : U256.t) : Prop :=
  forall state,
    eval_primitive env Primitive.GetBlockTimestamp state = inl (now, state) /\
    eval_primitive env Primitive.GetBlockNumber state    = inl (block_num, state) /\
    (* address(this), msg.sender, msg.value, calldata length are env fields
       and are constant by construction *)
    True.
```

The `EnvConstants` predicate captures the obvious-but-not-mechanised
fact that block.timestamp, block.number, etc., are constant within a
single external call. The fields already on `Environment.t` (caller,
callvalue, calldata, address, code_name) don't need explicit
constancy assumptions — they're just record fields. Only the
state-touching primitives that the runtime *could* in principle
vary (`GetBlockTimestamp`, `GetBlockNumber`, `GetBalance`,
`GetGas`) need pinning.

**Rationale.** Cleaner than threading `H_timestamp_eq1_eq2`
hypotheses through every proof. Captures one of the upstream's
implicit assumptions explicitly in our axioms list. Easy to
audit-document: `EnvConstants` is one of the assumptions that an
equivalence proof rests on.

Add to `Audit.v` (when first equivalence proof lands): document
`EnvConstants` as an axiom of the equivalence tier, alongside the
upstream's admitted-by-default Stdlib lemmas.

### D7. Storage layout — symbolic base slot for libraries, fixed slots for contracts

**Decision.** Library-style contracts whose Yul functions take a
`<name>_slot` parameter (ThrottleLib, ProposalLib, ...) get
equivalence lemmas parameterised over a `base_slot : U256.t`
argument. Storage is asserted to encode the sim's state at offsets
relative to `base_slot`.

Contracts whose storage is `this`-rooted via EIP-7201 (StakingVault,
Governor, RewardTokenRegistry, ...) need an additional step:
compute the namespaced-storage location from a `bytes32 location`
constant and tie storage assertions to that fixed slot. For now,
defer this step — Phase 1 (ThrottleLib) and Phase 2
(UnstakingManager — also library-style) sidestep it. Phase 3 will
formalise the EIP-7201 location derivation when it first becomes
necessary.

**Rationale.** Library-style proofs are strictly simpler — we don't
have to encode the EIP-7201 keccak chain or the namespace string.
Starting on the simpler shape lets us validate the rest of the
methodology before tackling the harder one.

### D8. Audit.v cross-link — equivalence tier displaces Caveat-5 incrementally

**Decision.** When the first equivalence proof lands (ThrottleLib),
`Audit.v` Caveat-5's status changes from "fully open" to "partial":

> Caveat-5 (partial): claims about the contracts proved equivalent
> in `rocq/proofs/equivalence/` hold over the Solidity contract,
> assuming (a) solc-rocq emits a faithful deep embedding, (b)
> shallow_embed.py preserves operational semantics, (c) the
> RocqOfSolidity Stdlib axioms in `proofs/RocqOfSolidity.v` capture
> EVM semantics. For contracts not yet listed in the equivalence
> tier, the original Caveat-5 statement stands.

Each subsequent contract that lands an equivalence proof appends to
the "covered" list. Phase 4 decides whether to commit to closing
the remaining contracts or to leave Caveat-5 partial-permanently
for the heavyweight tier.

**Rationale.** Honest, audit-facing language. Doesn't overstate
what landing one equivalence proof buys us, and gives a clear
mechanism for incremental progress.

### Decisions summary table

| # | Topic | Decision |
|---|---|---|
| D1 | Equivalence-relation shape | `RunO.t` Hoare triple by default; `RunP.t` for validity statements |
| D2 | Storage projection | Per-contract `proj_sim` forward; no explicit reverse |
| D3 | Revert alignment | One sub-lemma per revert reason; success lemma has precondition ruling them out |
| D4 | Operation granularity | One equivalence lemma per Yul function |
| D5 | Shallow vs deep | Shallow form via `shallow_embed.py`; deep form built but unreferenced |
| D6 | Env constants | Bundled `EnvConstants env now block_num` predicate |
| D7 | Storage layout | Symbolic `base_slot` for libraries; defer EIP-7201 derivation until Phase 3 |
| D8 | Audit.v cross-link | Incrementally update Caveat-5 status as each contract lands |

## Phase 0.5 outcome — toy proof closes

Output of `task #170`. Deliverable:
`rocq/proofs/equivalence/Sandbox.v`. The file references the
upstream tutorial's shallow-embedded `Contract_16` and proves

```coq
Lemma toy_equivalence codes environment state (x y : U256.t)
    (H_x : 0 <= x < 2^256)
    (H_y : 0 <= y < 2^256)
    (H_no_overflow : x + y < 2^256) :
  {{? codes, environment, Some state |
    Contract_16.Contract_16_deployed.checked_add_t_uint256 x y ⇓
    Result.Ok (x + y)
  | Some state ?}}.
```

Built locally with

```sh
OPAM_SWITCH=rocq820 bash formal-verification/scripts/rocq-build \
    proofs/equivalence/Sandbox.v
# → All Rocq targets compiled successfully.
```

What this confirms end-to-end:

- The upstream library modules (`RocqOfSolidity.RocqOfSolidity`,
  `RocqOfSolidity.simulations.RocqOfSolidity`,
  `RocqOfSolidity.proofs.RocqOfSolidity`, and the worked
  `RocqOfSolidity.contracts.tutorial.shallow`) are all resolvable
  from our governor repo's coqc invocation via the
  `scripts/rocq-build` `-R` mapping.
- The `{{? … ⇓ … | … ?}}` Hoare-triple notation parses and the
  short-form tactics (`lu`, `cu`, `p`, `pe`, `s`) all dispatch
  correctly inside our build.
- The same proof body shape the tutorial uses (`unfold body; lu;
  repeat (lu || cu || p); s; unfold Pure.*; destruct ... eqn:?; …`)
  closes against a different precondition than the tutorial's own.
  The proof is not a copy — it states `x + y < 2^256` directly
  rather than the tutorial's `safe_add x y = Some sum` wrapper — and
  still passes, exercising the tactics from scratch.

The plumbing for the contracts we'll actually verify (running
`shallow_embed.py` on our `generated/<Name>.v` outputs to produce
`generated/<Name>_shallow.v`) is **not** yet built; it will be the
first plumbing task in Phase 1. The toy proof confirms the
foundation is sound; the per-contract work won't be blocked by
the methodology.

## Outputs of tasks #166, #167, #168, #169, #170

Phase 0 of the equivalence-proof workstream is complete. The
methodology is settled, end-to-end validated, and documented for
Phase 1+ to cite.
