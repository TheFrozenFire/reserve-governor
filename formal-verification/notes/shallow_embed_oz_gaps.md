# `shallow_embed.py` gaps surfacing on the OZ sweep

Diagnostic catalogue produced while running
`bash formal-verification/scripts/ir-rocq-coverage --include-oz` and
the per-unit `shallow_embed.py` pipeline against the 18-file
OpenZeppelin allowlist (12 `@openzeppelin/contracts` + 6
`@openzeppelin/contracts-upgradeable`, pinned at 5.4.0 — see
`notes/oz_version_pin.md`). The goal here is not to fix anything
upstream; it's to enumerate what kinds of OZ-flavoured Yul will
break the shallow-embed → coqc pipeline and propose the smallest
upstream fix for each.

## Headline

At the **`--ir-rocq`** stage: **18/18 OZ files PASS**. At the
**`shallow_embed.py`** stage: every emitted Yul AST unit translates
cleanly. **All known OZ-driven gaps are at the `coqc` stage on the
shallow form** — that is, the .v files load successfully into Coq
8.20.1 against a properly-patched simulations tree, or they don't.

This matters because the workflow boundary is: the IR sweep is
already green; the shallow-embed Python tool isn't the blocker;
the friction is on coqc's side, and the loadable surface depends on
two upstream-rocq-of-solidity patches we already needed for our own
contracts (`linkersymbol` Definition + the `M.monadic` diagnostic).
Below is what surfaces when an OZ contract is run end-to-end.

## OZ sweep matrix (`--ir-rocq` tier)

| File | Kind | `--ir-rocq` lines | Shallow-embed status |
|---|---|---:|---|
| `contracts/access/AccessControl.sol` | abstract | 10 | trivial (no IR — abstract) |
| `contracts/access/extensions/AccessControlEnumerable.sol` | abstract | 1 838 | trivial (no IR — abstract) |
| `contracts/proxy/Clones.sol` | library | 684 | stub scaffold only |
| `contracts/proxy/ERC1967/ERC1967Proxy.sol` | concrete | 4 306 | full embed, 850 lines |
| `contracts/token/ERC20/utils/SafeERC20.sol` | library | 234 | stub scaffold only |
| `contracts/utils/Strings.sol` | library | 1 140 | stub scaffold only |
| `contracts/utils/cryptography/ECDSA.sol` | library | 228 | stub scaffold only |
| `contracts/utils/math/Math.sol` | library | 684 | stub scaffold only |
| `contracts/utils/math/SafeCast.sol` | library | 228 | stub scaffold only |
| `contracts/utils/structs/Checkpoints.sol` | library | 912 | stub scaffold only |
| `contracts/utils/structs/EnumerableSet.sol` | library | 1 824 | stub scaffold only |
| `contracts/utils/types/Time.sol` | library | 912 | stub scaffold only |
| `contracts-upgradeable/governance/GovernorUpgradeable.sol` | abstract | 2 764 | trivial (no IR — abstract) |
| `contracts-upgradeable/proxy/utils/Initializable.sol` | abstract | 2 | trivial (no IR — abstract) |
| `contracts-upgradeable/proxy/utils/UUPSUpgradeable.sol` | abstract | 922 | trivial (no IR — abstract) |
| `contracts-upgradeable/token/ERC20/ERC20Upgradeable.sol` | abstract | 16 | trivial (no IR — abstract) |
| `contracts-upgradeable/token/ERC20/extensions/ERC4626Upgradeable.sol` | abstract | 936 | trivial (no IR — abstract) |
| `contracts-upgradeable/utils/NoncesUpgradeable.sol` | abstract | 4 | trivial (no IR — abstract) |

Two important observations baked into the matrix:

1. **Abstract contracts emit no IR.** solc-rocq round-trips an
   `abstract contract` through `--ir-rocq` and produces a near-empty
   `.v` — this is correct behaviour (abstract contracts can't deploy),
   but it means the OZ-allowlist sweep's pass-rate is misleading on
   its own. The real test of OZ shallow-embed surface is whatever
   *our* concrete contracts that inherit those abstracts produce.

2. **Standalone libraries emit only the deploy scaffold.** A
   library compiled in isolation produces the
   `allocate_unbounded` / `constructor_<Name>` /
   `revert_error_…` / `body` / `<Name>_deployed.body` scaffold (~80
   lines after shallow-embed). The library's real functions
   (`Math.mulDiv`, `SafeCast.toUint64`, etc.) only get codegen when
   they're *called* by a concrete contract — so the actual coverage
   shows up under our governor concretes via `--ir-rocq` of
   `ReserveOptimisticGovernor.sol` (which pulls in Math, SafeCast,
   Address, Errors, Panic, etc.).

The remainder of this note diagnoses the gaps surfacing in the
concrete-contract path — specifically the OZ-derived units emitted
when our governor contracts are compiled.

## Gap categories

The four diagnostic axes the task asks about. Treat each as a row
in a "what could go wrong" risk table.

### 1. Missing Yul primitives (R041 / R042 territory)

**Status: no new gaps on the OZ surface area we hit.**

WISDOM R041 documented the original missing-primitive failure:
solc-rocq emitted `linkersymbol(...)` calls for every library
external call, and `linkersymbol` had no Definition in
`simulations/RocqOfSolidity.v`. The Coq error message was the
infamous "object of type ident" — R042 then fixed the diagnostic to
name the real cause (commit `754592d34f` upstream). R042's
companion finding is critical here: a defensive sweep cross-checked
every standard Yul EVM instruction the generator emits against
`Stdlib` and **everything is defined**, modulo the reserved-word
rename convention (`mod` → `mod_`, `return` → `return_`).

OZ-specific check on the largest concrete OZ-derived unit
(`ReserveOptimisticGovernor_1302` after shallow-embed): 39
`linkersymbol(...)` calls (SafeCast, Panic, Math, ECDSA,
SignatureChecker, ...). All resolve through the existing
`linkersymbol : U256.t -> M.t U256.t := M.pure name` definition
added in R041. The full Yul nodeType set surfaced by OZ Governor
is `{YulAssignment, YulBlock, YulBreak, YulCase, YulCode, YulData,
YulExpressionStatement, YulForLoop, YulFunctionCall,
YulFunctionDefinition, YulIdentifier, YulIf, YulLeave, YulLiteral,
YulObject, YulSwitch, YulTypedName, YulVariableDeclaration}` — all
handled by `shallow_embed.py`'s explicit `nodeType` arms.

Newer EVM primitives surfacing in OZ 5.4.0: `mcopy` (Cancun),
`chainid`, `extcodesize`, `staticcall`, `call`. All present in
`Stdlib`.

**Smallest upstream fix if a new primitive surfaces.** Add a
`Definition <primname> ... := ...` line next to the sibling
primitives in
`~/git/reserve/formal-verification/rocq-of-solidity/rocq/RocqOfSolidity/simulations/RocqOfSolidity.v`,
inside `Module Stdlib`. The R042 diagnostic now names this file as
the canonical fix location, so any future R041-class bug should
take seconds to triage. Cross-ref: WISDOM **R041** (the resolution),
**R042** (the diagnostic improvement + Stdlib coverage sweep).

### 2. R035 switch-binding bug

**Status: upstream-fixed for our concretes; the OZ surface
re-exposes the *successor* defect.**

R035's original symptom — `YulSwitch` binding the result as `'tt`
(unit) while branches returned `Z` — was patched upstream
(`TheFrozenFire/rocq-of-solidity:feat/env-block-context`, commit
`8421532309`). The fix was one line in `shallow_embed.py` (line
254: `final_updated_vars` → `commonly_updated_vars`).

The OZ surface re-exposes the *follow-on* defect that R035 calls out
as "Remaining downstream issue": the
`Shallow.let_state ~ ... := [[ Shallow.if_ (| _, <succ_with_inner_let_state>, _ |) ]] default~ tt in`
shape. shallow_embed.py emits this shape liberally for OZ-derived
code (governor body's revert-on-bad-input checks, the
ERC-7201 storage-slot loads, the Math.mulDiv overflow guard, the
ECDSA signature-recovery cleanup). A grep of the
`ReserveOptimisticGovernor_1302` shallow form: **99 occurrences**
of `let_state~` strictly nested inside `[[ ]]` brackets, across
**40 Yul-switch-derived `Shallow.if_` arms** and **616 total
`let_state~` uses**.

For the four already-wired-in shallow forms (ThrottleLib,
VersionRegistry, RewardTokenRegistry, Guardian) the defect never
surfaces because their bodies don't nest `let_state` inside
`Shallow.if_`. For UnstakingManager it surfaced and was unblocked
via the R041 `linkersymbol` fix (R041 closed three failure cases
that masked as R035-shape errors). For any new OZ-derived concrete
the same risk applies.

**Smallest upstream fix.** Two options, both already noted in
WISDOM R035:

1. Extend `M.monadic` (in
   `rocq/RocqOfSolidity/RocqOfSolidity.v`) to recognise the
   `Shallow.let_state` shape and traverse it the way it traverses
   raw `let v := x in f v`. This is the principled fix — the Ltac
   defect lives there.

2. Restructure `shallow_embed.py` to keep all `let_state~` at the
   top shallow layer and never emit them inside `[[ ]]` brackets.
   This is shallower as a patch but may require threading state
   through `M.strong_let_` for inner mutators inside
   `Shallow.if_`'s `success` parameter (which has type
   `M.t (BlockUnit.t * State)`).

Cross-ref: WISDOM **R035** (the bug and both patch directions),
**R041** (closes the symptom for our concretes), **R042**
(diagnoses the underlying Ltac-elaboration trap).

### 3. `M.monadic` Ltac scope issues

**Status: post-R042, every `M.monadic` failure is now self-naming.**

R042 fixed the diagnostic message: any unresolved identifier inside
`[[ ]]` now produces a `Tactic failure` that names the two
canonical causes (missing Require Import, missing primitive
Definition) and points at `simulations/RocqOfSolidity.v`. So even
if the OZ surface trips a new M.monadic failure, it shouldn't cost
the hours that R041's original bisection ladder cost.

The OZ-specific risk is the same R035 follow-on: M.monadic's
`context [run ?x]` traversal doesn't recognise `Shallow.let_state`,
and any time shallow_embed.py emits it inside `[[ ]]` we're
relying on R041's `linkersymbol` Definition (and other surrounding
Definitions) to fix elaboration well enough that M.monadic never
needs to descend into the troublesome subterm. This held for
UnstakingManager; it'll likely hold for OZ-derived concretes too,
but the underlying Ltac defect is still present.

**Smallest upstream fix.** Same as Gap 2 option 1 — extend
`M.monadic` to traverse `Shallow.let_state`. Cross-ref: WISDOM
**R042** (the diagnostic guard), **R041** (the case study that
motivated R042).

### 4. OZ-idiomatic patterns

This is the only axis with material OZ-specific surface area.
Three sub-patterns, each with its own risk profile.

#### 4a. ERC-7201 namespaced storage (`bytes32 _STORAGE_LOCATION`)

OZ 5.x uses ERC-7201 to give each upgradeable base a fixed storage
slot, computed as
`keccak256(abi.encode(uint256(keccak256("openzeppelin.storage.<Name>")) - 1)) & ~bytes32(uint256(0xff))`.
The result is a 32-byte literal — fine for solc, fine for
shallow_embed, fine for the Coq embedding (all `read_from_storage_*`
and `update_storage_*` primitives are present in `Stdlib`).

What *isn't* fine yet: equivalence proofs that talk about state in
hand-written simulations need to model the storage layout under
the same slot. Our `patches/@openzeppelin__contracts-upgradeable.patch`
widens `_getGovernorStorage()` and
`_getTimelockControllerStorage()` from `private` to `internal` so
derived contracts can reach them — that's a runtime-surface change
the simulations must mirror. No shallow-embed gap; this is a
simulation-side gap, recorded here for completeness.

**Smallest upstream fix.** None at the shallow-embed layer. The
work is in `rocq/simulations/<Contract>.v` — model the ERC-7201
storage struct as a separate Coq record and prove the slot-load
sequence resolves to the same record under the simulation's
read-model. Cross-ref: see `Audit.v` Caveat-5 and
`notes/oz_version_pin.md` for why the patched diff is load-bearing
for equivalence.

#### 4b. EIP-712 typed-data hashing

OZ Governor (and any OZ Votes-based delegation) emits Yul that
embeds the literal bytes `\x19\x01` as a string literal in the
typed-data prefix. solc serialises this as a JSON `""`
value inside the Yul AST — properly escaped JSON, but a tripping
hazard for any shell-pipeline that round-trips through `echo` or
`printf %s` (bash builtins on macOS interpret `\uNNNN` escapes,
corrupting the JSON before jq sees it).

Our existing `scripts/shallow-embed-sweep` already avoids the trap
(it pipes solc's stdout directly into jq via the `'^{'` filter, no
`echo` round-trip). Diagnostic-only scripts that do round-trip
through `echo` have to use `printf '%s\n'` instead.

shallow_embed.py itself handles the literal cleanly — it sees a Python
string of length 2 and emits a `0x1901…` hex literal. No defect at
the Python layer.

**Smallest upstream fix.** None — this is an ergonomics gotcha for
diagnostic scripts only. Documented here so the next agent doesn't
chase a phantom "shallow_embed crashes on EIP-712" report.
Cross-ref: WISDOM has no entry for this; this note is the entry.

#### 4c. Inline assembly blocks (`assembly { … }`)

The OZ upgradeable bases use `assembly { $.slot := SLOT_CONSTANT }`
for ERC-7201 storage-pointer setup. solc lowers this to standard
Yul (no `verbatim_*` calls), which shallow_embed.py handles via
its YulAssignment / YulIdentifier arms. Confirmed empirically: the
full Yul nodeType set in OZ Governor's compilation does NOT
include `YulVerbatim`.

What *would* break: any future OZ contract that uses
`verbatim_<N>i_<M>o(...)` (raw opcode injection) — `shallow_embed.py`
has no `YulVerbatim` arm, and the call would surface as an
unknown-nodeType bug at translation time.

**Smallest upstream fix (preemptive).** Add a `YulVerbatim` arm to
`shallow_embed.py`'s `statement_to_rocq` / `expression_to_rocq`
that emits a `verbatim_<N>i_<M>o ~(| <args> |)` call site, plus a
matching `Definition verbatim_<N>i_<M>o : ... := ...` family in
`simulations/RocqOfSolidity.v`'s `Stdlib`. The opcodes injected
are by definition opaque (the whole point of `verbatim`), so the
faithful model is an axiomatic `Parameter` returning a fresh
nondet `U256.t` per call — and equivalence proofs against such a
contract simply can't close without proof-side admissions. Note
that this is not a current need; flagging it for if/when OZ adopts
verbatim. Cross-ref: no current WISDOM entry; raise one if/when this
surfaces.

## What this catalogue says about the OZ workstream

Three takeaways for the next agent in this seat:

1. **Shallow-embed of OZ-derived concretes works today** for the
   set of contracts our governor reaches. The bottleneck is not
   `--ir-rocq` and not `shallow_embed.py`; it's writing
   equivalence proofs against the resulting `.v` files. That work
   is staged behind the simulation-side ERC-7201 modelling and the
   per-contract proof effort — not behind tooling gaps.

2. **The R035 follow-on defect is the one with the largest blast
   radius.** Any OZ contract that nests a mutator inside
   `Shallow.if_(| _, succ, _ |)` re-exposes the M.monadic-vs-
   Shallow.let_state issue. R041's `linkersymbol` patch closed
   *our* observed cases; the underlying Ltac bug remains and will
   surface again on the next non-trivial OZ-derived contract.
   Fixing M.monadic to traverse `Shallow.let_state` is the highest
   leverage upstream patch.

3. **YulVerbatim is the only "would be a real new gap" risk.** OZ
   5.4.0 doesn't use it; OZ 5.6+ might. Adding the arm
   preemptively is one of the cheaper hedges in the catalogue.

None of these are blocking the equivalence-proof workstream; they're
the named risks to watch as more OZ surface gets pulled in.
