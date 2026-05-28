# Certora / CVL discipline (Reserve formal-verification)

Lessons captured while authoring Certora specs under
`formal-verification/certora/` and bringing the local prover online.
Each entry documents a Certora/CVL gotcha that cost real time during
this work. Mirrors the `rocq/WISDOM.md` convention. C-prefix because
R is taken.

## C001: `^` is XOR in CVL, not exponent

CVL inherits Solidity-style operator semantics: `^` is bitwise XOR.
`10^18 == 24` (because `10 XOR 18 = 24`), not `10**18`. A rule like

```cvl
assert params.vetoThreshold <= 10^18;
```

verifies trivially under almost any input because the constant
collapses to 24. This was caught during the Governor coverage push
when the agent re-read its own rule and realized it had been silently
"verifying" against a wrong constant.

**Workaround:** use base-10 literals for exponents:

```cvl
assert params.vetoThreshold <= 1000000000000000000;  // 1e18
```

CVL has no `**` operator. Define a constant in the spec if you want
the literal in one place:

```cvl
definition WAD() returns uint256 = 1000000000000000000;
```

Sanity check: any rule with a constant that looks exponential is
suspect. If verification was suspiciously fast, suspect this.

## C002: "Failures summary" in stdout is misleading for vacuity checks

`certoraRun.py` aggregates anything that looks like a violated assert
into a "Failures summary" block at the end of stdout. Vacuity sanity
checks intentionally have a `VIOLATED_ASSERT`-shaped child (their
internal mechanism is "assert a contradiction; if you can violate it,
the precondition was satisfiable"). Those land in the same summary.

**Workaround:** trust the JSON, not the stdout. A sanity check with

```
nodeType=VIOLATED_ASSERT  status=VERIFIED
```

is **passing** — it means the precondition is satisfiable, which is
the desired outcome. Only worry when the **ROOT** rule itself shows
`status=VIOLATED`.

Quick extractor:

```sh
RUN_DIR=$(ls -dt emv-*-certora-* | head -1)
python3 -c "
import json, glob
files = sorted(glob.glob(f'$RUN_DIR/Reports/treeView/treeViewStatus_*.json'))
with open(files[-1]) as f: data = json.load(f)
def walk(n, d=0):
    if 'name' in n and 'status' in n:
        print(f'{\"  \"*d}{n[\"name\"][:55]:55} status={n.get(\"status\",\"?\")} type={n.get(\"nodeType\",\"\")}')
    for c in n.get('children', []): walk(c, d+1)
for r in data.get('rules', []): walk(r)
"
```

## C003: `external` summary does NOT propagate through self-calls

If an OZ base contract internally calls `this.foo()` (or directly
calls its own external function via internal JUMP, as the optimizer
often emits), the CVL `external` summary on `foo()` is silently
bypassed. The StakingVault agent hit this on `_convertToShares ->
totalAssets()`: an `external` summary on `totalAssets()` had no
effect; the rule kept timing out as if the call was fully modeled.

**Workaround:** summarize the **internal** helper directly:

```cvl
methods {
    function _calculateHandout(uint256, address) internal returns (uint256) => CONSTANT;
}
```

Or restructure the rule so the self-call path is never exercised.

A symptom that points at this: a rule that should be trivial because
of an obvious external summary still times out at the SMT layer.

## C004: OZ EnumerableSet has cross-slot HAVOC

`EnumerableSet` keeps `_values` (the array) and `_positions[v]` (a
1-indexed slot pointing into the array). The invariant is

```
_positions[v] in [1, _values.length]  iff  _values[_positions[v]-1] == v
```

Certora's storage exploration treats `_positions` and `_values` as
independent mappings. Initial states can have `_positions[v] = 3` but
`_values[2] != v`, which then breaks any rule whose action exercises
the set:

- "register adds to set" can VIOLATE when an initial-state pathology
  makes `_contains()` return false after `_add()`.
- "remove doesn't affect other elements" can VIOLATE for the same
  reason.

Two contracts hit this independently in this push
(RewardTokenRegistry, OptimisticSelectorRegistry).

**Workaround options, easiest first:**

1. State the **symmetric** direction. "After remove, isRegistered(x) =
   false" tends to be provable; "after register, isRegistered(x) =
   true" tends to be the one that hits HAVOC. The pair of symmetric
   provable directions captures most of the semantic intent.

2. Document the deferred direction in the spec header and note the
   invariant lives in the Rocq simulation instead.

3. `requireInvariant` encoding the cross-slot consistency at the top
   of the rule. Heavyweight but airtight.

## C005: Interface-typed params need an address-typed local

A function signed `f(IFoo arg)` does not accept a numeric literal in
CVL. `f@withrevert(e, 0)` fails to typecheck with

```
Could not find an overloading of method ... that matches the given
arguments: 0
```

**Workaround:** declare an `address` local and constrain it:

```cvl
address zeroArg;
require zeroArg == 0;
f@withrevert(e, zeroArg);
```

CVL converts `address` to interface types implicitly; what fails is
the integer-literal-to-interface coercion.

## C006: Initial storage is arbitrary, not zero

Solidity zero-initializes storage; Certora does not assume this.
Rules like

```cvl
// "getter reverts when no version has been registered"
getLatestVersion@withrevert(e);
assert lastReverted;
```

will VIOLATE because Certora explores initial states where the
private `latestVersion` slot holds an arbitrary value.

**Workaround:** make the precondition explicit, OR add a class
invariant tying the relevant private slot to a readable storage that
captures registration history.

For functions whose only "unset" guard is a private slot you cannot
observe from CVL, the rule is deferred unless the contract is changed
to expose the slot, or a ghost invariant is established inductively.
Document the limitation in the spec header.

## C007: Build needs JDK 21 + Gradle 8.5 + kill stale Kotlin daemons

The CertoraProver README says "JDK 19+, `./gradlew assemble`". The
bundled Gradle 7.2 wrapper can only run on JDK 8-16, and the
project's KSP processors are compiled for JDK 19 class files, so the
two are mutually incompatible. CertoraProver CI works because their
own Docker image (`public.ecr.aws/certora/cvt-image:...`) pins the
right combo; the README never mentions that.

**Workaround for native macOS arm64 build:**

1. Install `openjdk@21` via Homebrew.
2. Bump `gradle/wrapper/gradle-wrapper.properties` from `gradle-7.2`
   to `gradle-8.5`. That's the only diff from upstream.
3. Before any rebuild after switching JDKs, **kill the Kotlin compile
   daemon**:

   ```sh
   pkill -f KotlinCompileDaemon
   ```

   The Kotlin daemon has a 2-hour idle timeout and is reused across
   builds keyed by classpath, not by JDK version. A stale JDK 17
   daemon will silently service your JDK 21 build, fail to load
   class-63 jars, and crash with a confusing
   `UnsupportedClassVersionError`.

Full versions used: JDK 21, Gradle 8.5, Z3 4.15.4, CVC5 1.3.4, LLVM
22.1.6, Rust 1.93-nightly, solc 0.8.28.

## C008: Path normalization breaks for nested contracts

Certora's autofinder recompile pass has a path-matching bug: during
its second compile, `c_file` becomes an absolute path under
`.certora_sources/`, but the contracts dict keys remain relative, and
the comparison resolves against the script's CWD (the repo root, not
`.certora_sources`). This works "by accident" for top-level
`contracts/Foo.sol` but reliably breaks for
`contracts/governance/Foo.sol` or `contracts/staking/Foo.sol`.

**Workaround:** add to the conf:

```json
"disable_internal_function_instrumentation": true
```

This skips the autofinder pass entirely. It is safe when all
summaries in the spec are external wildcards (`function _.foo(...)
external => ...`), which is the common case. If you actually need
internal-function summaries on the contract under test, prefer:

```json
"use_relpaths_for_solc_json": true
```

which fixes the underlying path-resolution. The Governor agent used
the `disable_internal_function_instrumentation` path; the
OptimisticSelectorRegistry agent used `use_relpaths_for_solc_json`.

## C009: `optimistic_hashing` is required for `keccak256(string)`

A contract that does

```solidity
string memory version = ...;
bytes32 hash = keccak256(abi.encodePacked(version));
```

makes Certora try to hash a variable-length array. It errors out with

```
Trying to hash a non-constant length array whose length ...
```

**Workaround:** add to the conf:

```json
"optimistic_hashing": true
```

This tells the prover to assume hashes are collision-free on the
variable-length input. Almost always the right setting; it's only
unsafe if your property genuinely depends on the adversary being
able to find a collision.

## C010: `optimistic_loop` + `loop_iter` for dynamic-array loops

Any function with a loop over a dynamic array — e.g. OZ Timelock's
`_execute` walking `targets[]`, OZ Governor's deque-pop in
`_executor()` — needs both:

```json
"optimistic_loop": true,
"loop_iter": 3
```

`optimistic_loop: true` tells the prover that bounded unrolling
captures all reachable behaviors. `loop_iter: N` is the bound. 3 is
fine for most rules; bump if the contract has nested loops or longer
fixed sequences. The Timelock and Governor agents both needed this.

## C011: TIMEOUT does not exit the run cleanly

When a single rule's SMT problem hits its solver budget, Certora
emits

```
Result for ruleName: ruleName: TIMEOUT
```

then proceeds to **hang for many minutes** emitting

```
Ping 8m - Processed 9/10 (90%) rules. 23 tasks complete, 1 pending.
Ping 9m - ...
Ping 10m - ...
```

The CLI process does NOT exit even though all real work is done. The
StakingVault agent burned 5+ minutes per iteration waiting on this.

**Workaround:** wrap `certoraRun.py` in an external `timeout`:

```sh
timeout 600 certoraRun.py path/to/Foo.conf
```

If a rule routinely times out, scope it down (smaller state space,
tighter preconditions) rather than just upping the timeout.

## C012: Non-ASCII in conf strings rejected

The conf parser rejects em-dashes, plus signs, curly quotes, and
other non-ASCII in `msg` and other string fields. The error is
opaque:

```
attribute/flag 'msg': {'—'} not allowed in 'msg'
```

**Workaround:** ASCII only. Use `-` not `—`, `and` not `+`, `"..."`
not `"..."`. This bites every editor that auto-converts hyphens to
em-dashes.

## C013: `emv.jar` slim vs shadow

After `./gradlew assemble`, two jars land in `build/libs/`:

- `emv.jar` — slim, no Main-Class manifest, NOT runnable.
- `emv-0.4-jar-with-dependencies.jar` — the shadowJar with all deps,
  Main-Class = `EntryPointKt`. This is what `java -jar` needs.

`certoraRun.py` invokes `java -jar $CERTORA/emv.jar` literally — it
expects "emv.jar" by name but needs the shadow content.

**Workaround:** symlink. The env.sh setup creates
`$CERTORA/emv.jar -> .../emv-0.4-jar-with-dependencies.jar`. If you
ever rebuild and the symlink breaks (e.g. version bump renames the
shadow jar), re-point it.

Symptom of getting this wrong:

```
CRITICAL: no main manifest attribute, in .../emv.jar
```

## C014: Filename and contract name often differ

In this codebase, `contracts/VersionRegistry.sol` defines a contract
called `ReserveOptimisticGovernanceVersionRegistry`. Certora's
default file-to-contract resolution assumes they match, fails with

```
'verify' argument, ReserveOptimisticGovernanceVersionRegistry,
doesn't match any contract name
```

**Workaround:** use the explicit `file.sol:Contract` syntax in conf:

```json
"files": ["contracts/VersionRegistry.sol:ReserveOptimisticGovernanceVersionRegistry"]
```

Always cheaper to write the explicit form than to depend on the
filename heuristic.

## C015: External NONDET summaries are the strongest abstraction

When verifying a contract that calls into other contracts (e.g. the
governor calling the timelock, or the guardian calling the governor),
the maximally-strong abstraction is

```cvl
function _.method(args) external => NONDET;
```

The leading `_.` is a wildcard: any function with this signature on
any external address gets the summary. `NONDET` means the prover
chooses an arbitrary return value. Any property that holds under
arbitrary downstream behavior is unconditionally sound.

**When NONDET is not enough:** if two reads of the same external
state need to agree (TOCTOU pattern — a snapshot threaded through
multiple checks), NONDET is too free — it lets the prover pick
different answers for each call. Then use a ghost-backed summary:

```cvl
ghost mapping(address => bool) ghostIsOwner;

methods {
    function _.isOwner(address a) external => ghostIsOwner[a] expect bool;
}
```

Now each rule can `require ghostIsOwner[e.msg.sender]` to pin the
auth outcome for the caller under test. The
RewardTokenRegistry, VersionRegistry, and OptimisticSelectorRegistry
agents all used this pattern.

## C016: Worktree-isolated agents may break out

Sub-agents launched with `isolation: worktree` get a clean git
worktree, but their shell environment doesn't constrain them to it.
A common pattern in this push: agent finds its worktree has no
`node_modules`, breaks out via `cd /Users/jmart/git/reserve/.../governor`
to use the parent checkout's `node_modules`, then runs certoraRun
from there.

The downsides: (a) artifacts land in the main repo as untracked
files; (b) `.certora_internal/` cache contention if multiple agents
break out simultaneously; (c) the agent's claimed "in my worktree"
commit may actually be on the main branch.

**Workaround for future runs:** symlink `node_modules` into each
worktree before dispatching, or include the symlink instruction in
the agent prompt. The cleanest fix would be to make `node_modules`
worktree-aware (e.g. a shared symlink committed to the repo pointing
at a sibling install).
