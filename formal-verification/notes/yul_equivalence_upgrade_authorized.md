# Yul-equivalence sketch: `upgrade_authorized`

This memo bridges the abstract `VersionRegistry.upgrade_authorized`
predicate (proved correct in
[`proofs/Integration_upgrade_authorization.v`](../rocq/proofs/Integration_upgrade_authorization.v))
to the Yul body of `StakingVault._authorizeUpgrade` that the
compiler actually emits.

**Status: bridge sketch only.** The full mechanization — a closed
proof of "the Yul function returns success iff `upgrade_authorized`
holds" — is future work. This memo establishes the artifact (IR has
been generated, Yul function identified, decomposition documented)
and scopes the remaining proof obligations.

---

## What the abstract proof says

`Integration_upgrade_authorization.v` carries three audit-narrative
theorems against the abstract `upgrade_authorized` predicate:

  * `register_then_authorize_self` — after registering version `v`
    with impl `svi`, `upgrade_authorized(hash v, svi) = true`.
  * `register_two_then_authorize_rejects_old` — registering `v2`
    after `v1` makes `upgrade_authorized(hash v1, _) = false` for
    any impl.
  * `register_deprecate_then_authorize_rejects` — deprecating the
    just-registered `v` makes `upgrade_authorized(hash v, _) =
    false` for any impl.

These pin down the "only latest && !deprecated" gate on the
abstract predicate's domain. They say *nothing* about the Yul
bytecode the Solidity compiler emits.

## What the Yul actually does

We ran the rocq-of-solidity toolchain over `StakingVault.sol` to
emit the IR:

```
bash formal-verification/scripts/solc-rocq --ir-rocq \
     contracts/staking/StakingVault.sol > /tmp/sv-ir.rocq
```

The result is 107,364 lines of generated IR. The relevant chunk
splits into three Yul functions, each `Code.Function.make`d in the
deployed section:

### `fun_authorizeUpgrade(stakingVaultImpl)`

A one-line dispatcher that calls the modifier:

```
modifier_onlyRole_1517(stakingVaultImpl)
```

This is the compiler's standard handling of the `onlyRole(...)`
modifier on the Solidity declaration:

```solidity
function _authorizeUpgrade(address stakingVaultImpl)
    internal view override onlyRole(DEFAULT_ADMIN_ROLE) { ... }
```

The modifier expansion happens at IR level; the function body in
the Solidity source becomes `fun_authorizeUpgrade_inner`.

### `modifier_onlyRole_1517(stakingVaultImpl)`

Three Yul steps in order:

  1. Load the `DEFAULT_ADMIN_ROLE` constant.
  2. Call `fun__checkRole(role)` — the OZ AccessControl role check.
     If the caller lacks the role, this reverts.
  3. Call `fun_authorizeUpgrade_inner(stakingVaultImpl)` — the
     actual version-registry checks.

The modifier is what enforces "only admin can authorize an
upgrade." That's a role-auth concern, currently tracked under task
#123 (role-auth threading across domains). For *this* memo, we
assume the role check passes and focus on the inner function.

### `fun_authorizeUpgrade_inner(stakingVaultImpl)`

The Solidity equivalent (from
[`StakingVault.sol:530-541`](../../contracts/staking/StakingVault.sol)):

```solidity
function _authorizeUpgrade(address stakingVaultImpl)
    internal view override onlyRole(DEFAULT_ADMIN_ROLE) {
    bytes32 versionHash = keccak256(abi.encodePacked(
        Versioned(stakingVaultImpl).version()
    ));

    (bytes32 latestVersionHash, , , bool deprecated) =
        versionRegistry.getLatestVersion();
    require(!deprecated, Vault__VersionDeprecated(versionHash));
    require(versionHash == latestVersionHash,
        Vault__NotLatestStakingVault(stakingVaultImpl));

    (address latestStakingVaultImpl, , ) =
        versionRegistry.getImplementationsForVersion(versionHash);
    require(latestStakingVaultImpl == stakingVaultImpl,
        Vault__NotLatestStakingVault(stakingVaultImpl));
}
```

Translates at the Yul level into:

  1. **External call to `stakingVaultImpl.version()`**, then
     `keccak256` over the abi-encoded result. The IR emits this as
     a sequence of `staticcall`, memory copies, `abi_encode_string`,
     and `keccak256` opcodes.
  2. **External call to `versionRegistry.getLatestVersion()`**,
     decoding the 4-tuple `(bytes32, address, uint256, bool)`.
  3. **`require(!deprecated)`** — `iszero` on the deprecated bool,
     conditional revert with `Vault__VersionDeprecated`.
  4. **`require(versionHash == latestVersionHash)`** — `eq` opcode
     plus conditional revert.
  5. **External call to `versionRegistry.getImplementationsForVersion(versionHash)`**,
     decoding the triple `(address, address, address)`.
  6. **`require(latestStakingVaultImpl == stakingVaultImpl)`** — `eq`
     plus conditional revert.

In abstract form, the Yul body computes:

```
yul_authorizeUpgrade_inner(svi) ≡
  let h = keccak256(version(svi))
  let (lh, _, _, dep) = registry.getLatestVersion()
  assert(!dep)
  assert(h == lh)
  let (lsvi, _, _) = registry.getImplementationsForVersion(h)
  assert(lsvi == svi)
```

This is observably equivalent to the abstract predicate:

```
upgrade_authorized(s, vh, svi) :=
  match getLatestVersion(s) with
  | Success lv =>
      negb lv.deprecated
        && (lv.latestVersionHash =? vh)
        && (let (lsvi, _, _) := getImplementationsForVersion(s, vh)
            in lsvi =? svi)
  | _ => false
  end
```

when one identifies `vh ≡ keccak256(version(svi))`.

---

## What a full equivalence proof would require

Closing the bridge from "the Yul body reverts iff the abstract
predicate returns false" requires:

  1. **Yul execution semantics.** The rocq-of-solidity corpus
     provides a step-relation over Yul state (memory, storage, call
     stack, returndata). A Yul-equivalence proof reasons about
     state evolution under that semantics.
  2. **External-call oracles.** Both `versionRegistry.getLatestVersion()`
     and `versionRegistry.getImplementationsForVersion(_)` are
     `staticcall`s to a foreign contract. The proof treats them as
     oracles whose output matches the abstract `getLatestVersion`
     and `getImplementationsForVersion` operations — that
     assumption is the price of not also Yul-mechanizing the
     `VersionRegistry` contract.
  3. **Keccak oracle.** The `keccak256` opcode over
     `abi_encode_string(version(svi))` is treated as the
     `version_hash` function from the abstract simulation, which is
     declared injective via `version_hash_injective`. The injection
     assumption is standard for collision-resistant hashes.
  4. **Equivalence theorem.** A statement of the form:

     ```
     forall s svi rev_state,
       run_yul fun_authorizeUpgrade_inner s svi succeeds
         <-> upgrade_authorized rev_state
               (version_hash (version svi)) svi = true
     ```

     Bridging the Yul state `s` to the abstract `rev_state` is the
     core of the proof — it requires modeling how storage reads of
     the VersionRegistry implementation correspond to abstract
     reads.

This is a substantial undertaking — comparable in scope to one of
the existing per-domain simulation files. The rocq-of-solidity
project's documentation suggests this kind of proof typically
spans hundreds of lines once the Yul step-relation lemmas are in
place.

---

## What stays open

The IR has been generated and surveyed. The Yul function is
identified and its operational structure documented. A future
session can pick up by:

  1. Importing the rocq-of-solidity Yul-execution library into
     this project.
  2. Defining the storage-slot mapping for the
     `ReserveOptimisticGovernanceVersionRegistry` contract.
  3. Writing the step-by-step bridge proof.

The CAS-side witness in
[`cas/version_registry/registry_history.gp`](../cas/version_registry/registry_history.gp)
already exercises the abstract predicate on real input ranges,
giving differential confidence that the abstract predicate
captures the intended semantics. The remaining gap is purely
"abstract predicate ↔ emitted Yul" — not "abstract predicate ↔
contract author's intent."
