# Certora local-prover spike

A working Certora Prover install built from source — runs entirely on
this machine, no cloud account needed. Lives at
`~/git/reserve/formal-verification/CertoraProver/`.

## Quick run

```sh
source ~/git/reserve/_tools/certora/env.sh
cd formal-verification/certora/spike
certoraRun.py Vault.conf
```

## What's in the spike

`spike/Vault.sol` — a tiny single-asset escrow vault with `deposit`,
`withdraw`, and a deliberately broken `withdrawBuggy` that forgets to
decrement the user's balance.

`spike/Vault.spec` — five CVL rules:
- `depositIncreasesBalance` — sender balance + totalDeposited both
  increase by msg.value.
- `withdrawDecreasesBalance` — symmetric on the safe path.
- `totalDepositedEqualsBalance_safe` — single-user invariant
  `balances[sender] == totalDeposited` preserved by deposit/withdraw.
- `totalDepositedEqualsBalance_buggy` — same invariant routed through
  `withdrawBuggy`. Expected to fail; proves the prover catches bugs.
- `envfreeFuncsStaticCheck` — implicit, asserts the envfree methods
  declared in `methods{}` really are envfree.

## What the spike proves

Four `VERIFIED`, one `VIOLATED`:

```
depositIncreasesBalance              status=VERIFIED
withdrawDecreasesBalance             status=VERIFIED
totalDepositedEqualsBalance_safe     status=VERIFIED  (under deposit, withdraw)
envfreeFuncsStaticCheck              status=VERIFIED
totalDepositedEqualsBalance_buggy    status=VIOLATED  (expected)
```

`VIOLATED` on the buggy variant means the SMT solver constructed an
execution that breaks the invariant. That's what we want: the prover is
not rubber-stamping; it actually catches the planted bug.

## Toolchain layout

```
~/git/reserve/
├── _tools/certora/
│   ├── env.sh                 # source me to activate the env
│   ├── bin/                   # cvc5, solc8.28, solc -> solc8.28
│   ├── solc/                  # versioned solc downloads
│   └── out/                   # $CERTORA — emv.jar, tac_optimizer, copied scripts
└── formal-verification/
    └── CertoraProver/         # cloned + built source
        ├── build/libs/        # emv.jar (-> shadow jar w/ deps)
        ├── fried-egg/         # Rust subproject -> tac_optimizer
        ├── scripts/           # certoraRun.py + sibling python packages
        └── .venv/             # python deps (activated by env.sh)
```

## Build reproducibility

The CertoraProver source assumes a Certora-published Docker image
(`public.ecr.aws/certora/cvt-image:...`). To build natively on macOS
arm64, the wrapper Gradle 7.2 had to be bumped to 8.5 (in
`gradle/wrapper/gradle-wrapper.properties`) so it can run on JDK 21.
That single edit is the only diff from upstream.

Versions used in this install:
- Gradle 8.5
- JDK 21 (Homebrew openjdk@21)
- Kotlin 1.9.20 (declared in gradle.properties)
- Z3 4.15.4 (Homebrew z3)
- CVC5 1.3.4 (downloaded macOS-arm64-static from cvc5/cvc5 releases)
- LLVM 22.1.6 (Homebrew llvm; for llvm-symbolizer / llvm-dwarfdump)
- Rust 1.93-nightly (cargo + rustfilt via cargo install)
- Graphviz 15 (Homebrew graphviz; for tac-report rendering)
- solc 0.8.28 (matches governor pragma)

## Watch out

- **Stale Kotlin daemon.** The Kotlin compile daemon has a 2-hour idle
  timeout and gets reused across Gradle invocations. If you change JDK
  versions and the build mysteriously fails with
  `UnsupportedClassVersionError`, run `pkill -f KotlinCompileDaemon`.

- **`emv.jar` vs `emv-0.4-jar-with-dependencies.jar`.** The slim
  `emv.jar` has no Main-Class manifest entry. The runnable one is the
  shadow jar. The env.sh setup symlinks `emv.jar` -> the shadow jar.

- **Em-dashes in `msg` field.** The conf parser rejects non-ASCII in
  string fields. ASCII only.

- **Cloud vs local.** `is_local()` in `Shared/certoraUtils.py` returns
  true iff `$CERTORA/emv.jar` exists and the conf doesn't pass
  `server`. Don't add a `server` field unless you want a cloud run.
