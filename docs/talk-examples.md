# Run an ADD witness and its rejecting mutations

This walkthrough executes actual Clean row programs, fixed lookups, and complete interaction
ledgers for `SP1Clean.Soundness.HostFinalMemory.ensemble`. It is executable fixture evidence;
it does not close the full SP1 soundness/completeness capstone.

## Run

From a prepared checkout:

```sh
scripts/run_talk_examples.sh
scripts/run_talk_examples.sh --json
```

The script also works by absolute path from another directory. It builds its test module through
Lake before running and writes build diagnostics to stderr. The JSON contains the git revision,
a dirty-working-tree flag, assembly identity, fixture-derived source/target projection, and each
case's expected and actual acceptance. It contains no timestamps, so unchanged successive runs
produce identical JSON. A mismatch, incomplete output, or build failure exits nonzero.

For a fresh checkout, install Git, Python 3, and elan first, then explicitly prepare dependencies:

```sh
git clone https://github.com/dtumad/sp1-lean.git
cd sp1-lean
# Check out the reviewed revision containing this walkthrough before preparing dependencies.
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
scripts/run_talk_examples.sh --json
```

The setup command may download the immutable dependencies in `lake-manifest.json` and their
available caches. Do not run bare `lake update`. The runner itself installs no toolchains,
updates no dependencies, and disables Lake cache downloads. It checks that every dependency is
present at its resolved revision without tracked source edits, and that direct pins agree with
the manifest. Missing prerequisites fail with setup guidance before building.

The first run may need a substantial alignment build, including the generated Sail model and
the umbrella imported by the existing ADD audit anchor. A warm run is not a cold reproduction;
report whether project artifacts and dependency caches were present when quoting timings.

## Read the witness and change it

The fixture runs **ADD x1,x2,x3** with **x2=100**, **x3=23**, and **x1=123** at
**PC 65536→65540**, **clock 9→17**. These displayed fields come from the shared input definitions.
It starts from an arbitrary local source rather than a boot state. The host queue is empty;
the installed commitment banks still require their terminal rows.

| Case | Actual acceptance |
|---|---|
| `active-add` | true |
| `missing-ram-validator` | false |
| `duplicate-ram-validator` | false |
| `wrong-final-record-clock` | false |
| `missing-unchanged-register-validators` | false |
| `changed-untouched-x31` | false |
| `changed-untouched-ram` | false |
| `missing-bank-terminal` | false |
| `empty-identity` | true |

Start at [the shared complete-memory fixture](../SP1CleanTest/Alignment/Support/HostFinalMemoryFixture.lean).
`rows` combines the ADD core rows, bank terminals, and outgoing register/RAM checks. `check`
evaluates the verifier and every physical row, constructs actual Byte/Range providers, and tests
constraints, channel membership, the count bound, and full-message balance.

For two slide-sized mutations, inspect `missing-ram-validator` and `changed-untouched-x31` in
`results`. The first drops table 88 while retaining its final RAM record; its receipt no longer
balances. The second changes only the supplied target's untouched x31; the complete change
inventory now demands authentication that the physical witness cannot supply. Both are checked
by the same evaluator as the accepted witness. Editing a case's expected Boolean and rerunning
must fail; it does not change the actual acceptance computation.

The original regression declarations remain in
[HostFinalMemory](../SP1CleanTest/Alignment/Core/HostFinalMemory.lean), and the shared evaluator
and local ADD rows live in [LocalCoreFixture](../SP1CleanTest/Alignment/Support/LocalCoreFixture.lean).
Existing extensions retain the `LocalCore.addFixture`, `evaluateComponent`, and `provideBytes`
interfaces. To check repeatability, invocation from another directory, and an intentionally
inverted expectation, run:

```sh
scripts/check_talk_examples.sh
```

## Follow the universal statements

[HostFinalMemory.source_checkFinal](../SP1Clean/Soundness/HostFinalMemorySoundness.lean)
quantifies over an arbitrary witness of the concrete six-call assembly. From its constraints
and balanced channels it derives the complete finite source-to-target Memory comparison,
including locations outside the final inventory. The assembly fixes the source, supplied
target, host boundaries, and installed handlers. The comparison consumes the actual final
records; its statement does not by itself assert an entire Sail endpoint.

[HostHintReadCPU.source_execution](../SP1Clean/Soundness/HostHintReadExecutionPath.lean)
derives a genuine `ExecutionPath` for its installed host assembly from a valid program image,
witness constraints, and balanced channels. Its conclusions include exhaustive event coverage,
write permissions, the final clock/PC, and final-frontier values. Read its exact assembly and
premises before combining it with an endpoint claim. The [roadmap](roadmap.md) records remaining
capstone obligations.

State balance alone is weaker than an exhaustive execution. The separate
[StateBalanceExample](../SP1Clean/Soundness/Examples/StateBalance.lean) proves endpoint balance
for edges `0→1, 1→2, 10→11, 11→10`, but proves that no strictly increasing natural rank covers
the cycle and no exhaustive trail goes from 0 to 2. This is an abstract graph counterexample
to State balance alone, not a full SP1 AIR exploit.

The universal production statements are Lean proofs subject to the repository's
[compiled-library trust policy](trust-policy.md). The executable fixture checks additionally
use Lean's evaluator/compiler; existing regression theorems use the disclosed test-only
`native_decide` boundary. The namespaced test `main` is invoked by a small `#eval` driver because
the generated Sail library already owns root `main`. The wrapper checks the entire JSON output
as well as process status, including the known Lean stack-overflow/zero-exit failure mode.
Neither a printed `true` nor the JSON is a proof certificate.
