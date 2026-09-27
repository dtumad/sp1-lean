Backend presentation evidence for [PR #104](https://github.com/dtumad/sp1-lean/pull/104), reviewed and locally reproduced at **`698bec03cf75327921a694c55a219d340a77ea47`**. No tracked files, pins, or PR settings were changed. The backend worktree was clean before and after. [All pins and environment details](PINS.md) are included in this package.

Suggested speaker paragraph:

> We took three existing Lean gadgets through Clean's pinned WASM and R1CS backend. For 29 inputs, we compared every original circuit cell against Lean's generated witness and checked the complete R1CS, including the backend's extra signals. We also checked 26 witness mutations: 21 were rejected and five remained valid. One valid example changes the inverse of zero to seven, showing that the circuit relation allows more than the canonical generator output. This is concrete standalone backend conformance over BN254, not a proof of backend correctness, an export of the SP1 ensemble, or coverage of every conditional consumer.

Fresh reproduction completed September 27, 2026, at 21:37:25 UTC. The existing shell checker passed in **12.649 seconds** with `LEAN_NUM_THREADS=2`. Its **actual, unedited output** is [backend-check.log](logs/fresh/backend-check.log); command, timing and exit code 0 are in [its record](logs/fresh/backend-check.command.json):

```text
Build completed successfully (4004 jobs).
Exported 3 unchanged gadget constraint systems to .lake/backend-gadgets.AvZvya/generated
PASS deterministic backend artifact regeneration
PASS is-zero: 2 Lean witness cells, 6 R1CS constraints, 7 total signals
PASS is-zero-word: 11 Lean witness cells, 33 R1CS constraints, 32 total signals
PASS word-range-check: 64 Lean witness cells, 132 R1CS constraints, 133 total signals
PASS 29 generated witnesses and 26 explicit mutations; every original Lean cell compared and full R1CS checked
```

This was a **warm-cache run**: `.lake/packages`, `.lake/build`, the native exporter, and local `node_modules` were already present. The executable hash did not change. “4004 jobs” is Lake's successful target graph, not a claim that all jobs recompiled. No setup, reinstall, dependency update or clean build was performed. `--no-cache` disables Lake's automatic release downloads while still using local build artifacts. The checker freshly regenerated every export file, compared the complete inventory and every byte with the committed artifacts, and reran all external witness checks.

| Gadget | Input cells | Original witness cells | Lean assertions | Full R1CS constraints | Total signals | Cases accepted/rejected | Mutations accepted/rejected |
|---|---:|---:|---:|---:|---:|---:|---:|
| `is-zero` | 1 | 2 | 3 | 6 | 7 | 7/0 | 1/4 |
| `is-zero-word` | 4 | 11 | 17 | 33 | 32 | 10/0 | 4/8 |
| `word-range-check` | 4 | 64 | 68 | 132 | 133 | 3/9 | 0/9 |

Totals: **29 cases (20 accepted, 9 rejected); 26 mutations (5 accepted, 21 rejected)**. The mutation counts include one rejected backend-auxiliary corruption per gadget. All totals are derived from the copied [manifest](artifacts/manifest.json), case files and the existing checker's explicit auxiliary test; see [counts.json](counts.json). Signals include the constant signal at index zero (value one), every original input/witness cell and backend auxiliaries: respectively 3, 16 and 64 auxiliaries. Measured R1CS costs **6/33/132** are costs of these unchanged circuits and this pinned lowering, not optimization gains.

All examples use the **BN254 scalar field**, characteristic `21888242871839275222246405745257275088548364400416034343698204186575808495617`. SP1's pinned deployed base field is **KoalaBear**, characteristic `2130706433`. Field elements in the fixture JSON are exact decimal strings. Cases cover zero/nonzero, field-minus-one/minus-two, scalar `2^64` and `2^128`, each word limb, maximum valid 16-bit limbs, and rejected limbs `65536`, `2^64`, and field-minus-one. The range failures show that low-64-bit witness extraction cannot hide these invalid field inputs.

`IsZeroOperation.circuit` and `IsZeroWordOperation.circuit` are invoked through thin adapters with **gate = 1** and their existing `populateFE` witnesses. This does not test every selector, inactive/padding case or real consumer. `WordRangeCheck.circuit` contributes its existing 64 bit witnesses. Every original assertion is retained; there is no constraint stripping. Exporter rejection tests cover lookup, interaction, native witness closure, `dataGet`, `hintGet`, and an unbound loop index. Their actual backend diagnostics are in [manifest.json](artifacts/manifest.json). These supported standalone programs are not a generic ensemble export or a new Rust operation-faithfulness anchor. There is no new universal backend theorem to quote.

Two retained witnesses make the distinction between a bad witness and valid noncanonical freedom explicit. Both start from the existing checker's zero-input witness, using Clean's actual cell-to-signal map: input `a` is signal 2, inverse is signal 3, result is signal 1.

| Existing mutation | Actual original cells `(a, inverse, result)` | Actual snarkjs verdict | Exit |
|---|---|---|---:|
| `is-zero/zero-corrupt-zero-result` | `(0, 0, 0)` | `WITNESS IS NOT CORRECT`; aborts at constraint 1 | 1 |
| `is-zero/zero-zero-inverse-is-free` | `(0, 7, 1)` | `WITNESS IS CORRECT` | 0 |

The unedited logs are [rejected result](logs/fresh/zero-corrupt-zero-result.log) and [accepted inverse seven](logs/fresh/zero-zero-inverse-is-free.log). Actual binary witnesses and snarkjs-exported full signal arrays are [rejected `.wtns`](witnesses/is-zero/zero-corrupt-zero-result.wtns), [rejected JSON](witnesses/is-zero/zero-corrupt-zero-result.json), [accepted `.wtns`](witnesses/is-zero/zero-zero-inverse-is-free.wtns), and [accepted JSON](witnesses/is-zero/zero-zero-inverse-is-free.json). [representative-verdicts.json](representative-verdicts.json) records exact commands, expected/actual exit codes, original-cell mapping, and all seven signal values. The canonical zero witness is `(0,0,1)`; inverse seven intentionally differs from it while satisfying the same original relation. The Lean assertion evaluator checks expected mutation acceptance before artifact export; the full snarkjs R1CS check independently checks the mutated backend witness.

The shell runner deletes its scratch directory. To retain real witnesses, we reran the **existing Python checker** against byte-identical artifact copies, writing the package's ignored `witnesses/` directory. That fresh second run passed in 9.709 seconds: [log](logs/fresh/retained-witness-check.log), [command record](logs/fresh/retained-witness-check.command.json). Both selected snarkjs checks were then run again directly and their raw output saved. Clean's WASM does not enforce assertions; successful witness calculation alone is never treated as acceptance. The checker requires the explicit witness verdict and exact exit code (0 for accepted, 1 for rejected), and checks the full R1CS including auxiliaries.

Reproduce in a checkout already prepared at the exact revision. These commands reuse installed prerequisites:

```sh
cd /absolute/path/to/sp1-lean-fork
test "$(git rev-parse HEAD)" = 698bec03cf75327921a694c55a219d340a77ea47
LEAN_NUM_THREADS=2 bash scripts/check_backend_gadgets.sh
```

For a fresh environment, setup is explicit: install the toolchain from `lean-toolchain`, prepare the pinned Lake dependencies, activate Node **22.16.0**, and run `npm ci --prefix tools/backend-gadgets`. The runner never installs tools or changes pins; no `circom` executable is required. The complete npm lock is included. The normal native generation command, if independently needed, is `LEAN_NUM_THREADS=2 lake --no-cache build --wfail --iofail backendGadgets`, followed by `.lake/build/bin/backendGadgets /absolute/path/to/ignored-output`; do not overwrite committed artifacts for this reproduction.

With `backend_evidence` set to this unpacked package, the following uses only the included artifacts and existing checker/tool install. It regenerates witnesses in a fresh ignored directory while retaining the packaged originals:

```sh
backend_evidence=/absolute/path/to/presentation-evidence/backend
python3 scripts/check_backend_gadgets.py "$backend_evidence/artifacts"   "$backend_evidence/reproduced-witnesses"   --cli tools/backend-gadgets/node_modules/snarkjs/build/cli.cjs
node tools/backend-gadgets/node_modules/snarkjs/build/cli.cjs wtns check   "$backend_evidence/artifacts/is-zero/circuit.r1cs"   "$backend_evidence/witnesses/is-zero/zero-corrupt-zero-result.wtns"
# Expected exit 1 and WITNESS IS NOT CORRECT.
node tools/backend-gadgets/node_modules/snarkjs/build/cli.cjs wtns check   "$backend_evidence/artifacts/is-zero/circuit.r1cs"   "$backend_evidence/witnesses/is-zero/zero-zero-inverse-is-free.wtns"
# Expected exit 0 and WITNESS IS CORRECT.
```

Freshly queried GitHub evidence is included under [ci/](ci/), with query times and commands in [capture.json](ci/capture.json). The successful [run 36349817969](https://github.com/dtumad/sp1-lean/actions/runs/36349817969) completed at **2026-09-27 21:14:03 UTC**; guards, build, handoff, and build-full all passed. The [full-build job](https://github.com/dtumad/sp1-lean/actions/runs/36349817969/job/108706743599) includes the backend checker. This is **successful PR CI associated with the exact head**, not a direct checkout of that head: the captured [full raw log](ci/successful-build-full.log) proves checkout of merge commit `6d6a6238dc80c7007bff7c498cd64072b3b87b8c`, merging head `698bec03cf75327921a694c55a219d340a77ea47` into then-base `9e383aaa85aec0eaf8ed0856f243ed8806520aef`. [Checkout/backend excerpts](ci/checkout-and-backend-excerpt.log) preserve the original log lines. This does not imply testing against later `main` commits.

The earlier [run 36349817287](https://github.com/dtumad/sp1-lean/actions/runs/36349817287), associated with the same head, was **cancelled**: guards passed, build was cancelled, and handoff/build-full were skipped. It was superseded by the successful run above. Cancelled/skipped checks are not reported as passed. The PR remained open with the same head when queried; see [PR snapshot](ci/pr-104.json), [successful run](ci/successful-run.json), and [superseded run](ci/superseded-run.json).

Historical local validation from implementation is copied under [logs/historical/](logs/historical/), with original file mtimes and hashes in [its inventory](logs/historical/inventory.json). These logs record the earlier strict full build, core/full lint, audit, deterministic witness export and Rust differential (857 rows), plus backend runs and the existing npm advisory notice. `backend-lake-test.log` is empty; success was reported at implementation time but cannot be inferred from that empty file alone. These historical files predate the commit and do not embed a revision/exit-code attestation, so they are supporting records rather than fresh exact-head reruns. Only the backend reproductions and two representative verdicts above were rerun for this package. CI independently records the broader gates on its specified merge commit.

The package contains copied native exporter/checker source, all deterministic gadget artifacts, all 55 original/mutated witnesses, dependency/tool pin files, current CI metadata/logs, and actual local logs. No Lean/npm tool installation or full repository checkout is bundled. [SHA256SUMS](SHA256SUMS) covers the delivered evidence files. The presentation agent can refresh its source pin coherently from this evidence; this package does not change the frozen talk narration.
