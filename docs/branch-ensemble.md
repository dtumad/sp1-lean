# A compiler-derived branch in the complete local assembly

The [joined example](../SP1CleanTest/Alignment/Audit/BranchEnsembleRoundTrip.lean) extends
the existing official Sail/compiler/local-row example through the actual
`SP1Clean.Soundness.HostFinalMemory.ensemble`. It uses the same `BEQ x1,x2,+4092`,
zero operands, PC 65536→69628, and clock 1→9. The instruction row and its hint come
from the successful deterministic compiler result.

`BranchEnsemble.accepted` proves raw constraints and every registered channel balance
for the concrete physical witness. `BranchEnsemble.joined` combines that acceptance
with the official Sail transition, canonical projection, compiler result, and the
source/target realization proofs. The target snapshot authenticates all GPRs and RAM;
the separate Sail transition retains the full normally retiring interpreter state.
This is one concrete construction, not a general compiler-totality or capstone theorem.

The [fixture](../SP1CleanTest/Alignment/Support/BranchEnsembleFixture.lean) derives
Program and Memory demand from the actual compiled row. Ordered source/final providers,
target validators, terminal rows, and Byte/Range providers are real installed components.
The public verifier contributes to provider demand and is checked with every other row.
The accepted fixture retains all 89 installed tables, with 57 physical rows across 14
nonempty tables plus the public verifier row. Its 257 registry entries identify 22 distinct
channels. No RAM access is invented for this register-only branch.

The reusable [finite witness checker](../ToClean/Air/EnsembleCheck.lean) proves that its
Boolean result is equivalent to Clean's raw constraints and channel-balance predicates.
Its authenticated finite lookup inventory covers even installed components with no rows.
It counts every physical interaction occurrence, including duplicates and multiplicity
zero, against the field characteristic. The assembly registers some identical channels
more than once. The [export inventory](../SP1CleanTest/Alignment/Support/BranchEnsembleInventory.lean)
uses a unique registry with proved full `RawChannel` membership equivalence, then
transports acceptance back to the original assembly. This changes no physical ledger.

## Reproduce and inspect

From a checkout with the immutable dependencies and toolchain already prepared:

```sh
scripts/check_branch_ensemble.sh
```

The runner builds its test module with warning/info failures enabled, evaluates actual
rows and ledgers, and writes `.lake/build/branch-ensemble/`:

- `results.json`: actual table/row counts, public endpoints, and acceptance outcomes;
- `axioms.log`: literal public theorem types and compiled axiom reports;
- `commands.log`, `build.log`, and `runner.stdout.log`: original command output;
- `provenance.json`: source revision/tree, dirty state, dependency pins, cache conditions,
  and CI checkout/run identifiers where available.

For a fresh clone, first install the toolchain named by `lean-toolchain` and run
`lake exe cache get`, as described in [the existing walkthrough](talk-examples.md).
The runner itself installs nothing and refuses missing, moved, or locally edited
dependency checkouts. Available project oleans are reused; this is not a cold-build
benchmark. A tested dirty checkout is identified explicitly in its provenance.

The regression cases include the original branch, a wrong public next PC, missing and
duplicated authentication rows, a changed untouched target register, an empty identity
segment, and malformed seed indices/lengths. Expectations are compared with actual checker
results. Exceptions, process failures, incomplete JSON, and missing theorem output fail
the runner; none count as successful rejection. The driver evaluates the compiler and
physical witness. It does not execute the noncomputable full Sail state.

The generic correctness theorems live in the production library. Concrete regression
proofs additionally use the test-only evaluator/compiler trust boundary disclosed by
[the trust policy](trust-policy.md); the artifact reports the actual dependencies.
No new trust-policy exception is introduced.

On a PR carrying `ci:alignment`, the `build-full` job publishes the directory as
`branch-ensemble-<checkout SHA>-<run ID>-<attempt>`. PR CI may check a merge commit;
the recorded checkout SHA and PR head are kept distinct. The presentation workspace
should cite the tested revision and CI artifact, and own any slide re-pinning.

## Speaker paragraph

“This branch starts with the official Sail step and passes its canonical access view
through the real event compiler. We now build the surrounding authentication and
boundary rows too. A proved checker establishes raw acceptance of that concrete
complete local assembly, and mutations to the public endpoint or authentication
inventory reject. It closes this example's construction gap; the general mixed-execution
compiler and endpoint work remains a separate campaign.”
