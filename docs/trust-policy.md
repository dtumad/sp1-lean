# Lean trust policy

The trust check asks whether the built libraries depend on permitted axioms. It does not judge
whether a theorem states the intended claim. The separate capstone contract, model review,
whole-chip faithfulness and extraction-provenance checks retain that responsibility.

## Policy

[`scripts/trust_policy.json`](../scripts/trust_policy.json) is the reviewed policy. It permits:

- Lean's logical baseline: `propext`, `Classical.choice`, and `Quot.sound`.
- The named external operations in the pinned generated Sail interface. These are model inputs,
  not proved implementations of platform operations. An operation can appear through the type
  of an interpreter relation without being reached by an execution in the supported profile.
- The named existing `bv_decide` proof owners, including two from pinned Clean. Their certificate
  checkers run as native code, so these proofs also trust compiled computation. Only generated
  axiom counter suffixes are normalized; a new proof owner requires a policy review.
- In the test scope, `native_decide` and `bv_decide` computation. The production scan separately
  rejects a test-native dependency entering a production declaration.

`sorryAx` and unknown axioms fail in both scopes. The main scope rejects general native decision
proofs. There is no automatic policy-update command. Reducing the existing native trust or
replacing Sail external operations with implementations is separate proof/model work.

## Check and reports

After building current oleans:

```sh
lake build --wfail --iofail SP1Clean ToClean ToMathlib ToPolyFun SP1CleanTest
python3 scripts/check_trust.py
lake env python3 scripts/test_trust_integration.py
scripts/run_audit.sh
```

`--scope main` and `--scope test` select one library scope. `--validate-policy-only` checks the
policy without Lean or dependency checkouts, for the lightweight CI job. Reports default to
`.lake/build/trust/`; `--report-dir` selects another directory. They record the actual revision,
whether tracked files differ, toolchain, dependency pins, policy digest, module inventory,
declarations and classified dependencies. Reports are diagnostics, not trusted proof objects.
CI uploads them on success or failure. Missing modules, scanner failures, malformed reports,
empty declaration sets and incomplete module coverage fail rather than reuse an old report.

The checker invokes the scanner at the existing immutable PolyFun pin, checking the scanner
source against that revision before use. It follows declaration types and bodies transitively,
including private declarations and mutual families. Main ownership comes from the four source
libraries' modules, independently of their Lean namespaces. Test modules are discovered from
the source tree and imported individually. The root-index guard and the scanner's module count
check completeness; no per-theorem registration or expected declaration count is maintained.

Compiled-environment inspection does not cover anonymous examples or unused field defaults
before elaboration at a use site. Source-level admission and kernel-bypass guards remain
complementary. This scanner inspects built environments; it is not an independent kernel
implementation and does not make stale oleans current. Build before checking.

## Audit workflow

`scripts/run_audit.sh` runs the policy check alongside the pin, source and semantic-contract
gates. Its `--main-only` and `--test-only` flags retain their library scope. Normal runs never
rewrite tracked inputs. There are no census snapshots, declaration-count synchronizations, or
per-theorem registration steps. The retired `--update` flag fails with a migration message;
trust exceptions are explicit policy edits, not approval of whatever the current build uses.

The main/test split is about proof dependencies, not namespace spelling. Moving an ordinary
helper, adding a theorem, or changing its use of standard logical axioms needs no policy update.
Choose public/private visibility for API and implementation needs, independently of this check.

Fixtures live outside all released libraries. They exercise private and transitive admissions,
axioms in types, mutual dependencies, actual native computations, misleading names, missing
modules and new ordinary declarations needing no registration.
