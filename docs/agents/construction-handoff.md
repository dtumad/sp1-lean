# Canonical Clean construction migration

The construction infrastructure is split into reviewable fork changes. The SP1 migration uses
Clean's canonical data-aware witness interpreter and row/table/ensemble builders, removing the
local `AgreesBelowWithData`, `WitnessGenerationData`, `TableBuild`, and `EnsembleBuild` copies.
The selected scope is explicit construction from semantic row inputs and fixed prover data.
It does not close the mixed host-call capstone or certify the demand-driven scheduler.

## Review stack

| Change | Review | Base / toolchain |
|---|---|---|
| Canonical agreement, data-aware list/array generator, row/table construction | [Clean fork #1](https://github.com/dtumad/clean/pull/1) | upstream `fba2a29f`, Lean 4.33.1 |
| Typed explicit ensemble builder and receipt/Boolean example | [Clean fork #2](https://github.com/dtumad/clean/pull/2) | fork #1, Lean 4.33.1 |
| Scheduler row-evaluator adapter | [Clean fork #3](https://github.com/dtumad/clean/pull/3) | upstream #446 `89e9abec`, Lean 4.32.2 |
| SP1 consumer migration | this draft branch | fork main `c2868590`, Lean 4.33.1 |

The immutable Clean dependency is `f2d0c2ac0499a428f98172eaad94420714e8aed6`, reachable from
`dtumad/clean` branch `codex/construction-core`. No other dependency or toolchain changes.
The original additive pilot remains at `9414b02f`; presentation and compiler campaigns are
independent of this migration.

## Durable API

- `ProverEnvironment.AgreesBelow` includes cell agreement below the offset, equal data, and equal
  hints. The canonical `ComputableWitnesses` obligations now permit honest data/hint reads.
- Canonical list/array generator functions take optional `(data:=data)`; existing calls retain
  their empty-data behavior. Their equivalence and honesty theorems share the same environment.
- `Component.buildRow`, `Table.build`, and `Table.buildHinted` preserve physical layouts and prove
  raw checks from circuit completeness, computability, and semantic prover premises.
- `Ensemble.RowInputs` indexes semantic inputs and row-local hints by registered component.
  `Ensemble.build` constructs the tables with shared data; `build_constraints` includes the
  public verifier and `build_interactions` describes the complete physical ledger.
- `FlatOperation.witgen_witnessOperationsOnly` proves that filtering non-witness operations
  preserves generated cells. It does not remove the circuit's checks or prove balance.

The Clean example `Examples.Construction.buildReads_statement` constructs an accepted ensemble
from two semantic memory reads and Boolean row hints. Its proof derives the actual verifier
pulls and reader pushes and proves the interaction-count bound. The concrete fixture discharges
those semantic premises in the kernel. Missing, duplicate, or corrupted receipts, wrong public
values, and non-Boolean hints have executable regressions. Alternative Boolean witnesses remain
permitted by the checked semantic relation.

## Validation and reproduction

In the Clean fork, run `bash scripts/check-construction-pilot.sh` after installing the pinned
backend tools documented in `doc/construction-pilot.md`. It builds Clean and all CleanTests,
requires backend tests rather than allowing skips, runs 42 construction regressions and four
exportability checks, audits 30 theorem axiom reports, checks the production import closure,
and runs the style gate. Only the ten unchanged upstream tactic-smoke-test `sorry` warnings
are allowed in CleanTests; the new code builds warning-free. All audited construction theorems
use only `propext`, `Classical.choice`, and `Quot.sound`. Caches may be reused.

The SP1 migration passed:

- `lake build --wfail --iofail SP1Clean ToClean ToMathlib ToPolyFun backendGadgets` and the
  strict full `SP1CleanTest` build, with zero warnings/info diagnostics; all four root linters.
- Main and test trust audits: 38,644 declarations / 1,043 modules and 1,713 declarations /
  73 modules respectively, with zero forbidden dependencies; adversarial compiled trust fixtures.
- Fresh witness/testdata regeneration, byte-identical across all 25 chips. The generation-time
  gate recomputed native rows against committed SP1 dumps. The Rust interpreter independently
  reproduced all 857 fixture rows and checked the anchored extracted constraints.
- Byte-identical whole-ensemble export and backend gadget constraint payloads. Backend conformance
  checked 29 generated witnesses and 26 mutations; only the manifest's Clean revision changed.
- Pin, root-index, layering, source/trust guards, and all 32 Python guard tests.

The five physical-provider projection proofs now name `EnsembleWitness.ofTables_tables`
explicitly because Clean's new normalization rules live in `circuit_norm`, not global `simp`.
No native chip circuit, extracted oracle, semantic contract, or faithfulness anchor was changed.
Build logs and portable patches stay in ignored local artifacts; all three Clean fork PRs have
passed their GitHub build and Plonky3 backend jobs.

## Publication boundary

The user authorized fork PRs and portable upstream-ready patches. No upstream PR or maintainer
message is authorized by that choice. This migration remains draft until the canonical changes
have the upstream PR coverage required by `clean-upstream.md`; successful fork validation alone
is not that merge gate. Preserve the branch containing the immutable pin and return to an
upstream pin when the canonical changes are accepted.

The scheduler adapter belongs on #446's own Lean 4.32.2 stack. Its proof obligation is equality
of the private evaluator with the canonical generator, including witness-operation filtering.
`completeRow` still uses empty hints; `generate` initially fixes data before padding/demand while
the final witness derives data from final tables. Final-data agreement, scheduler validity,
termination, and successful-generation completeness remain separate obligations.

The isolated scheduler adapter passed its strict full Clean build, new interpreter regressions,
and unchanged Fibonacci generation tests on Lean 4.32.2. Its two equality theorems and canonical
honesty report only the standard logical axioms. Its dependency manifest is unchanged.
