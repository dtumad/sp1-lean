# ADD and complete-counter evidence — PR #100

Exact source: [`80092c9a0a2aea3db9db3066fba51018b095e628`](https://github.com/dtumad/sp1-lean/tree/80092c9a0a2aea3db9db3066fba51018b095e628), [PR #100](https://github.com/dtumad/sp1-lean/pull/100).

The source tree was clean before and after this fresh reproduction. The existing pinned dependency checkouts, dependency artifacts and project artifacts were already present. This is a **warm exact-revision reproduction**, not a clean-clone or cold-build measurement. No dependency installation, regeneration or revision update was needed.

[Reproduction metadata](reproduction.json) records actual commands, exit codes, timings, installed Lean and source status. [The full dependency manifest](lake-manifest.json) records every resolved immutable pin. Lean is `leanprover/lean4:v4.33.1`; Clean is `fba2a29f5e36420d797c1de118ac9f11f23b819e`. The ADD wrapper verified every dependency revision and rejected tracked dependency edits before running.

## Reproduce

In a checkout of the exact source above, prepare the pinned toolchain and dependencies using the repository's [setup instructions](https://github.com/dtumad/sp1-lean/blob/80092c9a0a2aea3db9db3066fba51018b095e628/docs/talk-examples.md), then run:

```sh
LEAN_NUM_THREADS=2 scripts/run_talk_examples.sh --json
LEAN_NUM_THREADS=2 lake build --wfail --iofail SP1CleanTest.Alignment.Examples.Counter
lake env lean scripts/counterExample.lean
```

For the literal signatures/axioms below, run `lake env lean /absolute/path/to/this/bundle/examples/declarations.lean` from the same prepared checkout. Build before using `lake env lean`; it does not rebuild dependencies. The copied probe is an inspection command, outside the production library.

## Actual ADD output

The checker uses `SP1Clean.Soundness.HostFinalMemory.ensemble`, the actual **89-table** complete-Memory fixture. It checks the row operations and full interaction ledger. Source values are x2=100 and x3=23; the target has x1=123, PC 65536→65540 and clock 9→17. This fixture is distinct from the retained 55-table soundness theorem.

| Case | Expected | Actual |
|---|---|---|
| active-add | accepted | accepted |
| missing-ram-validator | rejected | rejected |
| duplicate-ram-validator | rejected | rejected |
| wrong-final-record-clock | rejected | rejected |
| missing-unchanged-register-validators | rejected | rejected |
| changed-untouched-x31 | rejected | rejected |
| changed-untouched-ram | rejected | rejected |
| missing-bank-terminal | rejected | rejected |
| empty-identity | accepted | accepted |

Unedited stdout from `scripts/run_talk_examples.sh --json`:

```json
{"assembly":"SP1Clean.Soundness.HostFinalMemory.ensemble","cases":[{"actual":true,"expected":true,"id":"active-add"},{"actual":false,"expected":false,"id":"missing-ram-validator"},{"actual":false,"expected":false,"id":"duplicate-ram-validator"},{"actual":false,"expected":false,"id":"wrong-final-record-clock"},{"actual":false,"expected":false,"id":"missing-unchanged-register-validators"},{"actual":false,"expected":false,"id":"changed-untouched-x31"},{"actual":false,"expected":false,"id":"changed-untouched-ram"},{"actual":false,"expected":false,"id":"missing-bank-terminal"},{"actual":true,"expected":true,"id":"empty-identity"}],"dirty":false,"evidence":"executable fixture checks; not proof certificates","input":{"instruction":"ADD x1,x2,x3","source":{"clock":9,"pc":65536,"registers":[{"index":2,"value":100},{"index":3,"value":23}]},"target":{"clock":17,"pc":65540,"registers":[{"index":1,"value":123}]}},"revision":"80092c9a0a2aea3db9db3066fba51018b095e628","table_count":89}
```

Raw files: [ADD stdout](add.stdout), [ADD stderr](add.stderr). Normal Lake build status appears on the wrapper's stderr; the wrapper separately rejects unexpected Lean diagnostics and mismatching/incomplete JSON.

**Speaker paragraph.** We can run a concrete ADD witness through the actual assembled row programs and interaction ledger. The valid row adds 100 and 23, while deleting authentication rows or changing an untouched target register makes the checker reject. These executable checks make the acceptance boundary inspectable and reproducible; the printed Booleans are not proof certificates or a completed SP1 capstone.

## Actual counter output and universal statements

The independent machine increments a natural number only below 15. The public field is `ZMod 97`; admissibility requires both canonical endpoints in 0..15 and at most 15 increment events, without reference to witness existence or compiler success. Static lookups prevent field wraparound. The executable compiler takes only the input and event list and returns an optional witness.

Unedited counter driver stdout:

```text
Counter over ZMod 97: executable fixture checks, not proof certificates
PASS compile-2-to-5: expected true, actual true
PASS empty-0-to-0: expected true, actual true
PASS empty-15-to-15: expected true, actual true
PASS maximum-0-to-15: expected true, actual true
PASS shuffled-physical-rows: expected true, actual true
PASS missing-transition: expected false, actual false
PASS duplicate-transition: expected false, actual false
PASS wrong-public-endpoint: expected false, actual false
PASS wrong-event-count: expected false, actual false
PASS endpoint-16: expected false, actual false
PASS decreasing-boundary: expected false, actual false
PASS empty-unequal-boundaries: expected false, actual false
PASS modular-wrap-row: expected false, actual false
Compiled 2 -> 5: rows [[2, 3], [3, 4], [4, 5]]; State interactions 8
```

The driver shows **2→5 with three rows**. The talk's schematic **3→5** diagram is a different example; refresh its labels when using this output. Keep the counter in the appendix. [Raw stdout](counter.stdout), [stderr](counter.stderr), and the [strict focused build output](counter-build.stdout) are included.

The following declarations and axiom reports are copied from the fresh Lean probe, rather than reconstructed by hand. The production soundness/completeness/acceptance equivalence proofs use only `propext`, `Classical.choice`, and `Quot.sound`. The executable regression theorems live in the separate test library and have its disclosed native-computation trust boundary.

```lean
@[reducible] def SP1Clean.Soundness.CounterExample.F : Type :=
ZMod 97
@[reducible] def SP1Clean.Soundness.CounterExample.machine : PFunctor.DynSystem.Labeled interface :=
{ State := ℕ, toDynSystem := PFunctor.DynSystem.mk' id fun n x => n + 1, Event := Event,
  event := fun x x_1 => Event.increment }
def SP1Clean.Soundness.CounterExample.boundary : fieldPair SP1Clean.Soundness.CounterExample.F →
  machine.State × machine.State :=
fun input => (ZMod.val input.1, ZMod.val input.2)
def SP1Clean.Soundness.CounterExample.admissible : fieldPair SP1Clean.Soundness.CounterExample.F → List Event → Prop :=
fun input events => ZMod.val input.1 ≤ 15 ∧ ZMod.val input.2 ≤ 15 ∧ events.length ≤ 15
SP1Clean.Soundness.CounterExample.compile (input : fieldPair SP1Clean.Soundness.CounterExample.F)
  (events : List Event) : Option (Air.Flat.EnsembleWitness ensemble)
SP1Clean.Soundness.CounterExample.soundness :
  ensemble.Soundness (fun x => True) fun input =>
    ∃ events, Air.Flat.Interpretation machine boundary admissible input events
SP1Clean.Soundness.CounterExample.compile_sound (input : fieldPair SP1Clean.Soundness.CounterExample.F)
  (events : List Event) (witness : Air.Flat.EnsembleWitness ensemble) (compiled : compile input events = some witness) :
  Air.Flat.Interpretation machine boundary admissible input events ∧ witness.Valid input
SP1Clean.Soundness.CounterExample.compile_complete (input : fieldPair SP1Clean.Soundness.CounterExample.F)
  (events : List Event) (execution : Air.Flat.Interpretation machine boundary admissible input events) :
  ∃ witness, compile input events = some witness
SP1Clean.Soundness.CounterExample.realizes : Air.Flat.Realizes machine ensemble boundary admissible
SP1Clean.Soundness.CounterExample.statement_iff (input : fieldPair SP1Clean.Soundness.CounterExample.F) :
  ensemble.Statement input ↔
    ∃ events, machine.Trace (boundary input).1 events (boundary input).2 ∧ admissible input events
SP1Clean.Soundness.CounterExample.compiled_interaction_bound (input : fieldPair SP1Clean.Soundness.CounterExample.F)
  (events : List Event) (admitted : admissible input events) :
  ((witnessOfRows input (consecutiveRows (ZMod.val input.1) events.length)).interactionsWith state.toRaw).length =
      2 * events.length + 2 ∧
    2 * events.length + 2 ≤ 32 ∧ 32 < 97
'SP1Clean.Soundness.CounterExample.soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'SP1Clean.Soundness.CounterExample.compile_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'SP1Clean.Soundness.CounterExample.compile_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'SP1Clean.Soundness.CounterExample.realizes' depends on axioms: [propext, Classical.choice, Quot.sound]
'SP1Clean.Soundness.CounterExample.statement_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SP1Clean.Soundness.CounterExample.compiled_interaction_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

[Probe source](declarations.lean), [raw declarations/axioms](declarations.stdout), [probe stderr](declarations.stderr).

**Speaker paragraph.** The counter closes both directions of the arithmetization interface on a small machine. Finite lookups and the ranked exhaustive-trail argument connect raw Clean acceptance to independently defined natural-number execution, and an executable compiler constructs every admissible trace, including empty ones. The universal acceptance equivalence and the executable regression checks are separate evidence. This is a complete small instance; the full SP1 instance remains open.

## Validation scope and CI

Fresh checks in this bundle: ADD JSON reproduction, strict counter-module build, all 13 printed counter cases, and literal declaration/axiom inspection. Every command exited zero; the Lean inspection/driver stderr files are empty. The ADD wrapper's build status is preserved separately.

Historical exact-head local validation is preserved in [validation.json](historical-validation/validation.json), with the available original [test](historical-validation/core-tests.log), [full lint](historical-validation/lint.log), [core lint](historical-validation/core-lint.log), [audit](historical-validation/audit.log), [export](historical-validation/export.log), [857-row interpreter differential](historical-validation/interpreter.log) and [runner regression](historical-validation/add-regression.log) logs. The [strict full-build transcript](historical-validation/build.log) is included. These full gates were not rerun merely for packaging unchanged code.

[Successful PR CI run](https://github.com/dtumad/sp1-lean/actions/runs/36347892958), including [full alignment build](https://github.com/dtumad/sp1-lean/actions/runs/36347892958/job/108701276195), is associated with the exact head above. [Run metadata](ci-run.json) records its head and completion; [PR/check metadata](../pr-100.json) retains both the successful run and the superseded cancelled/skipped run. No pending check is represented as passed.

The workflow uses GitHub's default pull-request merge checkout. Accordingly, CI is PR integration evidence associated with that head; the local logs/reproduction establish the exact source checkout. Later changes to `main` are not implicitly covered by these historical checks. The earlier independent-checkout reproduction at `d9c0e518` is not presented as a fresh-clone result for `80092c9a`.
