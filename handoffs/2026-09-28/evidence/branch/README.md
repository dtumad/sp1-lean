# Joined branch compiler/circuit evidence

This is one local Branch chip example, not an assembled witness or whole-machine completeness.
Published as [PR #106](https://github.com/dtumad/sp1-lean/pull/106), stacked on #103, at
**`066d52a73e01c46e1df8fc4a155176ee59bc660d`**. [Publication metadata](publication.json)
records the current base `112eb5d8`. Full local gates passed on `70b73fa3`; the complete tracked
source tree of the published commit is identical (`4be4c9f840b1d30c707525ed8a1df66c6852d8cb`).
The last merge changed history only after an external base rebase. [History-only integration](history-only-integration.json)
records that equality and fresh passing strict full build/parsed driver at the published clean head.
[Manifest](manifest.json) and [validation results](validation.json) preserve the full-gate revision
rather than relabeling old logs. CI is separately pending in [the captured PR checks](../pr-106.json).
The current head merges the updated #103 base without changing the original example commit.
The diff against the recorded updated base remains exactly the two example source files. The full validation/probe logs are the refreshed records from `70b73fa3`; the final-history
build/driver logs belong to `066d52a7`, as recorded above.

## What is joined

The checked singleton program image contains `BEQ x1, x2, +4092` (`0x7e208ee3`, little-endian
bytes `e3 8e 20 7e`) at PC 65536. The canonical loaded state has both source registers zero.
The fixture proves actual generated Sail decoding, full official `try_step 0 false` with normal
retirement, and a complete ordinary `ExecutionStep` with unchanged host and clock 1 to 9.
Its target PC is 69628.

The canonical semantic projection of that identical source/target transition equals the
computable view passed to `compileInstructionEvent?`. The event is obtained from that compiler
result using proof-checked `Option.get`, without a fallback or separately supplied positive event.
Clean's `BranchChip.component.buildRow` generates the physical row from the event. Its actual
output target is 69628; the table has exactly that one real row and satisfies `Table.Constraints`.
The executable flat check traverses all flattened assertions and fails if static lookups remain.

`driver-output.json` computes compiler/event/row facts. It does **not** execute the full Sail model:
the complete official step is the imported Lean theorem. `theorems-and-axioms.txt` contains the
literal theorem signatures and axiom dependencies obtained from the built module.

## Premises and trust

All concrete prerequisites are discharged in the fixture: image validity and loaded instruction
bytes; initialized/configured Sail source; PC and equal registers; actual configured decoder;
derived fetch readiness; aligned target; running empty host and non-ECALL instruction; canonical
access-plan success; initial frontier and clock 1; event register/value/timestamp bounds; BEQ
opcode; both candidate PC bounds required by the current event contract; and event-derived hints.
The field is the existing KoalaBear `SP1Prime = 2130706433` with its proved size/primality instances.
Prover data is empty. The final `joined` theorem has only the host policy parameter, whose choice
does not affect an ordinary BEQ step. It introduces no caller readiness or semantic-domain premise.

The local table proof constructs no Program, Byte, Range, State or Memory providers and proves
no cross-table channel balance. ROM loading authenticates Sail's fetch independently. This does
not discharge the general all-family compiler, output/access-push agreement, chronological fold,
boundary assembly, resource budget or host endpoint obligations.

This test uses the repository's existing test-only `native_decide` policy for concrete finite
checks. The semantic theorem also inherits the generated Sail platform hooks and standard Lean
logical axioms and existing approved `bv_decide` alignment lemmas. It is not axiom-free and is
not a new production trust exception. Read the exact
axiom output alongside the passing compiled-library audit.

## Reproduction

From a checkout of the recorded commit with pinned dependencies available:

```sh
LEAN_NUM_THREADS=2 lake build --wfail --iofail SP1Clean SP1CleanTest
LEAN_NUM_THREADS=2 lake env lean scripts/branchCompilerExample.lean > branch-output.json 2> branch-driver.log
python3 -m json.tool branch-output.json
LEAN_NUM_THREADS=2 lake test
LEAN_NUM_THREADS=2 lake lint
LEAN_NUM_THREADS=2 lake exe runLinter --no-build SP1Clean.Core ToClean ToMathlib ToPolyFun
LEAN_NUM_THREADS=2 scripts/run_audit.sh
LEAN_NUM_THREADS=2 scripts/check_witgen_export.sh --regen
scripts/run_interp_diff.sh
```

The driver fails on unexpected compiler/row facts. The captured evidence additionally requires
exit zero, empty stderr, JSON parsing, and exact expected numeric/Boolean fields. Copy the included
`theorem-probe.lean` to a local path and run `lake env lean PATH` to reproduce theorem/axiom output.

## Cache and scope

Validation used an isolated repository-local worktree. Only `.lake/packages` and `.lake/build`
were cloned from the already validated compiler campaign cache using `cp -cR`; no entire `.lake`
copy, path dependency, pin change or source change to an existing PR was made. The initial strict
focused build elaborated the fixture; this integration's strict full build rebuilt changed parent
dependencies and checked the whole cached dependency graph. Logs report warm
cache timings, not clean-clone build timings. The new source files and an exact source diff are
included so the evidence remains reviewable outside that worktree.

The unchanged compiler campaign's next slice is general I-type/ALU-type/U-type/x0 validity. This
joined example is a regression consumer, not a replacement for the remaining universal proofs.

## Actual output and speaker paragraph

The final-head [driver stdout](logs/final-history-driver.stdout) is byte-for-byte equivalent JSON
to [driver-output.json](driver-output.json): one real row, 46 cells, 50 flattened assertions,
immediate 4092, taken branch and target PC 69628. The final driver stderr is empty.
[Literal theorem statements and axiom dependencies](theorems-and-axioms.txt) come from the
same source tree. Read the statements separately from the executable output: the driver does
not run the noncomputable full Sail state.

**Speaker paragraph.** This branch example now joins the layers that the earlier regression
checked separately. The loaded instruction branches from 65536 to 69628 under the official
Sail step; the semantic compiler receives that same transition and generates the actual Clean
row, whose target and local constraints agree. The previous twelve-bit helper would turn the
legal offset +4092 into −4. This is a concrete regression for the fork's compiler/specification
connection, with the full Sail step supplied by a Lean theorem. It proves local chip acceptance,
without claiming assembled balance or general compiler completeness.
