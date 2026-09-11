# Axiom and trust ledger

Checked against the consolidated stack on 2026-09-11. Each raw file retains the source revision
at which its unchanged declaration inventory was recorded:
[`axiom-census.txt`](axiom-census.txt) (the main `SP1Clean` library, 1384 declarations) and
[`axiom-census-test.txt`](axiom-census-test.txt) (the `SP1CleanTest` anchors, 140 declarations).
`scripts/run_audit.sh` reproduces both and rejects dependency drift. The main and test split lets
CI elaborate each probe against the library built by that job.

## Result

- 1524 released declarations are probed.
- No source proof deferrals or project `axiom` declarations occur in the main library.
- No probed declaration carries `sorryAx`.
- Kernel bypasses and `native_decide` are absent from the main library.
- Compiler-trusted executable witnesses and regressions are isolated in `SP1CleanTest/`.

There is no direct-admission allowlist and no transitive `sorryAx` carrier allowlist. Both are empty.
The census is an explicit released-declaration inventory, not a claim that every declaration in the
repository has been independently reviewed. Adding a new public claim requires adding its probe.

An unexplained change to an axiom set requires review. A changed generated bit-vector proof-constant
index can be harmless, but must still be inspected before updating the raw snapshots. Historical
inventory growth and retired proof names can be recovered from git history.

## Dependency classes

The census reports several classes that should not be conflated:

| Class | Scope |
|---|---|
| `propext`, `Classical.choice`, `Quot.sound` | ordinary Lean/mathlib logical baseline |
| generated `bv_decide` proof constants | selected arithmetic and bit-vector helper proofs |
| generated Sail platform hooks | the official interpreter's external platform operations |
| generated `native_decide` constants | executable conformance tests only |
| `sorryAx` | forbidden; absent |

The uniform decoder agreement checkpoint added five main proofs. The ROM-fetch and hint-exclusion
lemmas use subsets of the ordinary logical baseline. `SailDecode.instructionDecode_agrees` and
`DecodedProgramProvider.spec_committed`/`constraints_committed` also retain Sail's `sys_enable_experimental_extensions`
hook through the official decoder target. The former closes `InstructionDecode.AgreesWithSail`;
the provider bridges instantiate the existing conditional ROM theorem without a decoder premise,
including directly from physical-row constraints. Two new
regression anchors include a compiler-trusted alias-domain check and kernel-checked witnesses of
Sail's hint priority.

The combined native-boundary integration adds 19 main declarations and three executable regression
anchors. These cover generic channel closure, the 59-table assembly and boot verifier, initial-record
authentication/uniqueness and its physical ledger, and Program-row ROM/Sail membership. The generic
closure and inventory arguments use the ordinary logical baseline. The assembly-indexed statements
also reference the existing proof-bearing chip registry and retain its disclosed Sail/bit-vector
dependencies; an initialization-only conclusion does not erase those dependencies from its type.
The new executable regressions remain in the test library. No previously recorded declaration
changed its axiom set, and no new main-library axiom name appeared. The three new compiler-trusted
constants belong exactly to those three test anchors.

The native Memory-frontier checkpoint adds 12 main probes: two shared selector/multiplicity lemmas
and ten assembly-level ledger, balance, and genesis statements. The shared lemmas use only the
ordinary logical baseline. The ten assembly statements retain the registry's existing 100-axiom
set, including its disclosed Sail and bit-vector dependencies. No prior main or test declaration
changed its axiom set, no recorded declaration was removed, and no new axiom name appeared.

The mixed-row Memory connection adds 21 main probes and one kernel-checked regression. Nine
component-local projection/selector proofs use the ordinary logical baseline, and the two
message-permutation interface proofs use no axioms. Ten assembly-indexed statements retain the
registry's existing 100-axiom set. The syscall read-time regression uses only the ordinary logical
baseline. All earlier axiom sets are unchanged, no declaration was removed, and no new axiom name
appeared in either scope.

The native State-ordering and touch-alignment checkpoint adds 32 main probes. Sixteen local
projection, timestamp, alignment, and generic trail proofs use the three logical baseline axioms;
`AlignedFacts.rowOKCore` uses two. Fourteen registry/assembly statements retain the existing
100-axiom set; the mixed carrier's State/facts equality retains 77 already-disclosed dependencies.
No earlier main declaration changes its axiom set, no declaration is removed, and no new main
axiom name appears. The local touch contract deliberately retains prior-clock conditions; its
closed construction is not a claim that mixed execution grounding is complete.

The prior-record and refresh-chronology checkpoint adds 11 main probes. Three table-local
MemoryBump evidence/order proofs use the three logical baseline axioms. Eight assembly-indexed
statements retain the existing 100-axiom registry set. No earlier main or test axiom set changes,
no declaration is removed, and no new axiom name appears. `ordered_memory_rows` derives both
prior clock-limb bounds and strict refresh order; `memory_refresh_free` consumes those conclusions
to construct the refresh-free ledger. These are structural chronology results; mixed execution
steps, host effects, and final-record currency remain separate obligations.

The mixed-carrier transport and grounding connection adds 27 main probes. Seventeen generic
read-window, rewrite, and timeline declarations use subsets of the logical baseline (fourteen
use two axioms; three use all three). Ten assembly-indexed declarations retain the existing
100-axiom registry set. All earlier main and test axiom sets are unchanged, no declaration is
removed, and no new axiom name appears. `grounding_carrier` constructs the canonical rewritten
carrier and `ground_of_steps` connects it to the generic engine, with original event step/frame
facts explicitly retained. Conditional final-value currency does not certify host execution or
bound an original refresh timestamp by the final State clock.

Most chip-local semantic and whole-chip faithfulness proofs use only the ordinary logical baseline.
Mul and several Sail bridges additionally retain generated bit-vector decision proofs. Execution
theorems stated against the complete Sail interpreter inherit its platform-hook surface, including
hooks not reached by the supported ordinary RV64IM paths.

`supported_core_native_sound` is proof-complete and `sorryAx`-free. Its census is not limited to the
three logical axioms because its target and its 25 Sail bridges retain the generated Sail and
bit-vector dependencies. The conditional exact-upstream
`sp1_air_refinement_of_obligations`/`sp1_air_sound_of_obligations` declarations inherit the same target
surface.

## Coverage of the probe generator

The generator scans:

- every chip's soundness, completeness, bundled circuit, and Sail bridge;
- Branch's split core proofs and DivRem's split completeness driver;
- every whole-chip faithfulness theorem, including the nested DivRem exact module;
- the proof-bearing 25-chip faithfulness index;
- witness and full-trace conformance anchors;
- the active official-Sail-step, deterministic-compiler-event, and bounded native non-vacuity join;
- the native grounding and soundness capstones;
- the generic ensemble correctness/export interfaces, fixed program provider, and finite
  program-image and host-memory frame proofs, authenticated initial register/RAM providers,
  ordered-key uniqueness, constructive row domains, and initialization inventory derived from
  the actual Clean control ledger with fixed endpoints, canonical finalization, and both
  inventories' exact physical Memory projections, plus the combined native assembly's raw-constraint
  initialization/Program/boot results and generic channel closure, its complete mixed Memory
  ledger and per-location frontier balance, the authenticated genesis invariant, exact mixed-row
  Memory projections, State ordering, aligned touch chronology, prior/final clock bounds, and
  refresh elimination derived from the native AIR, mixed read-window transport, canonical
  carrier construction, its derived timeline, and grounding under explicit event step/frame facts;
- the common shard evaluator, paired exact relation, natural-ledger bridge, and native
  correctness/language-equality surface;
- exact Core profile and manifest guards;
- the conditional exact-AIR refinement boundary;
- COMMIT-wrapper strengthening theorems; and
- registry, routing, balance, decode, and execution support theorems.

An incorrect fully qualified name causes probe elaboration to fail. The generator also compares
its new inventory with both committed probe files before writing either: losing a recorded name
fails even if a sibling still matches the same regular-expression target. This closes the partial
alternation failure that previously let a renamed `_core` theorem disappear from the census.

`python3 scripts/gen_axiom_probe.py --check` checks exact source/probe agreement without writing and
runs in CI. Intentional removals or renames require regenerating with `--allow-removals` and reviewing
the probe diff; that flag does not permit a configured target to match nothing. The audit-tool
regressions cover partial matches, both library inventories, intentional renames, and read-only
checking. This is protection against accidental coverage loss, not against a reviewer approving a
reduced inventory.

## Reproduce

```bash
lake build SP1Clean
lake test
python3 scripts/gen_axiom_probe.py --check
scripts/run_audit.sh
```

Use the raw census for declaration-level review. The summary above is intended to explain classes, not
replace that evidence.

The component-local ordinary-execution checkpoint adds 59 main probes, including the preserved
witness-facing compatibility methods. The four new native assembly/carrier statements retain
the existing 100-axiom registry set. The trajectory-generic ordinary step/frame proofs retain
the existing Sail target dependencies. One previously probed declaration changes its set:
`supportedChip_groundingContracts` drops the two Clean byte-provider `bv_decide` constants from
`And8.and_times_two_add_xor` and `Or8.or_times_two_sub_xor` (100 to 98 axioms), because its local
contract no longer includes the legacy ensemble's provider/balance proofs. Every other prior
main and test set is unchanged; no declaration was removed and no new axiom name appeared.
That checkpoint derives ordinary chip assumptions and operand bindings for the new assembly.
The subsequent mixed-execution checkpoint constructs the trajectory and derives HALT step/frame
facts; ROM preservation and active syscall step/frame facts remain explicit obligations.

The mixed-execution checkpoint adds 18 main probes. Seven handler, HALT, and timeline declarations
use subsets of the ordinary logical baseline (six use three axioms, one uses two). The semantic
event projection retains the existing 77 Sail dependencies through its instruction-row carrier;
ten assembly-indexed declarations retain the existing 100-axiom registry set. Every prior main
and test dependency set is unchanged, no declaration was removed, and no new axiom name appears.
`ground_of_host_steps` constructs the trajectory and discharges ordinary/HALT grounding internally.
It remains conditional on ROM preservation and active syscall step/frame facts, and does not yet
establish terminal ECALL/Exit agreement or the full boot-to-HALT execution relation.

The native syscall-semantics checkpoint adds 14 main probes and one kernel-checked regression.
Component-local inputs derive the row law without the legacy no-carry premise. The native
post-grounding bridge derives an `EventStep` for each active syscall on the constructed trajectory,
including the committed ECALL, three source registers, and target PC/return register. Host step/frame
facts remain conditional; full-code restrictions, host RAM effects, and ROM protection are not
claimed closed. The regression witnesses a PC arm whose raw low limb crosses `65535` while the
recombined PC correctly advances four bytes; it does not claim a complete AIR witness.
Seven new component-local proofs use the three-axiom logical baseline. `syscallRow_sourceValues`
also retains the official decoder's existing `sys_enable_experimental_extensions` hook through
its committed-program premise. Six assembly-indexed proofs retain the existing 100-axiom registry
set. The regression uses only the logical baseline. Every prior main and test axiom set is
unchanged; no declaration was removed and no new axiom name appeared.

The native syscall-profile checkpoint adds 15 main probes, all within the logical baseline:
ten use three axioms, three use `propext`/`Quot.sound`, and two use `propext` alone.
The fixed lookup and composed instruction chip are sound and complete; raw constraints derive
the eight-code restriction before Memory grounding. Projection preserves the original assertions,
interactions, and row width. The two existing word-encoding APIs retain identical elaborated
statements and axiom sets after their arithmetic was hoisted into `Math/WordEquality.lean`.
All prior main/test axiom sets are unchanged, with no removals or new main-library axiom names.
Five actual-constraint, export-inventory, and wiring regressions add five named compiler-trust
constants only in `SP1CleanTest.Core.SyscallCode`. The strengthened chip is not yet installed in
the 59-table assembly. Authenticated WRITE x12/buffer reads, HINT_READ's padded writes and
timestamp treatment, host effects, and ROM protection remain open integration obligations.

The stateful native-host checkpoint adds 16 main probes: eight use the three-axiom logical
baseline, seven use `propext`/`Quot.sound`, and the executable dispatcher uses `propext` alone.
The interpreter obtains actual register/byte observations, computes all eight selected effects,
and threads terminal state, both commitment banks, outputs, hints, and request-bound replies.
Its Sail adapter proves committed ECALL row laws and endpoint agreement, written-byte readback,
memory/register frames, and ROM preservation. All 1319 prior main and 113 prior test axiom sets
are unchanged; no declaration was removed and no new main-library axiom name appeared.
Eleven executable regressions add eleven compiler-trust constants only in
`SP1CleanTest.Core.HostExecution`. The host state is not yet threaded through mixed timed
grounding, and AIR-authenticated host accesses remain open. The native mutable commitment banks
also retain the disclosed exact-AIR compatibility gap: distinct overwrites within one shard
cannot all satisfy the exact instruction AIR's fixed public-digest binding. Recorded proof
requests assert no recursive proof acceptance.

The aligned host-footprint checkpoint adds 21 main probes: fifteen use the three-axiom logical
baseline, four use `propext`/`Quot.sound`, the footprint builder uses `propext` alone, and the
deduplicated-union theorem uses no axioms. Coverage, native window bounds, and distinct canonical
Memory locations follow from the computed inventory and successful host execution. Defined
Memory-bus words determine the host result; fully written words have the emitted little-endian
contents, and outside RAM cells are preserved. All 1335 prior main and 124 prior test axiom sets
are unchanged, with no removals or new main-library axiom names. Six regressions add six
compiler-trust constants only in `SP1CleanTest.Core.HostFootprint`. The minimal native cover's
empty-WRITE distinction from Rust's untraced physical reads is explicit. These are local semantic
bridges: host AIR tables, their timestamps and balanced accesses, and threaded host state in the
mixed trajectory remain integration work.

The host RAM access checkpoint adds nine main probes, all using only the three-axiom logical
baseline. The native circuit is sound and complete for a bounded word transfer at an aligned
guest RAM address, with strict prior/new time order and an effect at event time plus one. Its
constructor derives the timestamp witnesses from semantic bounds and order. The exact evaluated
Memory pair and host coordination record are retained, and its 201-cell witness program passes
the exportability check. All 1356 prior main and 130 prior test axiom sets are unchanged, with no
removals or new main-library axiom names. Four executed regressions add four compiler-trust
constants only in `SP1CleanTest.Core.HostRamAccess`. The component remains outside the mixed
ensemble; call-level footprint/value authorization, WRITE's x12 access, and threaded host state
remain open integration work.

The instruction-to-host handoff checkpoint adds nineteen main probes, each with exactly
`[propext, Classical.choice, Quot.sound]`. `HostCallChip` composes the original full-code-checked
syscall circuit, internally derived WRITE selection, and an authenticated x12 read-back at
event time plus one. Its raw-constraint and ledger theorems retain every original instruction
interaction, including PublicValues, and expose the complete evaluated host request. Both the
register reader and handoff have soundness/completeness proofs and timestamp constructors;
the composed witness program exports eight cells. The shared timestamp arithmetic replaces
existing proof bodies without changing any of the 1365 preceding main or 134 preceding test
axiom sets. Six new compiler-trust constants occur only in `SP1CleanTest.Core.HostCall`.
The audit now probes 1384 main and 140 test declarations, with no removals or new main-library
axiom names. This is a local component result: the x12 touch and handoff are not yet installed
in the mixed ensemble, and RAM footprint authorization, host effects and host-state threading
remain open. The original PublicValues pulls are preserved; compatibility with mutable
commitment slots remains separate.
