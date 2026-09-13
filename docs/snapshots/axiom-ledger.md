# Axiom and trust ledger

Checked against the consolidated stack on 2026-09-13. Each raw file retains the source revision
at which its unchanged declaration inventory was recorded:
[`axiom-census.txt`](axiom-census.txt) (the main `SP1Clean` library, 1863 declarations) and
[`axiom-census-test.txt`](axiom-census-test.txt) (the `SP1CleanTest` anchors, 233 declarations).
`scripts/run_audit.sh` reproduces both and rejects dependency drift. The main and test split lets
CI elaborate each probe against the library built by that job.

## Result

- 2096 released declarations are probed.
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

The native ROM-permission checkpoint adds 45 main declarations and six test anchors. Forty-two
main additions use the logical baseline or a subset. The new ensemble and its table-count theorem
retain the existing 100-axiom registry set; the byte-frame ROM-preservation lemma retains the
existing 77-axiom Sail set. All preceding 1818 main and 227 test dependency sets are unchanged,
with no removals or new main-library axiom names. Six new compiler-trusted proof constants are
isolated to the ROM-write, permission-forgery, partial-write, non-store, endpoint, and padding tests.

`ProtectedLocalCore.ensemble` installs a fixed writable-interval provider and four store wrappers.
The wrappers prove exact preservation of original physical widths, assertion/lookup lists, and
existing ledgers. The provider's constructor succeeds exactly on writable 48-bit byte addresses;
its soundness/completeness and exportable comparison witnesses are closed. Complete AIR regressions
reject a reproduced store into its own instruction and forged/missing permissions while retaining
partial writes beside code, store padding, and stopped identities. This is an explicit native
immutable-code profile restriction, separate from the original Rust-faithfulness claims.

The new 60-table witness still needs projection to the existing local assembly, permission
source authentication through balance, and grounding transport. The existing execution combinator
therefore still takes ROM preservation as a premise. Host-memory writes, complete outgoing-state
agreement, terminal Exit agreement, and compiler totality remain open.

The stateful local HALT checkpoint adds 16 main declarations and three test anchors. Eight main
additions use the logical baseline or a subset, two retain the existing 77-axiom Sail set, and six
retain the existing 100-axiom registry set. All preceding 1802 main and 224 test dependency sets are
unchanged, with no removals and no new main-library axiom names. The three new compiler-trusted
constants are isolated to the active HALT, legacy exit-range, and forged-HALT test anchors.

HALT's Program fetch, zero code, upper exit limbs, and incoming register currency now determine
the actual stateful host transition and its exit status. The local grounding theorem derives its
step/frame facts internally, retaining ROM preservation and active SyscallInstrs effects as
semantic premises. The host policy characteristic explicitly agrees with the AIR field. The legacy
HALT row remains restricted to 16-bit exits; regression confirms that 65536 is accepted by the
concrete host but rejected by this row. Terminal Exit-bus agreement, full outgoing-state agreement,
ordinary normal-retirement reconstruction, the other host effects, and compiler totality remain open.

The following checkpoints record the claim boundary at each preceding stage.

The local stateful-replay checkpoint adds 34 main declarations and three test anchors. Twenty
main additions retain the existing 100-axiom registry set; ten retain the existing 77-axiom Sail
set. The incoming-state ordinary engine interface uses 98 of the registry's existing axioms.
Two shared projection/ordering proofs use subsets of the logical baseline; the non-ECALL proof
adds only the already disclosed experimental-extension hook to that baseline. All preceding
1768 main and 221 test dependency sets are unchanged, with no removals or new axiom names in
either scope. The three tests are kernel proofs reusing existing execution fixtures, with no
new compiler-trusted proof constants.

The local AIR's ordered tape now drives paired replay of the complete source state. Covered
replay clocks agree with the AIR timeline, and all ordinary chip step/frame facts are derived
on the actual Sail projection. Running-host and non-ECALL guards follow from incoming State
truth and committed decoding. The conditional grounding theorem retains only ROM preservation
and HALT/syscall facts as semantic premises; it does not assume replay success. Final State truth
recovers successful full-tape replay and the returned PC/clock. Normal-retirement reconstruction,
actual host-effect constraints, complete outgoing-state agreement, and compiler totality remain
open. Endpoint extension in the mathematical trajectory adds no execution steps.

The local structural-grounding checkpoint adds 48 main declarations and four test anchors.
Sixteen main additions use the logical baseline or a subset; 28 retain the existing 100-axiom
registry set, and one retains the existing 77-axiom Sail set. The shared ordinary alignment theorem
uses 98 of the registry's existing axioms. Two syscall decoding/window proofs use the baseline
plus the already disclosed experimental-extension hook. All preceding 1720 main and 217 test
dependency sets are unchanged, with no removals or new main-library axiom names. The four new
compiler-trusted constants belong only to the repeated-register, State-carry, clock-phase, and
stopped-source regressions.

The local AIR now derives aligned touches, prior/final clock bounds, strict refresh order, a
canonical carrier, and its source-bound timeline. `GroundingCarrier.ground_of_steps` connects that
carrier to the grounding engine while explicitly retaining original-event step/frame premises.
Two verifier assertions freeze a stopped source's clock; strict State ordering then excludes all
active events, fixing the reproduced ADD-after-HALT gap while preserving identity segments.
Stateful host-result binding, ROM preservation, complete outgoing-state agreement, and compiler
totality remain open. The active clock phase must be explicit in the shared compiler profile.
No unconditional local execution or AIR equivalence is claimed.

The local Program/State checkpoint adds 55 main declarations and three test anchors. Thirteen
main additions use the logical baseline or a subset; 36 retain the existing 100-axiom registry set,
and four shared row definitions retain the existing 77-axiom Sail set. The generic Program
matching theorem uses the baseline plus the already disclosed experimental-extension hook.
Byte/Range component silence uses the baseline plus two existing Clean bit-vector constants.
All preceding 1665 main and 214 test dependency sets are unchanged. There are no removals and no
new main-library axiom names; the three new compiler-trusted constants belong only to the local
reordered/padded, empty-segment, and unauthenticated-fetch regressions.

The local AIR now authenticates every active Program fetch and derives exact mixed Memory/State
ledgers, an exhaustive canonical State walk, and exact event durations, without caller-supplied
ordering or syscall inactivity. The shared row carrier, Program source proof, provider silence,
and verifier endpoint projection also serve the boot assembly. Local aligned grounding, stateful
host-result binding, exclusion of active execution after HALT, and complete outgoing-state agreement
remain open; no unconditional local execution or AIR equivalence is claimed.

The local Memory-ledger checkpoint adds 21 main declarations and four test anchors. Six main
additions use exactly the logical baseline; fifteen retain the existing 100-axiom registry set
through their assembly-indexed types. The component multiplicity proof moved to the shared
`CoreMemoryBalance` module without changing its public name. All preceding 1644 main and 210 test
dependency sets are unchanged, with no removals or new main-library axiom names. Four new
compiler-trusted constants belong only to `SP1CleanTest.Core.LocalCore`.

The local AIR now supplies canonical and unique final records, the exact physical Memory ledger,
signed-unit multiplicities, complete record permutation, and the per-location source/final equation.
The shared rules also replace duplicated boot-only boundary algebra. Full-ledger regressions exercise
active HINT_LEN and distant clock epochs, with one refresh per touched register at the maximum
24-bit high clock. They also record a concrete remaining host-binding gap: jointly forging HINT_LEN's
return and final register record preserves current AIR validity while disagreeing with finite host
execution. These results establish ledger structure, not final-value currency or native execution
soundness. Host integration and transport of the later boot grounding stages remain open.

The complete-source grounding checkpoint adds 15 main declarations and two test anchors.
Ten main additions use exactly the logical baseline; five retain the existing 100-axiom registry
set through their assembly-indexed types and proofs. All preceding 1629 main and 208 test dependency
sets are unchanged, with no removals or new main-library axiom names. The two new compiler-trusted
constants belong only to the local assembly's source-binding and platform-rejection regressions.
The initialized Sail register map is now computable through a proved order-independent finite-map
fold, preserving its existing lookup and configuration theorems. The complete source is the local
ensemble parameter; its finite configuration/ROM/range checks and actual incoming PC/clock binding
supply initial State truth and the full live-memory invariant directly from raw constraints and
balance. Source timestamps are admissible local genesis seeds, including at nonzero clocks.
Complete outgoing-state agreement, active host integration, post-HALT AIR exclusion, and certified
native witness composition remain open.

The complete finite-boundary checkpoint adds 22 main declarations and seven test declarations.
Nineteen main additions use only the logical baseline; three retain the existing 77-axiom Sail
dependency set through the semantic step/segment relation. No new main axiom name appears, and
all preceding 1607 main and 201 test dependency sets are unchanged. Six new compiler-trusted
constants belong only to the snapshot regressions; the seventh test derives an actual HINT_READ
semantic step from its checked finite execution through the general soundness theorem.
The results cover exact full Sail/host/clock comparison, provider projection, boot representation,
semantic identity/composition, and sparse host execution with complete padded-memory effects.
They do not authenticate complete AIR boundaries or close the ordinary compiler or native witness
composition theorem.

The local snapshot-assembly checkpoint adds 21 main declarations and six test declarations.
Ten main additions use only the logical baseline (one omits `Classical.choice`); eleven retain the
existing 100-axiom registry set through their assembly-indexed types and proofs. No new main axiom
constant appears, and all preceding 1586 main and 195 test dependency sets are unchanged. The six
new compiler-trusted constants belong only to the complete local-assembly regression anchors.
These results cover finite source/program/ROM validation, source-record authentication and
uniqueness, the exact physical Memory projection, and Byte/Program closure for arbitrary local
PC/clock endpoints. Complete Sail/host endpoint binding, local timed grounding, final-state
agreement, and certified native witness composition remain open.

The arbitrary source-snapshot checkpoint adds 30 main declarations and seven test declarations.
All main additions use only the logical baseline; three omit `Classical.choice`. No new main
axiom constant appears, and all preceding 1556 main and 188 test dependency sets are unchanged,
including the generalized boot RAM provider. The seven new compiler-trusted constants belong
only to the snapshot regression anchors. The results cover complete finite RAM/register comparison,
snapshot-to-Sail content transport, source-value authentication, ordered provider composition,
and their constructors. They do not establish full machine-state endpoint encoding, arbitrary
native AIR shard composition, or incoming timestamp admissibility.

The stateful local-path checkpoint adds 51 main declarations and 15 test declarations. Nine of the
main additions use only the logical baseline (three omit `Classical.choice`); 42 retain the existing
77-axiom official-Sail dependency set through the step/run semantics. No new main-library axiom
constant is introduced, and all preceding 1505 main and 173 test dependency sets are unchanged.
The new tests add eleven compiler-trusted constants, confined to `SP1CleanTest`.
The probed results cover complete-state local path composition, split/join, determinism, PolyFun
finite reachability, stateful replay, post-HALT exclusion, and semantic boot/HALT corollaries.
They do not establish arbitrary native AIR boundary authentication, host-table integration,
compiler totality, native witness composition, or full event-tape export.

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
That checkpoint audited 1384 main and 140 test declarations, with no removals or new main-library
axiom names. This is a local component result: the x12 touch and handoff are not yet installed
in the mixed ensemble, and RAM footprint authorization, host effects and host-state threading
remain open. The original PublicValues pulls are preserved; compatibility with mutable
commitment slots remains separate.

The mutable commitment-bank checkpoint adds twenty-two main probes using only subsets of
`[propext, Classical.choice, Quot.sound]`. The native COMMIT/COMMIT_DEFERRED components prove
soundness/completeness, construct comparison/byte witnesses, retain exact handoff/state/public
ledgers, and implement the independent host interpreter's single-slot effect. Strict bounded
clock order and actual bank-table balance yield an exhaustive interpreter history through
`HostCommitHistory.ordered_history`; local table specifications and initial/final endpoints
remain explicit premises. All 1384 preceding main and 140 preceding test axiom sets are unchanged,
with no removals or new main-library axiom names. Six new compiler-trust constants occur only
in `SP1CleanTest.Core.HostCommit`, covering all sixteen routes, bounds and corrupted witnesses,
original instruction/provider balance, distinct overwrites, and rejected forks or omitted updates.
The 186-cell witness programs are exportable. That checkpoint audited 1406 main and 146 test
declarations. Native historical PublicValues providers permit mutable banks; they do not prove
the exact AIR's fixed `PublicValueBinding`. Installing these components and authenticating zero
initial/public final banks in the mixed machine remain integration work.

The public bank-boundary checkpoint adds nineteen main declarations, each using exactly
`[propext, Classical.choice, Quot.sound]`. `HostCommitEnsemble.sound` derives an exhaustive
ordered interpreter history from the actual nine-table bank ensemble's constraints and balance.
The verifier fixes zero genesis and public final words; a value-preserving terminal keeps the
last call timestamp private. Local contracts follow from Byte closure. Static auxiliary-component
proofs still establish bank-channel exclusion and Byte-provider requirements, and the host policy's
characteristic is explicitly matched to the field. All preceding 1406 main and 146 test axiom sets
are unchanged, with no removals or new main-library axiom names. Five new compiler-trust constants
occur only in `SP1CleanTest.Core.HostCommitBoundary`. Empty-bank regressions check the complete
emitted ledger; active histories check local assertions, Byte meanings, and bank balance, without
claiming full-machine call authentication. The terminal and verifier witness programs export
48 and zero cells respectively. That checkpoint audited 1425 main and 151 test declarations.
Installation in the mixed machine, authentication of calls, and coordination with its other host
effects remain open; this checkpoint does not establish a new RISC-V execution theorem.

The native control-handler checkpoint adds twenty-seven main declarations. Twenty-six use exactly
`[propext, Classical.choice, Quot.sound]`; `HostHaltChip.stopped_after` uses only `propext`.
Both handlers have closed local circuit proofs, full-dispatch bridges from matched register
observations, and exact HostCall ledger projections without another Memory or Exit contribution.
Constructors derive their completeness assumptions from successful host interpretation. The
instruction's structural exit range is proved equivalent to the handler's canonical bound at
`SP1Prime`; this field specialization is explicit. All preceding 1425 main and 151 test axiom sets
are unchanged, with no removals or new main-library axiom names, including after sharing the host
regression evaluator. Seven new compiler-trust constants occur only in
`SP1CleanTest.Core.HostControl`. They check canonical exits, unrestricted unused arguments,
malformed fields and witnesses, joint instruction/handler ledgers, handoff tampering, complete
interpreter effects and terminality, and constructed rows across clock-limb boundaries.
HALT and ENTER export 64 and zero witness cells. The census now probes 1452 main and 158 test
declarations. Matched observations and host-state order still need whole-machine derivation;
the four remaining host handlers and mixed-machine installation remain open.

The shared host-read checkpoint adds nineteen main declarations. Seventeen use exactly
`[propext, Classical.choice, Quot.sound]`; the physical-plan projection and uniqueness proofs
use `propext` and `Quot.sound`. The native provider preserves the word and performs one physical
Memory transfer while serving one or two logical consumers through separate unit interactions.
The semantic span plan proves exact read multiplicities, including overlapping buffers, and
constructors prove local completeness; physical address uniqueness explicitly requires correctly
indexed prior records. All preceding 1452 main and 158 test axiom sets are unchanged, with no
removals or new main-library axiom names. Five new compiler-trust constants occur only in
`SP1CleanTest.Core.HostRamRead`. Executed fixtures cover empty and overlapping spans, the final
RAM cells, unit multiplicities, invalid sharing/writes/witnesses, and mismatched or omitted reads.
The composed witness program exports 201 cells. The census now probes 1471 main and 163 test
declarations. Buffer requests in these regressions are fixtures: call-bound span/byte
authentication, the remaining host handlers, and mixed-machine installation remain open.

The host-byte checkpoint adds sixteen main declarations, all using exactly
`[propext, Classical.choice, Quot.sound]`. The read provider now exports its proved local word
and aligned-address bounds through the existing read channel. `HostRamBytes` has closed native
soundness/completeness, a constructor computing its low-byte columns, and exact ledger proofs:
one full-key read pull and no physical Memory touch. Its output reaches the Sail-backed host
byte interface once the corresponding Memory word is grounded. Defined covering words also
authenticate arbitrary requested slices with explicit complete guest-window bounds. The shared
byte-extraction lemma moved into `Math/ByteWord`; its existing grounding statement is preserved.

All preceding 1471 main and 163 test axiom sets are unchanged, with no removals or new main-library
axiom names. Five new compiler-trust constants occur only in `SP1CleanTest.Core.HostRamBytes`.
Executed regressions check all eight output positions, shared provider/consumer ledgers, malformed
byte columns and local channel guarantees, changed read keys, unaligned and empty reads, missing
bytes, and a span crossing the upper guest boundary. The decoder exports zero witness-program
cells. The census now probes 1487 main and 168 test declarations. Call-bound complete buffer
coverage, the four remaining host handlers, and mixed-machine integration remain open.

The complete 32-byte buffer checkpoint adds eighteen main probes. Seventeen use exactly
`[propext, Classical.choice, Quot.sound]`; the computed alignment selector uses no axioms.
`HostBuffer32` proves soundness, constructive completeness, full-window byte semantics,
minimal ordered coverage, and exact read/buffer/Memory ledgers. All eight alignment variants
export with zero witness-program cells. All preceding 1487 main and 168 test axiom sets are
unchanged, with no removals or new main-library axiom names. Five new compiler-trust constants
occur only in `SP1CleanTest.Core.HostBuffer32`, covering alignment and serialization, limb and
window boundaries, changed messages/cells, and overlapping buffers sharing seven physical reads.
The census now probes 1505 main and 173 test declarations. Buffer messages still require binding
to decoded calls; Memory currency, host-state order, and mixed-machine installation remain open.
