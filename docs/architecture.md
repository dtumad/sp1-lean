# Architecture

## Design rule

The stable verification boundary is a complete SP1 chip.

Rust operations and Lean gadgets may use different intermediate structures. A native Lean chip is
proved against a semantic contract, connected to Sail, and then compared with the complete upstream
chip assertion and interaction systems. Shared reader and operation extraction provides canonical
statement targets for the whole-chip oracles; the public verification boundary remains the chip.

This produces four distinct objects:

1. a proof-oriented native Clean circuit;
2. a semantic chip contract;
3. a complete extracted Rust AIR oracle; and
4. a Sail instruction-step theorem.

No one of these objects is silently treated as another.

That rule does not license duplicate *views* of the same object. The machine layer therefore has
two explicit strata and proved views at their boundary:

1. **Operational semantics:** `Machine.EventExecutionTrace` is the sole proof-free execution
   carrier. A valid trace converts directly to PolyFun's `DynSystem.Prefix`; its ordinary fragment
   converts directly to `SailChain`. `FormalModel/SupportedShard.lean` states the exact native
   supported image over this carrier.
2. **Physical AIR:** `DecodedInstructionRow`, `ChipRow`, and `RowView` retain dependent circuit
   types and field encodings. They are codecs for the physical witness, not competing execution
   models.

The completeness compiler also has **derived, field-free views**: `InstructionAccessPlan`,
`AccessSchedule`, `MemoryHistoryAccess`, and the State-history records.  They are deterministic
projections of `EventExecutionTrace`, not a second proof-free execution witness.  Their physical-row
projections are either proved in the agreement modules or named explicitly in `NativeTraceReady`;
an unbridged standalone timeline would still be duplicate representation.

Instruction identity follows the same rule. `Model/InstructionChipId.lean` fixes the neutral
25-entry order; `Model/InstructionRouting.lean` owns the pure opcode/`x0` route; and
`Soundness/SupportedMachine.lean` is only the circuit-bearing realization of those identities.
Adding another opcode list or positional 25-chip literal is an architecture regression.

The interaction layer deliberately has **two** primary views because their information differs:

- typed `TypedInteraction`s for soundness, where a message retains its State/Memory/Program shape;
- computable `LookupAccess` ledgers for completeness, recounting, and integer balance.

`Interaction.toAccess`, lifted table/ensemble-wide, is their bridge. Clean orientation is canonical
inside the native model. The Memory/Program sign dualization used by extracted Rust faithfulness is
an explicit Rust-facing projection, never a second native ledger definition.

## Repository layers

| Layer | Responsibility |
|---|---|
| `Math/` | field-generic words, carries, bit operations, and arithmetic lemmas |
| `Model/` | SP1 messages, channels, Sail state/execution, schedules, and syscall interfaces |
| `Extracted/` | generated Rust rows, assertion lists, interaction lists, manifest, and provenance |
| `FormalModel/` | semantic contracts and public witness relations |
| `Native/` | independent Clean circuits and witness-producing gadgets |
| `Proofs/` | circuit soundness/completeness and Sail bridges |
| `Faithful/` | whole-chip comparisons on canonical native rows reconstructed from extracted Rust rows |
| `Soundness/` | machine registry, typed decoding, grounding, and capstones |
| `Composition/` | the composed exact→native artifact: transport, provider redistribution, the 55-table assembly |
| `SP1CleanTest/` | compiler-trusted executable conformance tests, isolated from the main library |

`SP1Clean.lean` imports the complete main proof library (`scripts/check_root_index.sh` gates that it
lists every module). The test library imports it in the opposite direction and is never part of the
main theorem graph.

## Deliberate layering exceptions

Layering is by convention, and four exceptions to it are design decisions rather than drift. An
auditor should expect exactly these:

1. **Three chips keep `main` in `Proofs/`.** `DivRemChip`, `ShiftLeftChip`, and `ShiftRightChip`
   define `main` + `elaborated` in `Proofs/Chips/<X>Chip/Defs.lean` rather than `Native/Chips/`,
   because their mains are entangled with proof-layer decomposition modules (DivRem imports
   `Proofs/Operations/DivRemOperation/{Compare,Core}` and its own `Populate`; the shifts import
   their `Core`/`Populate`/`Dispatch`/`Math`/`Flags` families). Moving the file without moving the
   decomposition would make `Native/` import `Proofs/` — worse than the exception. The public chip
   boundary (one `main`, one `Spec`, `circuit` bundle) is unaffected.

2. **Chip `Spec` locations.** The complete inventory:

   | Location | Chips |
   |---|---|
   | `FormalModel/Contracts/Chips.lean` (13) | Add, Addi, Addw, Sub, Subw, Mul, UType, Jal, Jalr, Branch, DivRem, ShiftLeft, ShiftRight |
   | `Native/Chips/<X>Chip/Defs.lean` (10) | AluX0, LoadByte, LoadHalf, LoadWord, LoadDouble, LoadX0, StoreByte, StoreHalf, StoreWord, StoreDouble |
   | `Proofs/Chips/<X>Chip/Formal.lean` (2) | Lt, Bitwise (deliberately split `Spec`s) |

   The memory/x0 chips' contract blocks (`Inputs` + `Spec`) are Native-resident; homing them onto
   the Contracts surface is the "Spec homing" backlog item (`docs/roadmap.md`) — chip `Spec`s are
   performance-sensitive (the folded-hypothesis doctrine), so the moves are deliberate, measured
   work, not a rename sweep.

3. **`Assumptions`/`ProverAssumptions` locations.** Six chips (Add, Addi, Addw, Sub, Subw, UType)
   have theirs on `FormalModel/Contracts/ChipAssumptions.lean`; the rest stay in proof files for
   one of the two structural reasons stated in that file's module docstring (hint/helper-dependent
   preconditions, or a Native-resident contract block per item 2).

4. **Two time vocabularies, one engine.** The timed grounding walk is duration-generic
   (`TimedGrounding.walkT` over a `Semantics.Timeline` — the bus clock at the start of each
   semantic step, windows at least eight ticks wide), so mixed ordinary/syscall (8/264-tick)
   walks are expressible; the ordinary walk is literally its `Timeline.ordinary` instantiation
   through the `…_ordinary` bridges (`microValueT_ordinary` down to `groundedT_ordinary`).  What
   remains deliberately dual is the *vocabulary*: the fixed eight-tick micro-time layer
   (`Model/Semantics/MicroTime.lean` — `ordinaryClkInc`/`ramEffectOffset`/`regEffectOffset`, the
   Rust `CLK_INC`/`MemoryAccessPosition` constants) is what the per-chip layers speak and prove,
   and the `Machine.SP1MachineModel.schedule` event model (`Model/Machine/Schedule.lean`) is what
   the shard-event semantics speaks; the scheduled corollary's `UsesOrdinarySchedule` hypothesis
   bridges the statement level.  The constructive `Timeline` ↔ `Machine.clockAt` bridge lands
   with the halt-row work that first exercises a non-uniform timeline.

## One instruction chip

For each supported chip, the verification chain is:

```text
native Clean main
  ├─ circuit soundness ──→ semantic chip Spec
  ├─ circuit completeness
  ├─ Sail bridge ────────→ one official try_step transition
  └─ row codec
       └─ ChipFaithful ──→ complete Rust assertions + active interactions
```

### Native circuit and contract

`Native/Chips/<Chip>/Defs.lean` owns one native row type and one `main`. It composes readers and
arithmetic gadgets as true Clean subcircuits. Public semantic meaning lives under
`FormalModel/Contracts/`; it is not a restatement of the generated constraint list.

`Proofs/Chips/<Chip>/Formal.lean`, or a focused submodule for a large chip, proves:

- soundness: satisfying the circuit entails the semantic contract; and
- completeness: the honest witness closures satisfy the circuit under the stated prover inputs.

All 25 registered instruction circuits now have closed soundness and completeness proofs.

### Sail bridge

`Proofs/Chips/<Chip>/Bridge.lean` turns the semantic contract into the corresponding behavior of the
generated LeanRV64D Sail model. `ChipKind.advance` packages the result in the uniform interface used by
the machine proof.

The bridge is conditional on concrete decoded operands and the live machine state. Those facts are
derived by the grounding engine, not assumed by the chip's row-local channel predicates.

### Whole-chip Rust faithfulness

The extractor emits:

- the exact upstream Rust row type;
- every `assertZero` expression in order; and
- every interaction expression in order.

`Faithful/ChipOracle.lean` defines an explicit bijective row-layout codec. `ChipFaithful` proves:

```text
upstream assertions hold
  ↔ native Clean component constraints hold
```

and, on accepted rows:

```text
active upstream interactions
  = active native interactions, as a multiset
```

Zero-multiplicity entries are observationally absent from both LogUp and Clean balance. Native
interactions on an unexpected fifth channel are retained in the comparison, so a proof cannot make one
disappear by checking only the four expected buses.

`Faithful/SupportedMachine.lean` contains one proof-bearing entry for every descriptor and proves that
its table tags are exactly the 25 upstream instruction tables. This is the coverage tripwire for future
pin or registry changes.

The two W3 system tables carry the same whole-table comparison in `Faithful/StateBumpChip.lean` and
`Faithful/MemoryBumpChip.lean`, against `Extracted/SystemOracle/{StateBump,MemoryBump}.lean`. Both are
flat own-assert tables with `localLength = 0`, so their native row is the chip `Inputs` and the row
codec is the input-first physical row; the `ChipFaithful` structure itself is keyed on a circuit's
*output* type map, which for these tables is `unit`, so each anchor states that structure's two
clauses directly against `⟨StateBumpChip.circuit⟩` / `⟨MemoryBumpChip.circuit⟩`. They are not part of
the 25-entry instruction coverage certificate.

## The native supported machine

The new image-authenticated assembly is `NativeCore.ensemble`: 59 tables with a computed fixed
Program ROM, ordered initial/final memory inventories, and one boot verifier. Its raw Clean
constraints and balance now prove authentic, unique initial records; canonical, unique final
locations; and ROM/Sail membership for every active Program pull. Finalizers use negative
emissions without local Memory guarantees, so their location proofs precede timed grounding.
`NativeCoreDecode` carries the actual ordinary rows and their interactions into the semantic
decoder without reconstructing another witness. Final values, mixed host effects, and a closed
local-segment soundness/completeness instance remain work in progress; see [the roadmap](roadmap.md).

The semantic target now centers on `Model/Core/ExecutionPath.lean`: arbitrary finite paths through
complete Sail/host/clock states, with split/join and an equivalent PolyFun finite-prefix view.
`ExecutionReplay.lean` threads actual host effects when reconstructing an event tape. HALT is a
real terminal transition; empty segments are identities and positive-length segments cannot resume
after HALT. `ExecutionBoot.lean` supplies the boot-to-HALT endpoint corollary. Semantic path
composition alone does not authenticate the continuity of separately certified AIR witnesses.

`MemorySnapshot.lean` supplies the finite register/RAM part of an arbitrary source boundary.
`Realizes` covers every supported byte and all 32 integer registers; the finite `equivalent` check
ignores obsolete sparse writes while detecting mutations at untouched addresses. This type does
not encode PC, platform registers, Sail bookkeeping, host state, or clock, and equality of these
snapshots is not equality of complete execution states. The new `SnapshotRegisterProvider` and
`SnapshotRamProvider` authenticate source values through fixed lookups and compose with
`OrderedMemoryProvider`; their constructors discharge internal witness conditions. Boot RAM now
specializes the same implementation. The zero-time source records are local ledger seeds, not
claims about the preceding shard's last-access timestamps. `LocalCoreSourceGrounding` derives their
timing admissibility and genesis currency; complete final-state agreement remains open. Each provider
instance uses one source snapshot; simultaneous differently bound fixed tables require distinct
export names.

`ExecutionSnapshot.lean` retains the complete boundary: every Sail register and its presence,
runtime cycle count and output, the full host state, and execution clock. Sparse RAM realizes an
exact Sail map, including absence outside the native window. `equivalent_iff` proves that finite
comparison is exactly equality of these realized execution states; no bookkeeping is reset at
a shard cut. `memorySnapshot_realizes` connects initialized full snapshots to the existing source
provider representation. `HostSnapshot.lean` reads and updates finite snapshots directly, proving
the resulting complete state agrees with the Sail host adapter. This handles full padded writes
without evaluating the dense Sail memory. These are representation and semantic execution results;
the local AIR now checks and binds the source as described below. Complete target agreement with
the reconstructed execution and host-effect integration remain open.

`LocalCore.ensemble` takes the complete `ExecutionSnapshot` as fixed instance data and installs
its projected register/RAM providers in 59 tables. It reuses `NativeCore.afterInitialTables` for
the instruction/finalizer/provider suffix. `checkExecutionSource` validates the program, supported
decoding, complete Sail register initialization and platform configuration, all source ROM bytes,
and 48-bit source PC/clock ranges. Five field equalities bind the incoming public State token to
the actual source PC/clock; their decoding theorems exclude modular aliases. All ROM bytes are
checked even when absent from the touched inventory, binding instruction fetches to source RAM.
`LocalCoreBoundaries` derives source-record authenticity, uniqueness, the exact Memory ledger, and
source/public validity from raw constraints and balance. `LocalCoreSourceGrounding` supplies the
generic timed engine's initial State truth and live-memory invariant on any trajectory beginning
at that complete source. No semantic boundary or historical source-timestamp premise is supplied.
The active ADD regression at clock 9 checks all physical assertions and balances, including
rejections for invalid configuration, missing registers, and unrelated source/public endpoints.
Full outgoing Sail/host agreement and the mixed execution walk remain open. In particular, source
validation allows an already stopped host for identity segments; the AIR must still exclude active
steps from such a source through the execution integration.

`LocalCoreFinalBoundary` obtains canonical final records and per-location uniqueness directly
from this local assembly's constraints and Byte/order balances. Its proof view keeps the physical
suffix and public final-order endpoints unchanged. `LocalCoreMemory` then gives the complete
source/interior/final Memory decomposition, signed-unit multiplicities, record permutation, and
per-location frontier equation. The source frontier is the same one used by the genesis proof.
`CoreMemoryBalance` shares the component multiplicity and boundary algebra with the boot assembly;
finalizer semantics also have one shared proof. These are algebraic and structural conclusions,
not final-value currency. The active syscall regression preserves all three register touches and
exposes the pending host binding: matching a forged HINT_LEN return in both the instruction and
final record still passes AIR checks, although finite host execution yields a different result.

`NativeCoreMemory` retains the complete physical Memory ledger after the boundary inventories,
including ordinary, refresh, HALT, and active syscall rows. Its unit-multiplicity proof turns Clean
balance into an exact message permutation and then a per-location frontier equation. The initial
frontier satisfies the generic timed engine's live-memory invariant at the configured boot state.
These results assume only raw constraints and balance (and the trajectory's initial state for the
live invariant); final-record currency still requires the mixed-row walk.

`NativeCoreRows` projects that exact ledger into one ordinary/HALT/syscall inventory, with actual
MemoryBump pairs separate. `NativeCoreRowBalance` transports balance through reordering and
per-row message permutations, then eliminates refreshes under explicit aligned-touch and timestamp
order obligations. Its `RowMemoryPermutation` interface leaves read currency points independent:
the ordinary `AlignsWith` relation's all-reads-at-start field would exclude syscall rows. The
native State argument now constructs an exhaustive mixed-row order from the same witness:
`NativeCoreState` accounts for the complete State ledger, and `StateChronology` canonicalizes and
cancels the actual StateBump rows using a layout-independent ranking proof. `NativeCoreOrder`
instantiates that proof and establishes exact 8/264-tick durations and the boot clock residue.
`NativeCoreTouches.ordered_aligned_rows` combines the order with aligned Memory touches and their
unchanged per-location balance. `NativeCoreMemoryOrder.ordered_memory_rows` discharges the local
prior-clock conditions from the produced side of Memory balance, proves strict refresh order,
and supplies full `RowOKCore` facts. This includes clock bounds on the final frontier without
assuming final-table Memory guarantees. Its `memory_refresh_free` theorem constructs the
refresh-free ledger directly from raw constraints/balance and the checked image.
`NativeCoreTransport.grounding_carrier` completes that construction with canonical State endpoints,
full structural row facts, and `WindowAligned` semantic transport. The latter permits each original
read's pre-effect offset, so syscall reads are preserved. `NativeCoreGrounding` derives the
carrier's timeline, boot truth, and genesis, and `GroundingCarrier.ground_of_steps` instantiates the
generic engine. `NativeCoreInstructionExecution` discharges ordinary row step/frame facts using
component-local chip contracts and the carrier's derived timing. `NativeCoreTrajectory` constructs
the event transcript and trajectory, proving exact event positions from the State walk and
discharging the ordinary `stepOnce` equations. `NativeCoreHaltExecution` derives HALT's code and
clock facts from the assembly; `HaltGrounding` supplies its PC-only transition and register
read-backs. The resulting `ground_of_host_steps` retains ROM preservation and active syscall
step/frame facts as its two semantic premises. Given these, the original final frontier's values
are current at the public final State time. The host wrapper fixes zero-code HALT and delegates
other calls to the supplied environment. Constraining ROM protection, connecting host effects,
and proving terminal ECALL/Exit agreement and execution reconstruction remain open.

`SyscallInputs` supplies component-local syscall contracts and source observations from constraints,
finished Byte/Program guarantees, and incoming Memory currency. The row law follows using the
Program PC bound alone: a raw next low limb above `65535` still recombines correctly, with StateBump
normalization handled separately. `NativeCoreSyscallSemantics` derives a semantic `EventStep` for
every active syscall after grounding, recovering its committed ECALL, source registers, target
PC/return value, and exact position on the constructed trajectory. This bridge consumes the host
step fact; it does not derive the selected full-code profile or host effects. In particular, the
existing three-register footprint cannot certify host RAM writes such as `HINT_READ` or WRITE's
x12 length and guest-buffer reads. Host tables and their Memory footprint must supply those before
the unconditional capstone can close.

`CoreSyscallChip` separately composes the original instruction circuit with `SyscallCodeGuard`,
a boolean-gated fixed lookup over all four limbs of the prior x5 value. Its sound/complete contract
includes the eight-code semantic profile; `constraints_profile` authenticates it from raw
constraints without any Memory guarantee. The lookup has eight concrete rows and a canonical
`FiniteLookup.ofStatic` export realization. It adds no witness columns or interactions and does
not alter the original Rust-faithfulness claim. The 59-table assembly still uses the original
syscall component; integrating the strengthened chip belongs with the remaining host work.
The [roadmap](roadmap.md#native-clean-core) records the pinned executor's extra WRITE reads and
zero-clock, untraced hint writes that this integration must address explicitly.

`Model/Core/HostExecution.lean` supplies the concrete eight-call interpreter. Its dispatcher reads
x5/x10/x11 and WRITE's x12 from a partial observation interface, reads the requested guest bytes,
and returns the next host state and complete optional memory write. The state carries both
commitment banks, hint and hook-reply queues, outputs, recorded requests, and terminal status.
`HostExecutionLaws.lean` characterizes successful observations and writes; `HostSail.lean` supplies
actual Sail observations and proves the resulting ECALL row law, endpoint agreement, memory
readback/frame, register frame, and ROM preservation. The concrete handler is indexed by the
incoming host state. Machine integration must thread the returned state between calls and add
AIR-authenticated host accesses to the grounding footprint; the existing mixed trajectory does
neither yet. Mutable commitment updates use the native historical providers described below. The
exact AIR still binds every commit in a shard to one public digest, so distinct overwrites are a
disclosed exact-completeness obstacle. Proof requests record observed digests;
they do not assert recursive proof verification.

The host's byte observations now have a computed aligned-cell interface.
`Model/Core/HostFootprint.lean` includes the full register inputs and the unique union of read and
write cells. Execution derives coverage, window bounds, and existence of this inventory;
`Soundness/HostFootprint.lean` proves canonical, distinct encoded locations. Defined word
observations suffice to replay the same host execution, fully written words have the emitted
little-endian values, and outside words are preserved. Requiring defined words is essential:
two failed optional word reads can hide different readable bytes. The pending host AIR must
authenticate these observations and written words and retain their accesses in the mixed ledger.
The semantic footprint is a minimal native cover, with the zero-length WRITE distinction from
Rust recorded in the roadmap.

`HostRamAccessChip` now supplies the local Clean RAM transfer component. The existing address
and Memory readers establish canonical aligned RAM and the old/new word pair; local clock
checks establish strict bounded time order and the effect at event time plus one. Its semantic
constructor computes the timestamp comparison columns. The actual ledger contains precisely
that Memory pair and a host coordination record with the event clock, address, and both words.
The component has an exportable witness program. It remains outside the mixed ensemble until
the call tables bind these records to the full footprint and host effects.

`HostRamReadChip` composes that access with whole-word preservation and one-or-two logical read
copies. It cancels the lower-level coordination internally and retains one physical Memory pair.
The optional copy is a separate Boolean-gated unit interaction, so Clean's count bound accounts
for it. `HostReadPlan` computes a unique physical cell list for two spans and proves that its
expanded read multiplicities equal the two requested inventories. This handles overlapping
VERIFY_SP1_PROOF buffers without duplicate simultaneous Memory accesses. Physical address
uniqueness for compiled rows explicitly requires a correctly indexed prior-record history.
The read channel exposes the provider's local canonical aligned address and word bounds; it
does not assert the word's currency in an execution. `HostRamBytes` consumes that exact key and
composes the safe limb decoder to return the eight canonical little-endian bytes. Its soundness,
constructive completeness, zero-cell witness export, and exact read/Memory ledgers are proved.
`hostRamBytes_read_of_word` connects the output to the Sail-backed host byte interface once
Memory grounding supplies the defined word. `HostReadContext.readGuest_of_cells` lifts defined
word observations to an arbitrary requested slice with explicit complete-window bounds.
`HostBuffer32` constrains a complete 32-byte window using four or five shared reads. Its constructor
computes the alignment variant and minimal cover; the semantic specification proves complete-window
bounds and the exact host byte result from grounded words. The read ledger equals that cover, and
one full buffer message carries the query, clock, and all bytes to a future call consumer. Every
variant is sound, complete, and exportable with zero witness-program cells. Binding those messages
to decoded calls and installing these reads in the mixed machine remain open.

`HostCallChip` supplies the instruction-facing handoff. It composes `CoreSyscallChip`, Clean's
full-word equality gadget, and the shared `RegisterRead` circuit. WRITE reads x12 at event time
plus one and writes back the same word; all other calls have no extra active read. Each active
row emits the actual clock, full code, arguments and return word, and the selected WRITE length.
Raw constraints determine selection, and the ledger preserves all original instruction
interactions, including PublicValues. Soundness/completeness, timestamp construction and
exportability are proved locally. Installation in the mixed carrier, matching calls to RAM
footprints, host effects, and host-state threading remain open.

`HostCommitChip` now constrains the two mutable commitment banks. Each slot component checks the
full call and return, a canonical 32-bit value (also below the field characteristic for deferred
commitments), strict clock order, and exactly one bank-slot replacement. Its PublicValues pushes
supply each call's historical value; the original instruction pulls are preserved. This native
provider interpretation permits overwrites without claiming the exact AIR's fixed public-digest
binding. The state channels contain only clock/word tuples and have no semantic guarantees.
`HostCommitHistory.ordered_history` reads the eight physical slot tables of a bank and derives
an exhaustive ordered host-interpreter fold from their local specs and actual endpoint balance.
The count bound is retained. Its explicit local-spec and initial/final-record premises are
discharged by the nine-table bank ensemble below.
Both local circuit directions, witness construction, and the host-effect bridge are closed;
regressions check actual instruction/provider ledgers and distinct repeated writes.

`HostCommitEnsemble` closes those bank-level endpoint premises. Each bank adds one terminal
component, which preserves the words and advances to the fixed clock `2^48`; this clock is only
on the private bank channel. A verifier with no witness cells pushes the zero bank and pulls
that fixed terminal state carrying the public final words. The last call timestamp stays private.
The actual nine-table ledger yields an exhaustive history from raw constraints and balance;
Byte guarantees discharge local specs. Auxiliary components must prove that they omit the bank
channel and satisfy their Byte-provider requirements. These static interface proofs are separate
from witness validity. The subsystem has not yet been installed in the mixed machine, and its
HostCall inputs still require actual instruction sources. An instance without such sources can
only have an empty call history. Regressions distinguish complete empty-ledger satisfiability
from the bank-channel and local-check tests of active histories.

`HostHaltChip` and `HostEnterChip` consume the full control-call handoff. HALT checks a canonical
exit below the host policy's field characteristic and `2^32`; ENTER returns zero and preserves
the host state. Both full-dispatch bridges use observed x5/x10/x11 and an unstopped host, and both
effects have no RAM write. HALT then prevents further host dispatch. Their physical ledgers have
no Memory or Exit interactions, so the instruction retains those contributions. Local contracts
follow from raw constraints and HALT's Byte guarantees. `HostControlPopulate` constructs handler
rows directly from successful interpreter results and derives their completeness assumptions.
The instruction's structural exit limit is specifically KoalaBear; `HostControlCompatibility`
proves it equals the native handler's full range at `SP1Prime`. This does not imply whole-core
completeness for arbitrary field characteristics. These control handlers and the mutable banks
still need installation and ordering in the mixed machine; the four remaining handlers are
WRITE, HINT_LEN, HINT_READ, and VERIFY_SP1_PROOF.

The existing released execution theorem still uses the 55-table assembly described below and
retains its explicit semantic-boundary and syscall-inactivity premises.

`Soundness/SupportedMachine.lean` is the circuit-bearing instruction registry. Each of its 25
entries carries:

- its neutral `InstructionChipId`;
- the verified Clean circuit;
- its semantic `ChipKind`;
- and the proof that the circuit contract is the registered semantic contract.

Opcode families and the `rd = x0` guard are derived from the neutral identity's pure route rather
than stored again. `InstructionChipId.all` drives the Clean table list, typed row decoder, opcode
coverage, Sail dispatch, and faithfulness coverage. Its order is a witness-format decision.

`SP1Ensemble.lean` adds 30 proof-oriented provider/boundary tables to form a 55-table Clean ensemble:
six Byte-op providers at positions 25–30, one fixed Range provider for every width `0..16` at
31–47, Program at 48, MemoryInit/MemoryFinalize at 49/50, MemoryBump and StateBump at 51/52,
Halt at 53, and SyscallInstrs at 54. The seven channels are State, Byte, Program, Memory,
Exit, Syscall, and PublicValues. `SyscallTableInactive` restricts the current soundness theorem
to inactive SyscallInstrs tables. The complete Range family is semantic, not padding: shift consumers emit widths
outside the former `8/13/14/16` subset, so that subset could not balance an honest shift trace.
These provider circuits are not asserted to be row-wise copies of the exact upstream Core system
tables. They are the small native interface used to prove the instruction execution theorem;
`Composition/ProviderSegment.lean` consumes a caller-supplied, source-backed
`CanonicalPreprocessedInventory` together with the exact memory-boundary and bump rows, and
`CoreEnsemble.lean` proves the complete 55-table local constraint system.

The redistribution does not copy Byte/Range/Program multiplicities from the exact 34-table
execution cluster. That cluster counts system/public consumers that the native 55-table slice does
not contain. Instead, transport projects the actual Clean interactions of the verifier, 25
transported instruction tables, MemoryInit/MemoryFinalize, MemoryBump, StateBump, the manufactured
padding Halt table, and the empty SyscallInstrs table into a skeleton ledger and recounts it.
The raw exact Byte/Range/Program assertion lists are empty. `CoreAIR.PreprocessedBinding` only
records the named matrix/PCS-opening premise, to be discharged by ArkLib; it proves neither
row-local meaning nor provider selection. `PreprocessedProviderContract` is the explicit caller
premise for that meaning; neither raw
projected-key uniqueness nor native-demand coverage follows from it. The
Type-valued `CanonicalPreprocessedInventory` is a caller-supplied, demand-oriented selection already
partitioned by destination provider. Each selected carrier is backed by its matching exact source
matrix, with Range backed by the matching width block, and projected-key `Nodup` is an explicit field
of that selected inventory rather than a property of the raw matrices. It may omit raw keys whose
native demand is zero. The recount contract separately requires coverage of every nonzero
Byte/Program skeleton key, nonpositive skeleton sums at selected keys, and `2 * count ≤ p`.
`freshRowsByKey` is a declarative specification and small-regression helper only; it is not used to
materialize or deduplicate the real preprocessing universe. PCS/program identity, State and Memory
balance, and the semantic boundary remain explicit contracts.
The recount discharges Byte (including Range) and Program integer balance; the downstream global
contract retains all-channel interaction-count bounds and State/Memory integer balance.

## Structural buses and semantic grounding

The five Clean channels communicate only the algebra SP1 actually constrains:

- State: timestamp and PC edges;
- Program: decoded instruction rows;
- Memory: location, timestamp, and word limbs;
- Byte: byte/range lookup messages;
- Exit: the committed exit code, as a single reduced field cell.

Local guarantees are structural. In particular, State does not claim reachability and Program does not
claim commitment merely because a message appears; Exit's local guarantee is `True`, because the
whole content of that bus is its *balance*.

### The Halt table and the Exit hand-off

The 25 instruction chips carry SP1's ordinary `try_step` semantics; SP1's own ECALL path runs
through `SyscallInstrsChip` and the global syscall tables, which the supported profile excludes. The
Halt table at position 53 is the native ensemble's explicit, auditable replacement for exactly the
`HALT` arm (`Machine.ExecutableSyscallHandler.haltOnly`): one real row per halting shard, which
pulls the pre-syscall `(clk, pc)` and pushes `(clk + 264, pc = haltPc)` on the State bus, pulls the
committed `ECALL x5, x10, x11` from the Program bus, reads `t0`/`a0`/`a1` through the standard
register-access pairs, and constrains `t0 = 0` (`SyscallCode::HALT`).

Its Exit push is what ties that row to the public statement. The state-boundary verifier pulls
`⟨exit_code⟩` **ungated**, and every physical Halt row pushes either its reduced `a0` word (when
live) or the zero code (when padding). Balance alone then forces three things, with no new premise
and no widening of the public-values record: the Halt table has exactly one physical row; an
ordinary shard's committed `exit_code` is `0`; and a halting shard's is `reduce(a0)`. That is the
dichotomy `supported_core_witness_grounding` case-splits on, and it is why the halting conclusion
needs no extra hypothesis at the capstone. The halt row additionally pins `a0`'s upper three limbs
to zero — a **disclosed 16-bit exit-code profile restriction** (ours, not upstream's: SP1 instead
bounds `op_b` to a valid field element, so its decode never wraps), without which the single committed
field cell cannot decode back to `a0`, since SP1's own reduce wraps modulo a prime below `2^32`.

The whole-machine proof derives meaning in this order:

1. `WitnessDecode.lean` deterministically recovers typed rows from all 25 physical circuit tables.
2. State balance and strict timestamp rank produce an exhaustive order of exactly the active rows.
3. Program balance and the bound provider prove that each ordered row decodes the committed program.
4. Per-location Memory balance, provider uniqueness, and timestamp ordering recover the live value for
   each register or RAM access.
5. `ChipGroundingContracts` derive each exact row's assumptions, semantic `Spec`, routing, and readiness.
6. `LocalExecution.lean` applies `ChipKind.advance` in order to construct an actual Sail chain.

The generic timed engine and every one of the 25 registry contracts are proved. The result is packaged
by `supported_core_witness_grounding` and consumed in two forms: `supported_core_native_sound`
targets the broad shard-local Sail relation, while `supported_core_native_shard_sound` constructs
the common `CoreShardSemanticWitness` target shared with completeness. Its event transcript
deterministically evaluates to an `EventExecutionTrace` in which every transition has normal
`Retire_Success` evidence and a canonical `InstructionChipId` route. This excludes routed
instructions that enter Sail's trap path but cannot produce a valid native instruction row.

The source relation keeps non-algebraic facts visible. The exact AIR/PCS integration must derive the
authenticated provider contents, their uniqueness, and their binding to the committed program and
memory boundary. Separate application contracts must supply the loader and platform facts that are
not consequences of the table AIR itself:

- the program and initial state are bound to provider rows;
- memory-provider rows are unique per location; and
- code memory is compatible with the Sail execution model.

These are not Lean axioms. They are explicit relation conjuncts, deliberately split between facts
the exact proof artifact must authenticate and facts the SP1 loader/platform integration must
establish.

The physical range bound on pulled high timestamps is deliberately *not* on that list. It used to be
a third relation conjunct, because `ChipGroundingContracts.rowAligned` took it as a premise and so
could not produce the touch lists the memory balance is built from until it was already known.
Moving it into the per-touch antecedent of that field's slot conjunct broke the cycle, and the
capstone now derives it from the produced side of its own per-location Memory balance.

## Exact upstream Core AIR

The native ensemble is a proof architecture; it is not the upstream verifier relation.

`FormalModel/CoreProfile.lean` defines the audited table enum and exact clusters. Generated
`CoreAIRManifest.lean` independently records the runtime Rust names and widths. Kernel-checked
permutation theorems connect the readable profile to that manifest.

The baseline clusters are:

- execution: 3 preprocessed tables + 25 instruction tables + 6 system tables = 34;
- memory boundary: 3 preprocessed tables + 2 memory-global tables + Global = 6.

`Faithful/CoreAIR.lean` assigns every table its exact row type and generated lists. Its relation checks:

- exact active-cluster shape;
- all row assertions;
- public-value assertions;
- exact natural interaction balance; and
- the verifying key's preprocessed commitment.

This relation is suitable as the deterministic target of a knowledge extractor. It is stronger than
the verifier's raw field equations where necessary to express an execution multiset without modular
wraparound.

## Exact AIR refinement boundary

`Soundness/CoreAIR.lean` does not pretend that listing the upstream equations proves their execution
meaning. `CoreAIRRefinementObligations` names the missing proofs, including the system-table grounding
and syscall-event cases.

Today the file exports only:

- `sp1_air_refinement_of_obligations`; and
- `sp1_air_sound_of_obligations`.

They assemble a supplied bundle into the public relation, and they are useful for fixing the intended
API. They are not the final capstone. The unqualified names remain unavailable until the bundle is
constructed from the exact relation.

The intended implementation route is:

```text
exact instruction rows
  ── 25 ChipFaithful proofs ──→ native instruction constraints/interactions

exact system rows
  ── system grounding ────────→ native provider, boundary, and syscall facts

both
  ── supported_core_native_sound + event assembly
  ──→ SP1CoreShardSemanticRelation
```

This structure reuses the closed native proof and avoids a second whole-machine execution engine.

## Syscalls and schedules

Ordinary supported instructions occupy 8 SP1 ticks. A raw Core ECALL event occupies 264 ticks.
Sail specifies the instruction but not SP1's host handler, so the eventful target is parameterized by
an explicit `SyscallHandler`.

A concrete theorem must prove the claimed handler behavior. Precompile clusters are separate verifier
targets and should be added only with their full table and handler refinements.

COMMIT-row correctness and row existence are separate:

- AIR proves the digest operand of every canonical row that occurs;
- the standard halt wrapper is a property of the verification-key-bound program and supplies
  all-eight-row coverage across the full execution.

This wrapper property is absent from the base shard and execution relations.

## Shard execution and verifier layers

`FormalModel/Execution.lean` defines an authenticated full-execution target. It includes the
public-values ledger, full-state shard stitching, global balance, deferred-proof authentication, boot,
and final HALT conditions. It is deliberately downstream of shard AIR soundness.

`FormalModel/Verifier.lean` provides relation-level composition machinery for the later ArkLib layer.
ArkLib must supply probabilistic knowledge soundness for transcript processing, LogUp/GKR, zero-check,
PCS openings, commitments, and Fiat--Shamir. The error term must survive post-composition with the
deterministic AIR refinement. Its extracted input relation is the paired
`CoreAIR.Current.ShardRelation`: one witness contains both the 34-table execution cluster and the
six-table Memory-boundary cluster. The postprocessor is a total decoder into
`Machine.CoreShardSemanticWitness`, and the exact theorem is pinned to the production `SP1Prime`.

## Completeness

Clean circuit completeness is local: honest witness closures satisfy one circuit. Whole-machine
completeness is a different theorem:

```text
supported semantic execution
  → generated native and upstream traces
  → balanced AIR witness
  → accepting cryptographic proof
```

The source is `SupportedCoreShardExecutionRelation`, the canonical witness relation also produced by
`supported_core_native_shard_sound`. The forward implementation is the total, proof-independent
`nativeTrace` function applied to `CoreShardSemanticWitness.evaluatedTrace`. It decodes and compiles all 25
instruction families, schedules Memory refreshes, derives State refreshes, creates canonical
Memory boundaries, recounts Byte/Range/Program providers from the literal Clean consumer ledger,
and stores the public boundary once.

`supported_core_native_functionalCompleteness` proves that map satisfies
`SupportedCoreNativeRelation` on `SupportedCoreNativeAdmissibleShardRelation`; its existential
projection is `supported_core_native_complete`, and
`sp1Ensemble_statement_of_supported_execution` exposes the direct Clean statement.  Admissibility
is a restriction of `SupportedCoreShardExecutionRelation` by named readiness facts for this exact
compiler output and `NativeTraceFootprint.Fits`. The semantic and native active-row counts are
both checked by `CoreProfile.WithinOrdinaryRowLimit`. It does not assume table constraints, channel
balance, or an existential generated trace.

The source is deliberately narrower than the shared capacity-bounded canonical shard relation.
The remaining compiler-domain work includes registry-wide event validity; State and Memory chronology/row-agreement
lemmas; literal-ledger Byte polarity and demand servability; initial-Memory content; Program-row
physical projection; and the actual interaction-count bound.  Deterministic representation
facts should migrate out of readiness as their agreement theorems close. Configured decode itself
has already moved to the shared `ConfiguredDecode` predicate below both directions. The remaining
implications are named exactly by `NativeShardTraceTotal`;
`supported_core_native_shard_correct_of_totality` and its public-language-equality corollary consume
only that theorem. The library does not claim unconditional public-language equality until it is
closed. The older abstract language-certificate API was removed because its map could ignore the
semantic witness and therefore did not express compiler fidelity.

## Performance discipline

Large extracted lists and circuit specifications must remain folded. Whole-chip proofs cross different
spellings through explicit rewrite lemmas rather than asking unification to unfold both sides.
`circuit_proof_start_core` is used for completeness proofs near the kernel-size cliff. The main library
forbids `skipKernelTC` and `native_decide`.

Per-declaration elaboration-budget overrides are **prohibited by default**: `scripts/check_option_escapes.sh`
fails the audit on any `maxHeartbeats`/`maxRecDepth` site not named in `scripts/option_escapes_allowlist.txt`,
each entry of which carries a measured floor bracket and the mechanism that makes it irreducible. It is a
prohibition, not a budget: it does not count sites, and it does not permit a new escape hatch in exchange
for an old one.

Hand-written Lean carries **zero** `maxHeartbeats`, matching upstream Clean, which has none in 44,603
lines; the allowlisted sites are generated definitions plus a small number of measured structural
`maxRecDepth` cases. A blowup is normally a masked `whnf` cost, so the required fix is to fold it, not to
raise a number: see [`agents/proof-patterns.md`](agents/proof-patterns.md), especially
"Compile-time / performance landmines".

The project-specific patterns are in [`agents/proof-patterns.md`](agents/proof-patterns.md); Clean's own
`doc/performance-problems.md`, `doc/proving-guide.md`, `AGENTS.md`, and `Clean/Air/README.md` remain the
upstream authority.
