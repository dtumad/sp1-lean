# Roadmap

The native 25-chip soundness theorem, every registered chip contract, and every whole-chip
faithfulness proof are closed. The current development target is a self-contained native Clean
ensemble with soundness and constructive completeness for bounded local execution segments,
including constrained inline syscalls and native shard composition. Boot-to-HALT is a corollary
obtained by fixing the first and last boundaries. Exact upstream Core refinement remains separate.

## Native Clean core

The target is equality between the raw Clean ensemble statement and a bounded local RISC-V
execution relation over checked finite inputs and complete incoming/outgoing states. Ordinary steps
use official Sail; syscalls thread the concrete host state. Boundaries account for registers, RAM,
host queues/transcript position, accumulated outputs/requests, commitment banks, terminal status,
and execution clock. Program and platform identity are fixed across the chain. Native composition
uses explicit state boundaries; succinct commitment binding belongs to later recursion work.
The native profile protects instruction bytes
against both ordinary stores and host writes. Neither direction may depend on a caller proving
provider validity, compiler readiness, syscall inactivity, or an execution-dependent totality bundle.

The selected guest-runtime profile contains eight canonical full-register syscall codes:
HALT (0), WRITE (2), ENTER_UNCONSTRAINED (3, constrained return zero), COMMIT (16),
COMMIT_DEFERRED_PROOFS (26), VERIFY_SP1_PROOF (27, recording a request), HINT_LEN (240), and
HINT_READ (241). EXIT_UNCONSTRAINED, memory-protection flushing, ELF dumping, and profiler calls
are outside this native profile. `CoreSyscallChip` composes the instruction circuit with a
sound/complete fixed lookup enforcing all four code limbs. The existing 59-table assembly still
uses the original instruction circuit; integrating the strengthened chip and constraining the
selected host effects remain open.

Implemented foundations:

- `ExecutionSnapshot.lean` represents complete Sail/host/clock boundaries with finite register
  maps and sparse RAM. Its executable comparison is proved equivalent to literal equality of
  realized execution states, including nextPC, retirement bookkeeping, runtime counters/output,
  and absent register keys. The bounded memory realization has all supported bytes present and
  every outside address absent; it is not a quotient that ignores extra Sail-memory entries.
  Boot has a proved representation, and initialized snapshots project to the existing source
  providers. Exact comparison suffices for semantic identity and composition.
  `HostSnapshot.lean` computes host transitions directly on finite data and proves soundness and
  completeness against the full-state Sail host adapter. Its byte-write proof covers all hint
  padding and preserves untouched state. Regressions reject bookkeeping, host, and untouched RAM
  mutations and derive a genuine semantic HINT_READ step from the sparse interpreter. Complete
  outgoing snapshot authentication and host-effect integration by AIR constraints remain open.
- `MemorySnapshot.lean` represents all 32 integer registers and complete sparse RAM for a local
  source boundary. Its Sail representation relation covers every supported byte; its executable
  extensional comparison checks the union of finite supports, including untouched locations,
  while ignoring obsolete writes. `SnapshotRegisterProvider` authenticates the index and all
  four value limbs against a fixed snapshot table. `SnapshotRamProvider` authenticates arbitrary
  snapshot RAM; the old boot provider specializes the same circuit. Both compose with the existing
  ordering wrapper, have proved row constructors, and export their witness programs.
- `LocalCore.ensemble` now takes the complete `ExecutionSnapshot`, projects it to the source
  providers, and binds the incoming public token to its actual PC and clock. `checkExecutionSource`
  checks complete register initialization, the existing Sail platform configuration, finite program
  validity and decoding, all ROM bytes, and 48-bit source PC/clock bounds. `LocalCoreBoundaries`
  derives source-record authenticity, uniqueness, exact physical Memory projection, and source/public
  validity from raw constraints and balance. `LocalCoreSourceGrounding` then derives initial State
  truth and the complete live-memory invariant for any trajectory beginning at that source. Local
  zero-time seed records are admissible even at a nonzero start clock; they make no historical
  last-access claim. The complete 59-table ADD regression rejects unrelated source/public endpoints,
  out-of-range sources, missing registers, invalid platform state, wrong values, broken inventories,
  and changed ROM even with no RAM rows. Full outgoing Sail/host agreement and the mixed host walk
  remain open. The boot assembly's later grounding stages still need transport to this local one.
- `LocalCoreFinalBoundary` now derives finalizer contracts, canonical addresses, unique locations,
  and the exact negative Memory ledger from the local assembly's constraints and Byte/order balance.
  `LocalCoreMemory` retains every physical interior interaction and derives signed-unit multiplicities,
  complete source-plus-push/final-plus-pull permutation, and the per-location frontier equation.
  No Memory truth, execution order, or syscall inactivity premise is used. Component multiplicity
  and boundary algebra now live in `CoreMemoryBalance`, shared with the existing boot proofs.
  A full 59-table HINT_LEN regression exercises an active syscall, all three Memory pairs, and its
  264-tick edge. At the largest 24-bit high clock, one refresh per touched register suffices; no
  earlier-epoch history is replayed. It rejects damaged inventories and unmatched result/time/value
  changes. It also records a concrete integration gap: changing the return and matching final record from 3 to 4
  remains AIR-valid while the supplied host returns 3. Stateful host-result binding is therefore
  still necessary; ledger balance alone does not imply semantic execution or final-value currency.
- `LocalCoreProgram` authenticates every active Program pull through the unique checked-image
  producer. `LocalCoreDecode` preserves physical instruction cells, constraints, and channel
  guarantees. `LocalCoreRows` projects all ordinary/HALT/syscall occurrences and actual refresh
  pairs into exact Memory balance. `LocalCoreState` derives their complete State ledger and endpoint
  balance; `LocalCoreOrder` constructs an exhaustive canonical walk with exact 8/264-tick durations
  and the incoming clock residue. No ordering or syscall-inactivity premise is supplied. These
  adapters reuse `CoreProgramBalance`, `CoreExecutionRow`, `CoreTableProjection`, the existing
  decoder, and `StateChronology`. Regressions cover reversed physical instructions with padding,
  missing/forged Program rows, and empty local segments, including a stopped source.
- The local structural grounding path is closed through `LocalCoreTouches`, `LocalCoreMemoryOrder`,
  `LocalCoreTransport`, and `LocalCoreGrounding`. It derives aligned touches, both prior clock-limb
  bounds, final clock bounds, strict refresh order, an exhaustive carrier with canonical State
  messages, and its timeline. `GroundingCarrier.ground_of_steps` derives source State/Memory truth
  internally and concludes final State truth and physical final-record value currency, conditional
  only on the original event step/frame facts for a trajectory starting at the complete source.
  The carrier's timeline starts at that source's actual clock. Shared component and rewrite proofs
  live in `CoreRowBalance`, `CoreTouches`, `CoreMemoryChronology`, and `CoreRowTransport`.
- The local verifier now freezes the clock when the source host has an exit status.
  `executionRows_nil_of_stopped` derives absence of all active ordinary/HALT/syscall rows from
  strict State ordering. This closes the reproduced active-ADD-after-HALT gap while retaining
  stopped-source identity segments. Regressions also cover three touches to the same register,
  a real 24-bit State clock carry, and the distinction between source clock range checks and the
  active CPU's 1-mod-8 clock phase. That phase belongs in the eventual shared semantic profile;
  the broader pure execution path does not impose it.
- `LocalCoreTrajectory` constructs paired Sail/host replay from the full source and the exact
  ordered event tape. Covered replay clocks match the AIR timeline. `LocalCoreInstructionExecution`
  derives all 25 ordinary chips' step/frame facts: committed decode excludes ECALL, and the
  terminal-PC invariant plus an authenticated fetch proves the actual host is running.
  `LocalCoreHaltExecution` now derives HALT's committed ECALL and register observations, its actual
  stateful host step and exit status, and its step/frame facts. Its `ground_of_host_steps` leaves
  only ROM preservation and active SyscallInstrs facts as semantic premises. The host policy's
  characteristic explicitly agrees with the AIR field. The legacy HALT row still restricts exits
  to 16 bits, below the concrete host's canonical below-characteristic, 32-bit domain.
  `replay_of_finalTruth` recovers full-tape replay success and the returned PC/clock from grounded
  final State truth; it does not assume successful replay. Regressions check complete intermediate
  states, ordinary host preservation, endpoint extension, and rejection of a real step after HALT.
- `ProtectedLocalCore.ensemble` installs all four byte-permission store wrappers and the fixed
  writable-interval provider, for 60 tables. Original row widths, assertion/lookup lists, and
  existing interaction ledgers are provably preserved. The permission constructor succeeds exactly
  for writable addresses below `2^48`; its table size depends on ROM size. Full-AIR regressions
  reject the reproduced code-writing SB and forged/missing permissions, permit a partial store
  beside ROM in the same RAM cell, and retain store padding and stopped-source identities.
  Store and provider witness programs pass exportability checks. The generic byte-frame lemma
  proves ROM preservation from allowed writes. The complete witness projection now preserves
  constraints, exact old ledgers, data, and public input; `statement_implies_local` proves refinement
  to the original local AIR. Exhaustive source classification and count-bounded balance authenticate
  every active permission request, with a physical-row interface. `ProtectedStoreFootprints` now
  identifies those requests with every byte in the committed store footprint, and
  `ProtectedLocalCoreRom` transports the result to all 25 decoded instruction kinds using physical
  provenance. `ProtectedLocalCore.ground_of_host_steps` derives ordinary ROM preservation and HALT
  internally; only active SyscallInstrs step/frame effects remain semantic premises. This strengthens
  the native immutable-code profile without changing the original SP1 chip faithfulness statements.
- `Model/Core/Execution.lean` defines complete Sail/host/clock states and deterministic mixed
  transitions, with normal Sail retirement and the concrete eight-call host interpreter. Both
  ordinary and syscall steps require a running source. `HostTerminal.lean` proves that only HALT
  creates an exit status. `ExecutionPath.lean` proves local path/segment split and join, identity,
  determinism, weighted clock accounting, and equivalence to PolyFun finite reachability. Terminal
  paths end with a real HALT; no positive-length segment can follow it. `ExecutionReplay.lean`
  reconstructs the paired trajectory from event data and authenticates every supplied host event;
  `ExecutionBoot.lean` makes boot-to-HALT a semantic endpoint corollary. These are semantic results,
  not a completed native AIR equivalence or composition theorem. The two-ECALL regression joins a
  continuing shard to a terminal shard and rejects forged host/RAM boundaries and post-HALT steps.
- `ToClean/Air/CompleteEnsemble.lean` packages both correctness directions and a proof-independent
  compiler whose success domain is proved equal to an independent execution relation.
- `ToClean/Air/EnsembleExport.lean` exports all components, verifier, channels, and fixed lookups;
  every lookup realization and channel reference is backed by a Lean proof. Lowering preserves
  constraints and interactions. Serialization and the Rust interpreter remain explicit trust boundaries.
- The Rust whole-ensemble checker validates row shapes, fixed lookups, verifier constraints,
  full-message field balance, and Clean's interaction-count bound. Its row builder executes witness
  programs for supplied table inputs. The Lean-exported fixture is regenerated in CI.
- `Model/Core/` provides checked finite program images, sparse byte-memory operations and frame
  proofs, and executable hint/output/hook-reply operations, including padding-write protection.
- Every accepted image now constructs a loaded, configured Sail initial state with zeroed integer
  registers. Its memory agrees byte-for-byte and word-for-word with the ROM-overlaid sparse image,
  including zero defaults; no boot witness is supplied by the caller.
- The sparse initial-memory table has at most `2N + 1` constant-byte intervals for `N` image entries,
  with exactly one interval covering each in-range address. Native byte and word circuits prove
  reads from this concrete fixed table. Their executable constructors supply all internal columns
  on exactly the bounded read domain, and their witness programs are exportable. Word-read
  correctness reaches the initial Sail state's memory through the public semantic contract.
- Native register/RAM providers now push authenticated zero-time records directly to the Memory
  bus, preserve the requested address, and prove canonical address encoding. Their ordered wrappers
  constrain each control key to that address plus one. A shared theorem derives per-location
  uniqueness from endpoint balance, including mixed register/RAM rows and duplicate witness rows.
  Constructors discharge the wrappers' completeness conditions; ordered RAM construction succeeds
  exactly on aligned guest cells whose key exceeds the preceding key. Both witness programs export.
- `Soundness/InitialMemoryEnsemble.lean` now registers both providers and a terminal table in a
  Clean initialization subsystem with fixed control endpoints `0` and `2^48 + 1`. Its exact
  physical ledger yields endpoint balance; local table specifications and that balance prove
  authentic boot records and uniqueness by decoded memory location. No endpoint permutation or
  provider-uniqueness premise is supplied. Auxiliary tables must omit the private control channel.
  This is a compositional subsystem theorem: the enclosing machine must still derive its local
  table specifications from constraints and channel guarantees. Generic unit-balance and physical
  transition-view adapters are isolated in `ToClean/Air/`; the fixed verifier and terminal witness
  programs export. Regressions cover empty/mixed inventories and malformed control ledgers.
- Final register/RAM providers now check canonical locations and emit one negative Memory record per row.
  `OrderedMemoryProvider` and `OrderedMemoryEnsemble` share the ordering circuit and inventory
  argument between initialization and finalization. Both subsystems prove that their decoded
  records are exactly their physical Memory interactions. The final inventory derives uniqueness
  from its own fixed control boundary and actual balance; constructors discharge internal gadget
  conditions on a stated register/RAM domain. Regressions reject forged addresses, unrelated keys,
  duplicate/disconnected final rows, and mismatched values or clocks in paired boundary ledgers.
  Both finalizer witness programs export. Negative emissions assume no local Memory guarantee:
  `FinalSpec` now records canonical location only. Value/clock bounds and final-state meaning
  belong to the enclosing machine's timed-grounding conclusion.
- The executable instruction decoder now builds complete fixed Program messages from the finite
  image. Successful parses are proved to be exact ECALL or part of the existing routed instruction
  image; projection accepts exactly the parser's domain. The bounded input checker rejects any
  unsupported ROM entry and is independent of the AIR field. Computed rows preserve full addresses
  in the native window and satisfy Program-channel range guarantees. Provider constructors discharge
  the complete lookup and range assumptions, and their witness program exports. Regressions cover
  all 51 supported SP1 opcode projections, immediate/reserved-bit cases, and forged messages even at
  zero multiplicity. `SailDecode.instructionDecode_agrees` now proves agreement with official Sail
  for every accepted word and every configured state, covering 62 integer instruction variants and
  exact ECALL. The parser rejects the ADD/ORI encodings that the pinned Sail configuration claims
  for enabled Zihintntl/Zicbop hints; other `rd = x0` cases remain supported. Those aliases need
  semantic hint bridges before they can join the exact-decoder profile.
  `DecodedProgramProvider.spec_committed` derives actual ROM/Sail membership directly from the
  fixed provider's contract and finite-image validation, without a caller-supplied decoder certificate.
  Its `constraints_committed` companion derives that meaning from each physical row's raw fixed-table
  constraints, without a provider-validity or channel-balance premise.
  The 25 instruction circuits and faithfulness anchors are unchanged.
- `Soundness/NativeCoreEnsemble.lean` now combines all 25 instruction tables, the computed fixed
  Program table, both ordered memory inventories, and the existing Byte/Range/bump/Halt/syscall
  tables in one 59-table assembly. Its verifier fixes boot PC/time and both private ordering
  boundaries. The generic `ToClean/Air/ChannelClosure.lean` theorem closes Byte/Program directly
  from component requirements and the actual ledger; the older positional closure proof now uses
  this same helper. `NativeCoreBoundaries.lean` derives initial-record authenticity and location
  uniqueness, their exact physical Memory projection, public boot fields, and physical Program-row
  ROM/Sail membership. No caller supplies initial-provider validity or uniqueness. Regressions
  exercise the composed verifier, both inventories, forged boot fields, and noncanonical clocks.
  This assembly still contains the legacy Halt table, including its padding behavior; it is not
  yet certified as a boot-to-HALT machine.
- `NativeCoreFinalBoundary.lean` derives final-record canonicity and location uniqueness directly
  from the combined constraints, Byte closure, and private-channel balance. Its exact ledger
  projection retains the original records, including every value and timestamp, without assuming
  Memory guarantees. `NativeCoreProgram.program_pull_committed` proves that every active Program
  pull, including ECALL, names an instruction in the checked image and official Sail decoder.
  The fixed ROM is the only possible non-pull contributor; Clean's count-bounded balance supplies
  a matching complete payload. No Program-truth premise or instruction case is exposed to callers.
  `NativeCoreDecode.instructionRows_program_committed` transports that result to every active
  ordinary decoded row; the same adapter preserves its raw constraints and channel interactions.
- `NativeCoreMemory.memory_frontier_balance` derives the exact per-location Memory equation
  from the complete physical ledger and the two authenticated inventories. The interior retains
  ordinary instructions, refreshes, HALT, and active syscalls; constraints prove all Memory
  multiplicities are signed units or zero. `memoryInitialFrontier_liveOK` supplies the generic
  timed engine's genesis invariant for any trajectory starting at the configured image state.
  Neither theorem assumes Memory guarantees, semantic boundary facts, or syscall inactivity.
- `NativeCoreRows.executionRows_memory_balance` now connects that ledger to one mixed carrier
  containing every active ordinary, HALT, and syscall row. The projection preserves complete
  messages and duplicate occurrences; actual MemoryBump pairs are the only remaining side terms.
  `NativeCoreRowBalance.memory_refresh_free_of_chronology` eliminates those pairs after an
  exhaustive row ordering, per-row message permutations, aligned `RowOKCore` touch shape, and
  strict refresh timestamp order are supplied. Its interface preserves syscall read times instead
  of imposing ordinary rows' all-reads-at-start restriction. These are internal chronology seams,
  not new premises added to the native AIR relation.
- `NativeCoreTouches.ordered_aligned_rows` now derives an exhaustive State order and aligned
  Memory rows directly from the combined constraints/balance and a checked image. The State
  proof cancels actual StateBump rows internally and retains all active ordinary, HALT, and
  syscall occurrences. `ordered_rows_timing` proves exact 8/264-tick durations and the boot clock
  residue; `AlignedFacts` preserves State/fetch and complete Memory multisets while proving touch
  windows, per-location chains, and push-clock bounds.
- `NativeCoreMemoryOrder.ordered_memory_rows` derives both prior clock-limb bounds, final-frontier
  clock bounds, and strict order for every actual MemoryBump pair from the produced side of the
  balanced ledger. Execution writes lie before the bounded public final clock; refresh writes
  carry Byte-checked limbs; initial records have time zero. The resulting `MemoryChronology`
  supplies every aligned row's full `RowOKCore`. `memory_refresh_free` now constructs the
  refresh-free ledger from the checked image and raw constraints/balance, with no caller-supplied
  prior bounds or refresh order. It preserves all row occurrences, read times, pushed records,
  and prior/final values and locations; rewritten prior/final timestamps can only move earlier.
- `NativeCoreTransport.grounding_carrier` now constructs the final canonical, refresh-free mixed
  carrier with full `RowOKCore`, an exhaustive State walk, and both ledger balances. Its
  `WindowAligned` transport retains the original pre-effect read windows, including syscall
  offsets, and moves step/frame proofs across rewrites and State re-limbing. The generic
  `Timeline.ofDurations`/`rowTimeline` constructions derive successor timing from State edges.
  `NativeCoreGrounding.GroundingCarrier.ground_of_steps` connects this carrier to the grounding
  engine, deriving boot truth and genesis internally. Its remaining semantic premises are the
  original event rows' step/frame facts on the selected trajectory. Given those, it recovers
  final-state truth and the original physical frontier's values at the public final State time;
  it does not claim original refresh timestamps precede that time.
- `NativeCoreInstructionExecution.GroundingCarrier.instruction_engineFacts` derives step/frame
  facts for all 25 ordinary chips from the new assembly. Their wiring, assumptions, routing,
  and readiness contracts are component-local; the older witness-facing APIs remain proved
  specializations. The derived carrier timeline supplies each ordinary successor position.
  `GroundingCarrier.ground_of_system_steps` reduces the generic grounding premise to HALT and
  syscall step/frame facts, an ordinary `stepOnce` trajectory equation, and ROM preservation.
- `NativeCoreTrajectory` constructs the mixed transcript and its trajectory from the carrier's
  ordered physical events. The State walk identifies each event's exact list position, so ordinary
  successor equations follow internally. `NativeCoreHaltExecution` derives HALT's zero code from
  its own assertions and its clock bounds from Byte closure; `HaltGrounding` proves the PC park
  and all three register read-backs on that trajectory. `GroundingCarrier.ground_of_host_steps`
  retains only ROM preservation and active syscall step/frame facts as semantic premises.
  The host's zero-code arm is fixed to canonical HALT; other host behavior stays supplied by the
  environment. These are grounding results: terminal ECALL/Exit agreement and a full execution
  theorem for this assembly remain open.
- `SyscallInputs` derives the syscall contract, operand bounds, and source observations from a
  component's constraints and Byte/Program ledgers plus incoming Memory currency. The new row-law
  proof needs only the Program input PC bound; it permits a raw next low limb above `65535`.
  `NativeCoreSyscallSemantics.GroundingCarrier.syscall_eventStep_of_grounded` connects every active
  syscall in the mixed carrier to a semantic `EventStep` for the supplied host. Event position,
  committed ECALL, all three source registers, and the target PC/return register are derived
  internally. This is a post-grounding bridge: host step/frame facts remain open, as do the eight
  full-code restrictions and host RAM effects. The instruction row's three register touches cannot
  account for `HINT_READ` writes; those need host tables and a corresponding grounding footprint.
- `Model/Core/SyscallCode.lean` defines the eight-call full-word profile and its proved parser.
  `SyscallCodeGuard` enforces membership through a concrete fixed table, with a boolean active
  gate and unrestricted padding codes. `CoreSyscallChip` composes this guard with the original
  instruction chip, retaining its complete contract and adding no witness columns or channel
  interactions. `constraints_profile` derives the restriction directly from raw constraints,
  before Memory grounding. Regressions evaluate the actual assertions and finite lookup, reject
  upper-word aliases and nonboolean gates, and check the whole-chip lookup wiring and exportability.
  The original Rust-faithfulness anchor is unchanged. This is a component result; the strengthened
  chip has not yet replaced the original syscall component in the 59-table assembly.
- `Model/Core/HostExecution.lean` now executes all eight selected calls from observed registers
  and memory, threading hints, request-bound hook replies, both commitment banks, output bytes,
  recorded proof requests, and terminal state. `HostExecutionLaws.lean` proves exact dispatch,
  byte-observation, and padded-write conditions. `HostSail.lean` applies these effects to official
  Sail states and proves instruction row laws, endpoint observations, register/memory frames,
  written-byte readback, and ROM preservation. `HostState.step_sound` gives a committed ECALL
  transition for the concrete one-step handler. Regressions cover all eight calls, rejection paths,
  actual Sail updates, and successive hint/output/HALT calls sharing host state and memory.
  This closes the executable host semantics component. `LocalCoreTrajectory` now threads that
  host state through replay; authenticating the extra observations and effects with AIR tables
  remains open.
- `Model/Core/MemorySpan.lean` and `HostFootprint.lean` compute the complete register/cell
  inventory from host execution. It retains WRITE's x12, all requested buffer bytes, and every
  padded write byte; overlapping buffers share cells. Successful execution yields the footprint,
  guest-window bounds, and distinct canonical encoded Memory locations. Agreement on those
  observations reproduces the entire host result and effects. `Soundness/HostFootprint.lean`
  derives this agreement from defined Memory-bus words, proves preservation of outside RAM
  cells, and identifies each fully written post-state word with its little-endian host bytes.
  Regressions cover overlap, unaligned and empty reads, padding words, observed-byte changes,
  and the counterexample showing that equal failed word reads do not authenticate their bytes.
  These close local semantic bridges for the host access tables.
- `Model/Core/HintQueue.lean` now gives an executable persistent representation of complete
  hint bytes. Zero is empty; allocated nodes have smaller tail pointers. Source encoding,
  byte-exact decoding, deterministic meaning, preservation of all historical nodes, pops, and
  exact allocation counts are proved. Local node validity and a bounded root imply a complete
  finite queue. `HostQueue.lean` derives updates from every successful eight-call host execution,
  including guest prepends and ordered, request-bound hook replies. `hintLength?_of_run` observes
  the current represented queue; no static-source-queue assumption is introduced. Regressions
  follow changing lengths through all eight calls, empty-hint padding, preserved historical heads,
  and malformed pointers; equal lengths with different bytes remain distinguishable.
  `HintQueueRecords` now encodes pointers in three bounded 16-bit limbs. Its fixed source table
  authenticates node metadata against actual source hints and rejects oversized inventories.
  `HostHintLengthChip` constrains the current head, exact return, strict queue-clock advance,
  and full HostCall handoff; both routes export 122 computed witness cells. Its full host bridge
  uses explicit current-queue/node binding, while successful dispatch derives the constructor's
  completeness domain under pointer and clock bounds. Source and handler ledgers are proved.
  Joint regressions reject forged returns/metadata, false empty claims, malformed records, and
  stale clocks, and retain empty hints and historical source heads. The queue cursor now retains
  a separate allocation frontier after pops, including at an empty head, and HINT_LEN preserves it.
  `HintNodeAllocate` checks a fresh successor without 48-bit wrap, the old-head link, and bounded
  length; its byte-parametric extension theorem preserves every historical node. Its circuit
  exports 212 computed witness cells. `HintQueuePrepend` compiles any ordered prefix with all local
  contracts, exact row count, cursor continuity, and full endpoint representation under one
  capacity bound. Regressions reject historical identity reuse, carries that overflow, malformed
  fields, reordered/dropped/duplicated allocations, and forged frontier endpoints. A separate
  regression records that identical node metadata cannot authenticate different equal-length bytes.
  These are component results; allocation does not yet publish a node or a host-authorized transition.
  `HintQueueWords` now gives the exact padded word contents and proves that complete word coverage
  plus authenticated length determines every byte. The word values are exactly the semantic RAM
  write, including its mandatory final word. `HintQueueWordSource` authenticates original contents
  through a fixed source lookup, with no incoming byte premise and zero witness cells; its exact
  ledger is proved. Positions beyond the 48-bit key range are omitted, never aliased. Permitted
  native-window writes derive the needed position bound. `HintNodeWords` binds generated contents
  to the checked fresh allocation identity. Regressions reject same-length content changes,
  wrong keys, missing/forged padding, and length changes hidden by zero padding. Historical source
  words remain usable; new nodes correctly fail the source lookup until separately authorized.
  `HintReadSpan` now checks the exact positive padded word count and last written RAM address,
  including valid writes ending at `2^48`. It composes a proved native division-by-eight circuit
  and existing bounded adders; aligned permitted writes construct its completeness domain.
  The word ledger also authenticates the actual final-word marker. A bounded final word derives
  the node's true length below `2^64`, closing the metadata's modulo-length ambiguity without
  restricting unrelated source hints. `HintReadSpan.Spec.node_end` binds the checked span to that
  exact node extent. Regressions cover carries, the address ceiling, forged endpoints and markers,
  and the fact that a wrapped length word alone can pass the span while miscounting actual bytes.
  `HintReadWordChip` now composes the physical RAM transfer and exact word-index successor,
  pulling the immutable word and permission for every written byte, including padding. Its
  265-cell witness program and all non-Byte ledgers are proved. `HintReadCoverage` derives an
  exhaustive consecutive inventory from the actual two consumer tables and cursor balance,
  preserving the call clock and node identity; a constructed walk gives the converse balance.
  A checked span derives the constructor's successor bounds. Executed regressions retain row
  reordering and final-cell writes and reject omissions, repetitions, wrong clocks, forged
  contents/end markers, and missing or read-only padding permissions.
  `HostHintReadChip` now checks the complete call, current head, padded span, and final-word
  request. It pops the queue to the authenticated tail, preserves the allocation frontier, and
  emits both real word-cursor endpoints. Its 302-cell witness program is exportable. The host
  bridge derives the true natural length and complete padded-write request from authenticated
  records, permissions, and register observations; successful semantic dispatch constructs all
  arithmetic columns under store/clock capacity bounds. `HostHintReadCoverage` derives the exact
  actual-node word inventory using those physical handler endpoints and consumer-table balance.
  Executed checks join the instruction handoff, handler, fixed sources, RAM consumers, and
  permissions; they reject incomplete words, forged final contents, and altered queue boundaries.
  `HostHintReadWrites.run_of_tables` now combines the full host call with exact padded word-write
  agreement. Consumer word authentication derives every destination address, with no repeated
  cell; the actual Memory projection agrees with the semantic byte update. Authenticating each
  actual byte-permission pull permits the entire padded span. A regression shows why checking
  only the handler's final word is insufficient: swapped consumer markers can balance the cursor
  while repeating an address. Each consumer's immutable source rejects that substitution.
  `HostHintReadPartition` now derives per-call balance from one shared physical cursor ledger
  and unique handler clocks. Selection preserves all original row cells, data, and interactions;
  strict word-index progress also proves that no consumer can lack a handler. Its combined
  execution theorem uses this shared ledger directly. Executed checks cover interleaved calls,
  reversed rows, clock carries, and missing handlers/consumers. Duplicating complete calls still
  balances the cursor, so the handler-clock uniqueness premise is necessary here.
  `LocalCoreEventUniqueness.lean` now derives distinct incoming clocks for all active ordinary,
  HALT, and syscall occurrences from actual local constraints and balance, with arbitrary shard
  endpoints. `HostCallLedger.lean` derives binary activity from raw wrapper constraints and proves
  complete typed call permutation from the actual padded handoff ledger.
  `LocalCore.OrderingChannels` now isolates State balance and Byte guarantees from full Memory
  balance. The 60-table prefix of `HostLocalCore.ensemble` installs the HostCall wrapper at the
  actual syscall position and retains the protected stores, permission provider, complete source,
  verifier, and public input; host components are appended. Its physical projection proves the
  original constraints, Byte guarantees, exact State ledger, and active syscall inventory.
  `HostLocalCore.executionRows_ordered` and `hostCalls_clocks_nodup` follow from the extended
  ensemble's own constraints and balance. Auxiliary components prove their Byte requirements and
  CPU State silence statically; the real HINT_READ handler and both RAM consumer variants satisfy
  that interface. No projected Byte or Memory balance is required or claimed.
  `HostLocalHandoff.calls_perm` now derives complete instruction/handler call permutation from
  the actual physical receiver registry and this ensemble's own balance. `ReceiverView` provides
  the generic heterogeneous reader; `LocalCoreChannels` and `HostLocalCoreLedger` prove the
  complete retained-table inventory silent on HostCall. The implemented registry contains HALT,
  ENTER, all 16 commitment variants, both HINT_LEN variants, and HINT_READ, with proved static
  chronology interfaces and word-resource silence. `handler_clocks_nodup_of_registered` and
  `balanced_for_of_registered` remove the caller's handoff inventory/accounting equations.
  WRITE and VERIFY handlers remain unimplemented; the registry does not claim their completeness.
  Regressions cover padding, clock carries, duplicate/forged handoffs, and the installed WRITE
  projection: the same closing Memory frontier balances the wrapper but fails after dropping
  its x12 pair, despite unchanged State edges and valid original constraints.
  `HostHintReadLocal.ensemble` now fixes the handler and both actual word tables, automatically
  declares all installed host channels, and derives shared cursor balance, alignment, and selected-call
  balance from its own ledger. Static cursor silence excludes other handlers/resources; local
  word specifications and strict progress exclude orphan consumers. The 83-table regression checks
  reversed multi-call rows, clock carries, missing handlers/words, and orphan consumers.
  `HostLocalCorePermissions` proves the retained fixed image provider is the sole permission source
  when host auxiliaries are unit consumers. The real word consumers satisfy that condition.
  `HostHintReadLocalPermissions.run_of_witness` therefore derives dispatch and exact padded writes
  without separate handoff/cursor accounting or per-byte permissions. Installed permission tests cover
  the final RAM cell, a missing provider row, padding into ROM, and forged provider rows: cursor
  balance can survive the ROM write, but valid permission constraints and balance cannot.
  Automatic channel registration retains repeated channel records. This is harmless for Lean's
  balance predicate but does not meet `EnsembleExport.channels_unique`; before exporting this
  extended assembly, construct a canonical inventory and prove that it retains every channel.
  Deduplicating by name alone is insufficient without proving that equal names identify equal
  channel records, including their requirements and guarantees.
  `HostHintReadLocalRecords` now authenticates all actual node/word pulls, including canonical
  encodings, from complete ledger balance and physical source authentication. Fixed source tables
  close that authentication from snapshot bytes. The physical-table interface permits dynamic
  allocation proofs to use earlier grounding facts; the stronger raw-component interface alone
  would not suffice for those providers. `handler_spec` follows from this interface and AIR;
  `word_spec` isolates the remaining actual Memory-channel guarantees. The 85-table regression
  rejects missing source rows and changed fixed bytes, and a separate regression shows that equal
  semantic length words need not have canonical encodings.
  `HostHintReadLocalExecution.current_records` now restricts persistent-store bindings to each
  call's current allocation frontier: its current head bounds the node, and the balanced cursor
  path forces every selected word to use that node. `run_of_authenticated_witness` derives the
  local specifications and individual record bindings internally, proving concrete dispatch and
  the complete padded write inventory. It still requires current queue truth, extension into an
  authenticated persistent store, actual Memory representation guarantees, and current register
  observations. The future-node regression preserves record balance and valid source bytes while
  the actual cursor rejects words borrowed from a later, byte-identical node.
  `HostQueueOrder` now proves an exhaustive path through the actual HINT_READ and both HINT_LEN
  tables. `HostHintReadLocalQueue` derives their complete queue ledger and specifications from the
  installed AIR. `source_queue_rows_nil` proves the old fixed-source registration without endpoints
  cannot have active queue handlers under full constraints and balance. The new
  `HostHintQueueBoundary.ensemble` installs one endpoint pair in the actual verifier; generic
  `ClosedVerifier` transport derives a singleton representation preserving every constraint and
  channel balance. The source cursor binds to the incoming snapshot's hints. `source_queue_ordered`
  now closes the exhaustive token-path theorem from full constraints and balance without separate
  endpoint or authentication premises. The final cursor is fixed by the ensemble instance, and
  semantic final-byte binding is not yet proved. Installed subsystem regressions check duplicate
  chains, forged heads/frontiers, and zero-event identities; they are not full-AIR witnesses.
  **Next:** propagate semantic head truth along the physical path and bind the final cursor to the
  outgoing snapshot. Extend ordering to authenticated WRITE/hook allocation edges; the current
  three-handler theorem requires the other resources to be queue-silent. Preserve identity segments
  and use the already-required active 1-mod-8 clock profile; range-only source validation permits
  zero, while an active queue handler requires a positive clock. This is part of the shared compiler
  profile obligation, not a new reason to exclude zero-step segments.
  Then install RAM rows in mixed grounding, including Memory guarantees, predecessor currency,
  and full outgoing Memory agreement. New WRITE/hook node and word authorization and semantic
  head history remain open. Include the 48-bit
  identity bound in the shared resource profile.
  The full-AIR forged HINT_LEN return regression remains open until that integration.

- `HostRamAccessChip` is a sound and complete native Clean component for one aligned RAM word
  transfer. It composes the existing address and Memory gadgets, checks both high clocks locally,
  and proves strict prior/new time order and an effect at event time plus one. Its constructor
  derives the timestamp selector and gap columns from bounded, strictly ordered records. Exact
  ledger theorems retain the prior/new Memory pair and a coordination record containing the event
  clock, address, and both words. Its witness program is exportable. Regressions cover both clock
  branches, the final RAM cell, and malformed addresses, values, and clocks, including field
  underflow aliases. This component is not yet registered in the mixed ensemble. Call tables
  must still select the complete footprint, authorize values, and retain these accesses in
  the physical mixed ledger.

- `HostRamReadChip` now shares one physical read between one or two logical buffer consumers.
  Whole-word equality prevents writes, the lower-level access coordination cancels internally,
  and the actual Memory ledger retains exactly one prior/new pair. Separate unit-weight read
  pushes preserve Clean's interaction-count bound. `HostReadPlan.logical_cells_perm` proves
  that distinct physical cells with computed sharing bits recover both requested span inventories
  exactly, including overlapping VERIFY_SP1_PROOF buffers and empty WRITEs. The constructor
  proves local completeness from earlier bounded records; physical address uniqueness additionally
  requires that the supplied history is indexed by its actual cell, which is explicit in the
  theorem. Executed regressions balance compiled rows against both buffer inventories and reject
  wrong sharing, words, clocks, missing rows, writes and corrupted witnesses. The 201-cell witness
  program is exportable. Call-bound buffer coverage and installation in the
  mixed Memory ledger remain open; these fixture requests are not authenticated host calls.

- `HostRamBytes` now consumes a shared read and returns its eight canonical little-endian bytes
  through a sound/complete native Clean circuit. It reuses the safe limb decoder and adds zero
  witness-program cells or physical Memory accesses. The read channel carries only locally proved
  canonical word/address bounds; global currency remains a Memory-grounding conclusion.
  The exact decoder ledger preserves the full clock/address/value key, and its semantic bridge
  reaches the Sail-backed host read interface once that Memory word is grounded. The reusable
  `HostReadContext.readGuest_of_cells` theorem authenticates arbitrary byte slices from defined
  covering words and complete guest-window bounds, including empty and unaligned reads.
  Executed regressions check output order, joint shared-read ledgers, malformed byte columns and
  channel guarantees, wrong full-message keys, and missing bytes or out-of-window span tails.
  `HostBuffer32` supplies the complete fixed-size consumer described below; binding its query and
  payload to the decoded call and proving whole-machine host reads remain open.

- `HostBuffer32.circuit` is sound and complete for a full 32-byte guest-memory window. Its
  constructor computes the alignment variant, all four or five covering addresses, low-byte
  columns, and the payload from the query and canonical RAM words. The semantic theorem hides
  alignment cases: it states full-window bounds, exact read keys, and agreement with the host byte
  interface once the consumed words are grounded. Its consumed address list is the minimal ordered
  cover and is duplicate-free. Exact ledger theorems retain one shared read per covering word and
  one complete buffer message, with no extra physical Memory access. All eight variants export with
  zero witness-program cells. Executed regressions cover alignment, limb carries, upper/lower window
  limits, altered messages and covering cells, and two overlapping buffers served by seven distinct
  physical reads. The buffer channel carries local bounds only; Memory currency remains a grounding
  conclusion. The next step is a VERIFY_SP1_PROOF consumer that binds both full buffer messages to
  the decoded call and the host state transition. The buffer components are not yet registered in
  the mixed ensemble.

- `HostCallChip` composes the full-code-checked instruction with an internally computed WRITE
  selector, x12 read-back at event time plus one, and one gated host-call message carrying all
  four limbs of the code, arguments, return word and WRITE length. Raw constraints determine
  the selector; exact ledger theorems retain the new Memory pair and every original interaction
  on State, Program, Exit, Syscall and PublicValues. Non-WRITE calls emit zero length and no
  extra active Memory access. The sound/complete circuit and its semantic timestamp constructor
  are closed and exportable; complete-row regressions cover all eight calls, padding, invalid
  prior reads and corrupted selectors. This closes the local instruction-to-host handoff.
  It does not select RAM records, constrain returned host values/effects, or thread host state.
  The component and x12 touch still need installation in the mixed ensemble and grounding carrier.

- `HostCommitChip` supplies native COMMIT and COMMIT_DEFERRED updates for both eight-slot banks.
  Its sixteen routed components constrain the full call, canonical value bounds, strict bounded
  clock order, and a single-slot replacement; the semantic constructor computes all comparison
  and byte columns. Soundness/completeness and the exact host-interpreter effect are proved.
  The actual ledger consumes the handoff, replaces the bank state, and supplies historical
  PublicValues records matching the preserved instruction pulls. `HostCommitHistory.ordered_history`
  derives an exhaustive ordered interpreter fold from physical bank tables, their local specs,
  and endpoint balance including Clean's count bound. Joint-row regressions cover every slot,
  distinct overwrites, invalid clocks/values/witnesses, and rejected forks or missing updates;
  the witness programs export 186 cells. Native bank history does not require every intermediate
  value to equal the final digest. The composable bank ensemble below now authenticates its
  endpoints and derives local specs. Installing it and the handoff in the mixed machine remains open.

- `HostCommitBoundary` closes a bank at a fixed private-channel clock beyond all ordinary call
  times, preserving all eight words. Its terminal has 48 computed witness cells; its verifier
  fixes zero genesis and the public final words without allocating witnesses or publishing the
  last call timestamp. `HostCommitBank` registers eight slot tables plus that terminal.
  `HostCommitEnsemble.sound` derives an exhaustive host-interpreter history from the composable
  ensemble's raw constraints and actual balance, including Byte closure and the count guard.
  Its only auxiliary proof parameters are static bank-channel exclusion and Byte-provider
  requirements; no row-local spec, initial/final record, ordering or boundary-truth premise is
  supplied by the caller. Physical-table regressions cover empty banks, repeated writes,
  interleaved slots, missing/duplicate terminals, forged genesis, wrong public outputs, and invalid
  terminal clocks.
  This is a bank subsystem, not yet the mixed RISC-V ensemble. Calls and other host state/effects
  still need coordination there. In particular, with no auxiliary call sources this subsystem
  admits only empty call histories; no active-call non-vacuity claim is made for that configuration.

- `HostHaltChip` and `HostEnterChip` now constrain HALT and constrained-replay ENTER. Their complete
  dispatch bridges take matched x5/x10/x11 observations and an unstopped host, and prove the return
  value and absence of RAM writes; HALT records the exit and prevents further dispatch.
  The handlers consume HostCall records without adding another Exit or Memory contribution.
  `HostControlPopulate` constructs both rows from successful interpreter results and derives all
  local completeness assumptions. The faithful instruction's KoalaBear exit bound and the
  handler's canonical range are proved equivalent at `SP1Prime` in `HostControlCompatibility`;
  a generic handler proof is not an arbitrary-field whole-core completeness claim. Regressions
  cover exits through `SP1Prime - 1`, unrestricted unused arguments, forged handoffs, corrupted
  witnesses, full interpreter effects, and constructor clocks crossing 24-bit limb boundaries.
  Witness export uses 64 cells for HALT and zero for ENTER. Installation in the mixed machine
  remains open, together with the two remaining handler components: WRITE and
  VERIFY_SP1_PROOF. HINT_LEN's component and explicit queue obligations are described above.
  The host-row tests establish local checks and joint handoff balance, not a complete boot-to-HALT
  witness.

Host integration must account for these source-backed details in v6.4.0:

- `WRITE` takes its descriptor and pointer from x10/x11, but reads the byte count from **x12** and
  the output bytes from RAM (`crates/core/executor/src/minimal/write.rs`). The instruction row's
  x5/x10/x11 footprint cannot authenticate either extra input. Host tables must bind the x12
  read and the addressed buffer, including unaligned byte slices; supplying an arbitrary byte
  transcript or treating x11 as the length would change the semantics.
  The native footprint uses the minimal cell cover of the requested bytes. For an unaligned
  zero-length WRITE it is empty, whereas Rust's `(head + nbytes).div_ceil(8)` may still read a
  word. No equality with that untraced physical read inventory is claimed.
- `HINT_READ` writes a final padded eight-byte word even for zero or eight-byte-aligned lengths
  (`minimal/hint.rs`). The existing `HostIO` model preserves that footprint. The executor's
  `ContextMemory::mw_hint` writes without tracing and resets the cell's clock to zero
  (`crates/core/jit/src/context.rs`). Native authenticated host writes need an explicit timeline
  and ROM-protection argument; they cannot be admitted as additional authenticated boot records.
  Correspondence with those exact Rust timestamp conventions remains separate refinement work.
- The executor mutates commitment slots, but `SyscallInstrsChip::eval_commit` checks every COMMIT
  or COMMIT_DEFERRED_PROOFS row in a shard against one fixed public-values digest. Distinct overwrites of
  the same slot cannot both satisfy that binding. The native host model keeps mutable slots;
  its successful runs do not automatically satisfy the exact AIR's `PublicValueBinding`.
  Native `HostCommitChip` providers now preserve and match those pulls with historical records,
  while a separate state ledger proves mutable bank updates. This is a native interpretation,
  not a proof of exact `PublicValueBinding`; exact completeness still needs an explicit
  compatibility restriction or a different refinement target.
- The minimal executor treats COMMIT_DEFERRED_PROOFS and VERIFY_SP1_PROOF as no-ops; traced replay
  records deferred commitments (`vm/syscall/deferred.rs`). The native profile records canonical
  deferred values and the two observed 32-byte proof-request digests. Recording such a request
  asserts no recursive proof acceptance. These native observables and constrained replay's
  ENTER_UNCONSTRAINED return zero are explicit profile choices.

Still required before the native capstone can be claimed:

1. Finish complete boundary agreement. The full source is now the local ensemble parameter;
   configuration, initialization, ROM, PC/clock binding, and the authentic genesis State/Memory
   invariant follow from raw AIR constraints and balance. Exact finite state comparison, boot
   representation, and sparse host execution are also proved. Bind the complete outgoing Sail/host
   state, including untouched locations and bookkeeping, to the reconstructed execution. Retain
   boot initialization as a specialization. Source validation permits stopped host states for empty
   identity segments; the stopped-source verifier condition and strict State ordering now exclude
   every active instruction and syscall row after HALT.
2. Derive the remaining system execution facts for the local assembly.
   The structural path is now transported: complete source genesis, Program authentication,
   both unique Memory frontiers and their exact balance, exhaustive State ordering, aligned touches,
   prior bounds, strict refresh order, canonical carrier, and derived timeline are closed.
   `LocalCoreTrajectory` now instantiates the paired trajectory through `Model/Core/ExecutionReplay`,
   threading the actual host state and authenticating its covered clocks. Ordinary step/frame facts
   are derived through the registered component contracts, with running/non-ECALL guards discharged
   from incoming State truth. `LocalCoreHaltExecution.ground_of_host_steps` also derives the real
   HALT host transition and status, leaving ROM preservation and active SyscallInstrs semantic
   facts; final State truth supplies successful full-tape replay and the returned PC/clock.
   Widen the legacy HALT row's 16-bit exit domain when integrating the full syscall/Exit path.
   The 60-table `ProtectedLocalCore` witness now projects to the original local assembly with
   preserved constraints and balance. Every active permission request is authenticated from
   the fixed provider and connected to its decoded store's semantic byte footprint.
   `ProtectedLocalCore.ground_of_host_steps` now derives ordinary ROM preservation through the
   registered row effects and includes stateful HALT, leaving active SyscallInstrs effects explicit.
   The persistent hint-queue compiler covers all eight semantic calls. Fixed record providers,
   HINT_LEN/HINT_READ handlers, and verifier-owned queue endpoints now have an installed token-path
   theorem. Authenticate new nodes and derive head history, including WRITE/hook prepends and
   HINT_READ pops with their complete bytes, then bind the final cursor to the outgoing snapshot.
   Parameterize the bank subsystem's currently zero genesis with the complete local source
   commitment/deferred values before installing it in arbitrary continuation shards.
   Constrain actual host effects, including WRITE's x12/buffer reads and HINT_READ's padded RAM
   writes; the latter must use the same byte-permission interface. Terminal ECALL/Exit agreement and complete
   execution reconstruction, including ordinary normal retirement, remain open. No unconditional
   local execution theorem is claimed.
3. Integrate the paired semantic replay with the mixed carrier, the full-code-checked
   syscall chip and host effects into the AIR and mixed timed grounding. Ordinary ROM-write
   exclusion is already integrated through `ProtectedLocalCore`. Extending the Memory footprint must preserve host accesses
   in the balanced ledger rather than projecting back to the instruction-only footprint.
4. Prove the event compiler total on shared semantic resource bounds; construct all native tables
   and close soundness and completeness for the same arbitrary local-segment domain. Prove
   erasure of inactive padding and architectural preservation by administrative rows, including
   the zero-step case; keep semantic steps, weighted clock cost, and table height distinct. Make
   the active source clock phase explicit alongside ranges and capacity, while preserving identities.
5. Lift semantic split/join to certified native shards through complete boundary continuity.
   Prove identity, associativity, split/recompile, and composition across host effects. Derive
   boot prefixes and single-/multi-shard boot-to-HALT corollaries. Each shard has its own resource
   bound; the composed path need not fit in one shard.
6. Export event routing and provider-assembly recipes and instantiate the generic exporter for the
   complete native core. The current Rust `build_rows` API consumes assembled inputs; it is not yet
   the planned event-tape compiler.

The reusable correctness bundle is not yet instantiated for this core. No new unconditional
RISC-V/AIR equivalence is claimed. Keep the current audited Clean/Lean/Sail pins; public Clean main
does not yet supply the prover-data agreement fix or remove these native obligations. Cryptographic
proving, ELF authentication, host implementation correctness, and recursive proof verification are
separate adapters or workstreams.

## Capstone integration and review

The [pinned leanerVM comparison](leanervm-comparison.md) supports targeted fixes and small
simplifications during this capstone. Shared graph/ensemble APIs and binary-field bus work are
follow-ups; the comparison does not change the theorem target or authorize dependency updates.

The consolidation branch, `dtumad/core-verification-capstone`, already contains all eight
predecessor PRs. Preserve that history and implement the remaining work as reviewable commits;
there is no need to replay or merge the predecessors individually.

The public API will instantiate `CompleteEnsemble` and `EnsembleCompiler` for the same independent
bounded local-segment relation. Checked inputs and semantic resource limits determine the instance;
public outputs have canonical bounded encodings. Give the exported core a concrete `SP1Prime`
specialization while retaining generic underlying proofs. Both directions must close without a
decoder certificate, semantic boundary binding, provider-validity premise, syscall-inactivity
premise, or compiler-totality bundle supplied by the caller.

Integration proceeds through decoder agreement, authenticated Program and memory boundaries,
constrained host effects and mixed-row grounding, then constructive completeness and event-tape
export. In particular, the current syscall frame's unchanged-memory premise must be replaced by
precise host-memory footprints. ROM protection includes ordinary stores and hint padding. The new
core uses the syscall HALT path as its sole Exit contributor, with SP1's canonical field-valued exit
range rather than the legacy Halt table's 16-bit restriction. External hook and recursive-proof
requests remain transcript interactions, not claims that their implementations are verified.

Publication is gated on the closed theorem, the complete core export, and the final audit. Before
opening the combined PR, construct joint compiled local shards whose composition reaches HALT from
boot, with memory and host effects across the cuts. Compare complete Lean/Rust trace assembly,
retain all instruction dump-conformance gates,
and review the propositions and trust boundaries themselves. Finish with clean build/test/lint,
regeneration, axiom-audit, and fresh-build CI results. Align the maintained documentation around the
actual theorem, remove obsolete scaffolding and plan-number vocabulary with consumer checks, and
preserve provenance and review attribution. The combined PR will link the eight predecessors;
merging into `main` remains a later review decision.

Exact upstream Core refinement, authenticated succinct boundary commitments, and cryptographic
verifier soundness remain separate follow-on workstreams. Native shard composition is part of
this capstone. Historical exact-Core sequencing below does not override
the native capstone's current priority or authorize a dependency re-pin.

## Current checkpoint

Completed:

- 25 native instruction circuits with soundness and completeness;
- 25 Sail bridges and `ChipKind.advance` registrations;
- 25 whole-chip `ChipFaithful` proofs;
- a kernel-checked 25-table oracle-column-size ↔ independent-manifest `mainWidth` battery;
- deterministic typed row decoding and exhaustive ranked State ordering, with the public
  `supported_core_native_grounding` endpoint retaining final-State and memory-finalize truth;
- Program and Memory timed grounding for the native 55-table ensemble;
- `supported_core_native_sound`;
- `supported_core_native_shard_sound` into the shared proof-free
  `CoreShardSemanticWitness`, with deterministic event evaluation, normal-retirement evidence, and
  canonical 25-chip routing on every transition;
- neutral `InstructionChipId`/`InstructionRouting`/`ProviderTableId` registries shared by native
  ensemble construction, completeness assembly, decoding, and transport;
- one Model-layer `SP1TransitionView` shared literally by the ordinary semantic relation,
  soundness construction, chronological compiler, and Program agreement proof;
- the paired exact `CoreAIR.Current.ShardRelation`, containing the list-level 34-table execution and
  6-table Memory-boundary witnesses together;
- constructive exact-row assembly of all 55 native tables plus the verifier row, with local
  constraints proved from valid clusters, a caller-supplied `CanonicalPreprocessedInventory`, and
  named preprocessing, memory-boundary, and public-limb transport contracts;
- a hand-assembled one-instruction semantic trace record whose physical rows are circuit-generated,
  carried through native AIR soundness to Sail for any supplied model satisfying
  `UsesOrdinarySchedule`;
- honest COMMIT-row versus wrapper-coverage separation;
- **halting shards**: the native `HaltChip` table at ensemble position 53, the fifth (Exit) channel
  whose ungated verifier pull forces exactly one halt row and binds the committed `exit_code`, the
  committed-fragment Program re-base with its per-chip fetch discriminant, the halted grounding
  certificate, and the plain-Sail `OrdinaryRun`/`HaltedRun` dichotomy — plus the single-shard
  boot→halt corollary `supported_core_boot_to_halt_single_shard`; and
- zero main-library proof deferrals or project axioms.

Not completed:

- a closed `CoreAIRRefinementObligations` value;
- exact upstream system-table grounding;
- **the compiler's terminal halt row** — the deterministic completeness compiler still emits only
  the padding Halt row (`Occurrence .halt := Empty`, `NativeTraceReady.exitZero`), so the
  totality-conditional correctness and language-equality statements remain relative to
  `SupportedCoreNativeOrdinaryShardRelation`, and `SupportedCoreBootHaltRelation` has no
  constructed inhabitant; this is a possible bounded extension of the current checkpoint;
- cross-shard boot-to-halt soundness (the single-shard corollary above is not ledger composition);
- concrete syscall-handler refinements beyond `ExecutableSyscallHandler.haltOnly`;
- ArkLib verifier knowledge soundness; and
- `NativeShardTraceTotal`, the residual implications from the shared bounded semantic
  relation to `NativeTraceReady` and `NativeTraceFootprint.Fits`; and
- the exact-upstream reconfiguration theorem relating this native compiler output to Rust's full
  Core trace.

## P0: close exact Core AIR soundness

The final exact-v6.4.0 theorem in this phase is concrete at SP1's KoalaBear field. The native
instruction/grounding library remains generic, but the extracted `Global`/`SyscallInstrs` and
public-value curve-seed assertions contain KoalaBear-canonical literals; generalizing that exact
system layer would require a separate literal-interpretation theorem.

### 1. Transport all instruction tables

Build one registry-driven adapter from exact Rust instruction traces to the native instruction slice.
For each physical upstream row:

- use the chip's bijective row codec;
- use `ChipFaithful.constraints` to transport local validity;
- use `ChipFaithful.interactions` to transport the active interaction multiset; and
- preserve exact natural multiplicity counts when rows are concatenated.

The adapter must consume `supportedChipFaithfulness`, so adding or removing a Core instruction table
creates an explicit coverage failure. Do not write 25 unrelated top-level dispatch lists.

Deliverable: a theorem that projects the exact 25 instruction tables into the instruction part of a
valid native witness, with assertion and bus-balance transport proved once at the registry layer.

**Status (2026-08-22): the instruction-table transport and its access aggregation are delivered.**
`SP1Clean/Composition/` proves the transport once over an
arbitrary codec/oracle/`ChipFaithful` triple — no chip is named, so the 25 instantiations cannot
drift apart — and `extracted_instructionTables_constraints` runs it against the real extracted
relation: a witness satisfying `CoreAIR.Current.Relation` yields 25 native Clean tables satisfying their whole
circuits' constraint systems. `transported_map_component` shows those tables *are* `sp1Tables`, by
`rfl`; `transportedInstructionActiveAccesses_perm` appends the 25 per-table interaction
permutations into one ordered active ledger. `Composition/Balance.lean` carries the
extracted ℕ-exact balance to a zero signed-ℤ sum per payload under an explicit `SmallMultiplicities`
premise (`ZMod.val` and the centred `signedVal` diverge above `p / 2`; this is the multiplicity bound
the interaction-argument extractor must supply anyway). The former payload→native-key closure was
retired as unused: it balanced the full exact cluster, not the reduced native ensemble whose
Byte/Range/Program providers are recounted. `CoreArtifact` therefore keeps the remaining native
State/Memory/Exit integer balance as an explicit integration contract.

The current instantiation remains 25 generated citations of the generic theorems rather than a fold
over `supportedChipFaithfulness`; adding a Core table is still caught by the separately proved exact
profile/coverage equalities, but not by the aggregate theorem's own type. The remaining balance work
is no longer in the instruction segment: it is the provider/public-boundary redistribution described
below.

### 2. Ground preprocessed and system tables

> **Upstream drift, measured 2026-08-19 — read before sequencing this.** SP1's internal line has
> replaced the global-accumulation memory architecture with a Merkle-tree one: relative to our
> `v6.4.0` pin, `RiscvAir` drops `Global`, `MemoryGlobalInit`, `MemoryGlobalFinal`,
> `PageProtGlobalInit`, `PageProtGlobalFinal` and all four `Syscall*` tables, and gains
> `MerkleTreeTraversal`, `LeafHash`, `LeafHashControl`, `HintRead`, `HintReadControl`; six
> `InteractionKind` variants go with them. **The 25 instruction chips and their four buses are
> untouched**, so P0 §1 and everything under it is unaffected. But several bullets below —
> `Global`'s boundary/cumulative facts, the syscall tables, and the page-prot boundary — are
> grounding work aimed at tables that upstream is retiring. Sequence accordingly: prefer the
> bullets that survive the redesign (Program/Byte/Range/MemoryLocal/MemoryBump/StateBump), and
> treat the `Global`/syscall/page-prot grounding as pinned-to-v6.4.0 work that a future re-pin
> will re-derive rather than reuse. Details and evidence:
> `docs/agents/extraction.md` § "Upstream architecture drift".
>
> **Decision, 2026-08-28 (supersedes the 2026-08-20 "stay pinned, keep two layers" stance).** The
> unification campaign targets the Merkle-tree architecture as the core semantics and retires the
> native-vs-exact split; the grounding bullets below that aim at the retired
> `Global`/syscall-transcript/page-prot tables are **not scheduled** — they are recorded for the
> v6.4.0 claim only. Measured baseline, sequencing, and the open pin-base decision (the Merkle
> architecture is still private-only; public `v6.5.0` carries no AIR change):
> `docs/audits/2026-08-unification-target-architecture.md`. Statement-clarity and
> model-expansion work (plain-Sail conclusion, boundary restructure, real memory boundary,
> time-model unification, HALT handler, public-values widening by
> `exit_code`/`is_execution_shard`/`committed_value_digest`) is architecture-stable and proceeds
> immediately; the re-pin and the one-ensemble re-base execute when the Merkle architecture
> reaches a public release, unless the owner opts to pin a committed `sp1-private` revision.

Prove the semantic facts currently supplied to `SupportedCoreNativeRelation` from the exact upstream
tables:

- Program: the decoded Program-provider messages. Note that all three raw exact preprocessing
  tables — Byte, Range, and Program — carry *empty* assertion lists. C1 `PreprocessedBinding`
  (C1–C3 are the named cryptographic trust boundaries of `docs/verification-report.md`) only records
  the matrix/PCS-opening premise to be discharged by ArkLib. Row-local meaning therefore
  remains a separate caller premise, and the Program discharge additionally needs a (still unbuilt) correspondence
  between the committed decoded-operand encoding and the native `GuestProgram`/`ext_decode`
  decode, not through table constraints;
- Byte and Range: lookup-provider coverage;
- MemoryLocal and MemoryBump: per-location access order and timestamp differences;
- StateBump: State ordering across sparse clock ranges;
- Global: the public boundary and cumulative interaction facts;
- MemoryGlobalInit/Finalize: initial/final memory values and per-location uniqueness. Two
  qualifications from the 2026-08 audit: (a) value-truth at addresses the program image/ROM also
  pins is constrained by *no* Core system table — upstream it comes from the verifying key's
  `initial_global_cumulative_sum` binding, i.e. the C1/C3 layer; (b) the uniqueness premises are
  stated per 8-byte `locOf` cell while the upstream control chain (indexed control messages +
  `prev_addr < addr` + PublicValues endpoint anchors) orders exact byte addresses with no
  alignment constraint, so the discharge additionally needs an alignment/consumability argument
  or a per-address premise restatement; and
- SyscallCore/SyscallInstrs: raw syscall transcript consistency.

This work should target the existing `InitialBoundaryFacts` and event structures. Extend those
contracts only when the exact upstream AIR proves a materially stronger fact that is needed by
correctness. The pulled-timestamp `< 2^24` range fact is **not** on this list any more: it is
derived natively from the per-location Memory balance (`SP1Clean/Soundness/AIR.lean`), so the
upstream discharge inherits it rather than having to reprove it.

**Status (2026-08-22): local provider/system transport and full native assembly under named
transport contracts are delivered.**
`PreprocessedProviders.lean`, `MemoryBoundary.lean`, `SystemTables.lean`, and
`ProviderSegment.lean` constructs all 28 native provider tables from valid exact-cluster witnesses,
a caller-supplied `CanonicalPreprocessedInventory`, and named per-row preprocessing and
memory-boundary contracts, and proves their local constraints.
`CoreEnsemble.lean` appends them to the 25 transported instruction tables; its separate public-limb
contract projects the exact public boundary and justifies the native verifier row, yielding complete local
`EnsembleWitness.Constraints`. `CoreArtifact.lean` is the stable consumer-facing endpoint: the
caller-supplied recount contract derives Byte (including Range) and Program integer balance;
`ExactNativeGlobalContract` retains all-channel interaction-count bounds, State/Memory integer
balance, and `SemanticBoundaryBinding`. From the two, the library derives
`SupportedCoreNativeRelation` and an official-Sail local execution for any supplied model satisfying
`UsesOrdinarySchedule`. The
provider family is six Byte-op tables, all 17 Range widths `0..16`, Program, MemoryInit,
MemoryFinalize, MemoryBump, and StateBump. The complete Range family closes honest shift-row balance;
the former four-width subset omitted live shift lookup keys.

**Local system-table semantics update (2026-08-25).**
`Composition/CoreSystemSemantics.lean` now exposes the exact native inputs of MemoryBump and
StateBump and audited views for SyscallCore, SyscallInstrs, and MemoryLocal. `Channels.SyscallMsg` is
the one nine-field carrier used by the exact SyscallCore receive and SyscallInstrs send; their
generated table byte remains the send multiplicity. MemoryLocal names typed initial/final Memory
messages. The exact-list membership theorems expose those three endpoints without copying either
generated interaction list into a second hand-written ledger. SyscallCore and MemoryLocal retain iff
theorems for their complete local assertions, and exact-relation corollaries fan those facts out to
every physical row through the generic `CoreAIR.System.localValid_of_relationFor` eliminator.

This is local progress on five of the six Core system tables, not closure of their trace semantics.
Syscall transcript consistency, Memory range/order consequences, both bump ordering arguments, and
Global's public-boundary/cumulative meaning remain explicit obligations.

Byte/Range/Program multiplicities are now recounted from the actual Clean interaction ledger of the
verifier, 25 transported instruction tables, MemoryInit/MemoryFinalize, and both bumps instead of
copied from the full 34-table exact cluster, which includes system/public consumers absent here.
The raw exact Byte/Range/Program assertion lists are empty. `CoreAIR.PreprocessedBinding` only
records the named matrix/PCS-opening premise, to be discharged by ArkLib; it proves neither
row-local meaning nor provider selection. `PreprocessedProviderContract` is the explicit caller
premise for row-local semantics. Source main multiplicities are not reused and
raw projected keys are not assumed unique. The caller-supplied
`CanonicalPreprocessedInventory` selects matching-block source-backed carriers and explicitly carries
projected-key `Nodup`; it may omit raw keys with zero native demand. The recount contract separately
keeps nonzero Byte/Program-key coverage, skeleton nonpositivity, and `2 * count ≤ p` explicit.
`freshRowsByKey` is declarative/regression-only, not the inventory construction path. PCS/program
identity, State and Memory balance, and `SemanticBoundaryBinding` also remain explicit. The
exact/native table access permutations remain available; there is no joint inhabitance anchor for
that contract and valid exact clusters. The open proof must also cross the deliberately named
Range13-quotient→Range16 and raw `Global`→typed-Memory transformations; neither is a literal
interaction permutation.

The main correctness risks to audit are:

- no modular-wrap inference where natural ordering is required;
- no inference of provider uniqueness from ordinary channel balance alone;
- no inference that equal PC/timestamp endpoints imply equal complete Sail states;
- no silent use of the memory-boundary cluster as an execution cluster; and
- no transition constraint omitted by the list extractor on a future Rust pin.

### 3. Assemble ordinary and syscall events

The final shard decoder must preserve physical execution order and the mixed schedule:

- ordinary supported rows: one real Sail step and 8 ticks;
- raw ECALL rows: one `CoreSyscallEvent` and 264 ticks;
- boundary shards: no execution trace and unchanged PC/timestamp.

Keep `SyscallHandler` as the narrow host-semantics interface. Initially model only the syscall behavior
required for baseline Core soundness and the standard halt path. Add precompile handlers only with the
corresponding complete table clusters and semantic refinements.

Do not derive COMMIT-row existence from `SyscallInstrs` or a rolling public flag. AIR proves only the
operand of a row that exists.

### 4. Construct the exact refinement bundle

Instantiate every field of `CoreAIRRefinementObligations` from the preceding theorems and narrowly
stated external contracts. Keep those two sources visibly separate: AIR-derived table facts belong in
the exact refinement, while loader/platform/handler/code-memory contracts must remain an explicit
public theorem parameter or source-relation restriction. They must not disappear inside an
unqualified “AIR-only” bundle. Then publish:

```lean
sp1_air_refinement
sp1_air_sound
```

At that point the `_of_obligations` declarations may remain as internal composition helpers.

Acceptance criteria:

- source is exactly the paired `CoreAIR.Current.ShardRelation binds`;
- target is `SP1CoreShardSemanticRelation`;
- the map is a total deterministic function of statement and AIR witness;
- no field simply restates the final target as an assumption;
- the proof consumes the 34 execution-cluster and six Memory-boundary tables from the one paired
  witness, using each cluster only under its own authenticated relation;
- the audit remains `sorryAx`-free.

## P1: compose shards from boot to HALT

Prove a separate `sp1_execution_sound` against `SP1ExecutionRelation`.

Required inputs:

- the authenticated public-values ledger;
- verification-key/program consistency;
- full Sail-state continuity between consecutive execution shards;
- valid non-execution boundary shards;
- global cumulative-sum balance;
- deferred-proof digest authentication;
- boot reachability of the first execution state; and
- a final HALT with the public exit code.

PC and timestamp continuity are necessary but insufficient; the composition proof must carry the
complete machine state.

Public-output coverage remains an optional strengthening:

1. prove `UsesStandardHaltWrapper` for the exact committed standard guest, or
   `CommitCoveringVerifyingKey` for the verification key;
2. derive all-eight `CompleteCommitCoverage`;
3. use the row-to-flag and rolling-digest continuity theorems to derive
   `CompleteCommitDigestMatches` for the terminal public digest; and
4. add output-byte and hashing semantics before calling the result full public-output authentication.

Add deferred-COMMIT coverage only if a downstream theorem needs it.

## P2: ArkLib verifier integration

Pin the Core verifier target and prove:

- executable Lean/Rust verifier agreement on structured proofs;
- transcript and Fiat--Shamir refinement;
- LogUp/GKR knowledge soundness;
- zero-check and PCS knowledge soundness;
- commitment and preprocessed-trace binding;
- extraction of exact natural interaction multiplicities with bounds;
- construction/authentication of a matching-block source-backed `CanonicalPreprocessedInventory`,
  including projected-key `Nodup`, plus native-skeleton coverage/nonpositivity and canonical capacity
  for the Byte/Range/Program recount — without identifying full-cluster counts with the smaller
  native consumer universe; and
- a composed probabilistic `sp1_verifier_sound` with an explicit failure probability.

Compressed, Plonk, and Groth16 are separate targets. Do not broaden the Core theorem implicitly.

## P3: extractable witness generation and completeness

All 25 instruction chips generate their witnesses through Clean's exportable witness IR, and the
connection to SP1's Rust `generate_trace` exists today at **conformance strength**: the exported
wire-format programs + symbolic row maps (`export/witgen/`), the committed SP1 trace dumps
(`export/sp1dump/`), the fail-closed generation-time gate (`scripts/witgenExport.lean --testdata` —
every event row of every chip recomputed and matched cell-for-cell against SP1's real prover
output), and the independent Rust reference-interpreter differential (`rust/witgen-interp`, which
also reconstructs the full Rust rows and checks all extracted constraints on them).

The remaining P3 target is upgrading that sampled conformance to **proved construction**:

- generate every native instruction and provider row from supported execution events;
- prove row constraints and all channel balances;
- reconfigure the native trace to the exact upstream trace; and
- prove proof-system completeness separately.

The source relation must express supported, trace-generatable executions and concrete syscall handler
behavior. The conformance pipeline remains the empirical regression layer during this work but is not
a substitute for the theorem.

**Status (2026-08-25): deterministic all-table native completeness is closed on the explicit
admissible compiler image, and both directions now use one capacity-bounded semantic language.
Closing the transparent compiler-admissibility totality theorem remains open.**

W4 built `ToClean/Air/TableBuild.lean` and local completeness tables for all 25 instruction chips,
the 30 provider/boundary tables, and the verifier row.  W5 now adds the semantic construction:

- `InstructionEvent.lean` implements all 25 instruction-family projections;
- `TransitionView.lean` hoists fetch/decode/route and the attempted access plan into the one
  proof-free view consumed by both directions; access failure stays explicit instead of narrowing
  the semantic relation;
- `ExecutionCompiler.lean` folds the common witness's deterministically evaluated
  `Machine.EventExecutionTrace` chronologically;
- its structural totality theorem proves the fold adds no failure after one-row readiness, and the
  semantic specialization discharges outer fetch/decode/image/route projection directly from
  `SupportedCoreShardExecutionValid`;
- the shared field-free scheduler inserts register `MemoryBump` rows at timestamp-window crossings,
  while `stateBumpEvents` derives State refreshes;
- `MemoryHistory.lean` constructs the canonical initial/final record per touched location;
- `CanonicalClosure.lean` constructs Byte, Range, and Program providers from the trace's own literal
  Clean ledger; direct field balance removes the old `2 * multiplicity <= p` restriction; and
- `nativeTrace` deterministically assembles the exact 55-table witness and verifier boundary with
  no proof argument and no instruction padding.

`supported_core_native_functionalCompleteness`
(`SP1Clean/Soundness/NativeCompleteness.lean`) maps that trace into the unchanged
`SupportedCoreNativeRelation`.  Its source,
`SupportedCoreNativeAdmissibleShardRelation`, is the canonical bounded shard relation plus the named
compiler/readiness facts for its evaluated trace and the actual five-channel interaction footprint
`< p` (the remaining two channels are silent). The semantic and native row counts both feed the one
`CoreProfile.WithinOrdinaryRowLimit` policy. Constraints, channel balance, public equality, and the
semantic boundary are conclusions.  `supported_core_native_complete` is its existential form and
`sp1Ensemble_statement_of_supported_execution` is the direct Clean statement theorem.

The old abstract language-certificate API was removed: it permitted a witness map that ignored the
semantic execution and therefore could not establish compiler fidelity.  The concrete compiler now
retains each `LocatedTransition` beside its generated routed event and access schedule.

What P3 still means:

- prove access-plan success (especially complete source/target eight-byte RAM cells), then
  `Execution.NativeCompilerReady`—including every generated event's rich per-chip `Valid`
  contract—from every supported official Sail transition, rather than restricting the source;
- discharge the remaining State/Memory chronology and physical-row agreement fields from the
  deterministic compiler, including canonical addresses and initial Memory content;
- derive literal-ledger Byte polarity and Byte/Program demand servability instead of carrying them
  as broad closure assumptions;
- close the remaining Program-row physical projection (configured-state decode is already the
  shared `ConfiguredDecode` fact carried by each supported semantic transition); and
- derive the emitted interaction footprint from the Core row budget and table arities.

These implications are collected exactly by `NativeShardTraceTotal`. Capacity alignment
is closed: `supported_core_native_shard_sound` and
`supported_core_native_shard_functionalCompleteness` use the same bounded native/semantic relation
pair, and `supported_core_native_shard_correct_of_totality` plus its language-equality corollary need
only that one theorem. Until it is proved no unconditional public-language equality is claimed.
Reconfiguration to the exact upstream trace and cryptographic proof-system completeness remain
separate workstreams.

## Maintenance gates

Every phase ends with:

```bash
lake build SP1Clean
lake test
lake lint
scripts/run_audit.sh
```

On an SP1 pin change:

- compare the unmodified Rust machine source first;
- regenerate the runtime table/width/public-value manifest;
- re-audit first/last/transition selector use;
- regenerate every list anchor, the SP1 trace dumps, and the gated fixtures;
- update both semantic and extractor provenance;
- prove the 25-table coverage permutation again; and
- treat a cluster, width, interaction-kind, or schedule change as an architecture change, not a
  mechanical version bump.

On a Sail model re-pin: never hand-edit generated Lean. Update the pins in
`scripts/sail-config/generate_lean_rv64d.sh`, run `--stock` until byte-identical against the new
opencompl base, then `--sp1` and audit that the base diff is still exactly the four
platform-value sites the two-key config sets (PMP-off is a Lean-side hypothesis, not a
generated-model edit); publish + tag + pin, and refresh the pin rows in `release-audit.md`. Full procedure:
`docs/agents/sail-model-provenance.md` (expect `Model/SailMemory.lean` + `Proofs/Sail/` proof
churn from the base move itself).

## Cleanup / polish backlog (non-blocking)

Deferred quality/perf TODOs — none gate the VM theorem; pick up opportunistically. The
how-to-golf-safely rules live in `docs/agents/proof-patterns.md` § "Golf & cleanup discipline"
and § "Compile-time / performance landmines". Those project rules override generic mathlib cleanup
advice where Clean's folded terms, public audit declarations, or source-stable theorem statements
are involved.

- **`linter.style.longLine`** — the one remaining syntactic linter not yet enabled (the last
  candidate noted in AGENTS.md § Linters). Current fallout, lines over 100 **codepoints** in
  hand-written code: `Proofs/` 2965, `Native/` 1122, `Soundness/` 798, `Faithful/` 546,
  `Model/` 511, `FormalModel/` 317, `SP1CleanTest/` 30, `Math/` 13 — **6,302 lines across 311
  files**. (An earlier note quoted ~1080; that figure covered only `Native/` + `FormalModel/`.
  **Measure with codepoints, not bytes** — `awk 'length($0)>100'` counts bytes and over-reports by
  ~15% on this tree, whose docstrings are unicode-dense; the linter counts codepoints.) Enable it alone
  on the core pillar lake libraries, then reflow or per-file-suppress back to zero warnings.
  Heavy, mechanical. Reflowing is done opportunistically by the cleanup campaign, but the flag is
  deliberately **not** enabled there — flipping it is a separate, deliberate change.
- **Shift proof decomposition** — if the repeated `cpuA/msb*/aluA` tail becomes a real bottleneck,
  extract named evidence and prove the semantic result in a circuit-independent file, following the
  DivRem `Cases.lean` boundary. Do not recreate the retired DivRem `SpecObligation`/shared-tail
  architecture.
- **`/decompose-proof` candidates** — long proof bodies worth splitting into named sub-lemmas:
  `ShiftLeftChip`/`ShiftRightChip` `Formal.lean` `completeness`, `LoadHalfChip`'s 4-way `h_sel_lt`
  offset-selection case-bash, `BranchChip` `soundness`/`completeness`. Several are perf-tuned —
  decompose with care and watch elaboration time.
- **SailState-staging bridge preamble** — the `hpc_get`/`key`/`hsp_config` preamble recurs across
  ~10 store/jal/load `Bridge.lean` files → a shared lemma. Re-examine the shape first; upstream
  #101/#102 rewrote several bridges.
- **Namespace-isolate the auto-gen (linter hardening, Option B)** — the `sp1Lint` exclusion is a
  *soft* module-path filter. A hard boundary would relocate all auto-gen to a separate root
  namespace `SP1Extracted.*` so the stock `runLinter` excludes it by construction. Cost: ~87 module
  renames + import edits + `update_extracted.py` writer paths + lakefile globs. Not worth it for
  linting alone.
- **Spec homing** — move the ten Native-resident chip contract blocks (`Inputs` + `Spec` +
  `Assumptions` for AluX0 and the load/store chips; inventory table in `docs/architecture.md`
  § deliberate layering exceptions) onto `FormalModel/Contracts/`. Chip `Spec`s are
  perf-sensitive (folded-hypothesis doctrine) and the moves rebuild the heaviest proof families —
  measure per chip, one at a time. Lt/Bitwise's split `Spec`s are deliberate and stay.
- **Re-run `scripts/profile_compile.sh` after a suspected performance regression** — keep the
  generated report as a review artifact for the affected change; point-in-time timing output is not
  maintained as evergreen repository documentation.
- **Unify the two time models** — the engine half is DONE (2026-08-28): the timed grounding walk
  is duration-generic (`TimedGrounding.walkT` over `Semantics.Timeline`), mixed 8/264-tick walks
  are expressible, and the ordinary walk is its `Timeline.ordinary` instantiation with every
  carrier converted by a proved `…_ordinary` bridge — no chip or exported statement changed.
  The HALT row has since landed **without** needing the non-uniform timeline: the halted branch
  splits the halt edge out *before* the walk (the ordinary eight-tick walk runs on the instruction
  prefix, ending at the halt row's own pre-syscall pull), so the `264` window is arithmetic at the
  boundary rather than a mixed-duration walk. Remaining: the constructive
  `Timeline` ↔ `Machine.clockAt` bridge, and a genuinely mixed timeline if a future profile needs
  interleaved syscalls; see `docs/architecture.md` § deliberate layering exceptions item 4.
- **Fold more platform facts into the generation config** — `memory.regions`,
  `htif_tohost_base`, and `memory.physaddr_bits` are also config-driven upstream, so the SP1 PMA
  region (base `2^16`, size `2^48 − 2^16`) and HTIF-off could become *generated* values instead
  of `SailConfigured` hypotheses, shrinking the boot-predicate trust surface. Deliberately
  deferred: it perturbs generated output well beyond the six current sites (PMA/HTIF constants
  feed many proofs) — a measured proof-churn event, not a config tweak.

Explicitly rejected, with reasons: a *global* eval-map `eX` lemma (saves ~1 line/helper while
re-churning ~36 clean files at form-variation risk); a global `NeZero p` instance (would make the
pervasive `omit [Fact (2 ^ 17 < p)] in` clauses illegal — an owner decision, not a drive-by);
elaboration-budget directives as a speedup lever (the *wrong* lever — fold the blowup instead); and
the `unusedArguments` / `docBlame` / `docBlameThm` / `tacticDocs` environment linters.
