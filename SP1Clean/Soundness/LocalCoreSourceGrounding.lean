import SP1Clean.Soundness.LocalCoreBoundaries
import SP1Clean.Soundness.GenericWalk
import SP1Clean.Soundness.TypedState

/-! # Grounding genesis from the checked complete local source

The combined AIR checks the source's platform configuration, ROM, and actual incoming PC/clock.
Its physical source records supply the initial memory frontier. These results initialize the
generic timed engine on any trajectory beginning at that source, including a continuation at a
nonzero clock. A source record's zero timestamp is a local seed, not a claim about its last access
in an earlier shard. The mixed execution walk and complete outgoing boundary remain separate work.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The physical verifier's incoming State message names the complete source's actual time and PC. -/
theorem source_state_encoding_of_byte {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ witness.allTables, table.ChannelGuarantees byteChannel.toRaw) :
    StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput) = source.clock ∧
      StateMsg.pcBits (initialBoundaryStateMessage witness.publicInput) = source.pc := by
  have checked := public_contract_of_byte witness constraints (bytes _ witness.mem_allTables_verifierTable)
  exact ⟨checked.2.2.1.clock checked.2.1.2.2.1, checked.2.2.1.pc checked.2.1.2.2.2⟩

/-- The complete local AIR supplies the source and verifier Byte guarantees. -/
theorem source_state_encoding {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput) = source.clock ∧
      StateMsg.pcBits (initialBoundaryStateMessage witness.publicInput) = source.pc :=
  source_state_encoding_of_byte witness constraints
    (fun table member => (finishedChannel_guarantees image source witness constraints balanced table member).1)

/-- Complete source validation and AIR binding supply the initial State truth on a local trajectory. -/
theorem initialStateTruth_of_byte {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ witness.allTables, table.ChannelGuarantees byteChannel.toRaw)
    (trajectory : Trajectory) (timeline : Timeline)
    (initial : trajectory 0 = some source.sail.realize) (start : timeline.start 0 = source.clock) :
    LocalStateTruthG (image.toGuestProgram valid) trajectory timeline
      (initialBoundaryStateMessage witness.publicInput) := by
  have checked := (public_contract_of_byte witness constraints (bytes _ witness.mem_allTables_verifierTable)).2.1
  have encoding := source_state_encoding_of_byte witness constraints bytes
  refine ⟨0, source.sail.realize, initial, encoding.1.trans start.symm, ?_,
    checked.romLoaded, checked.configured⟩
  change source.sail.realize.regs.get? LeanRV64D.Defs.Register.PC =
    some (StateMsg.pcBits (initialBoundaryStateMessage witness.publicInput))
  rw [encoding.2]
  exact checked.pc

/-- The complete local AIR supplies the source and verifier Byte guarantees. -/
theorem initialStateTruth {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (trajectory : Trajectory) (timeline : Timeline)
    (initial : trajectory 0 = some source.sail.realize) (start : timeline.start 0 = source.clock) :
    LocalStateTruthG (image.toGuestProgram valid) trajectory timeline
      (initialBoundaryStateMessage witness.publicInput) :=
  initialStateTruth_of_byte valid witness constraints
    (fun table member => (finishedChannel_guarantees image source witness constraints balanced table member).1) trajectory timeline initial start

/-- The initial frontier selects the authentic physical source record for each location. -/
noncomputable def memoryInitialFrontier {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source)) : MemLoc → Option (MemoryMsg (ZMod p)) :=
  fun loc => (((SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records (sourceWitness witness)).filter
    (fun message => decide (MemoryMsg.locOf message = loc))).head?

/-- Source-record values are contents of the actual full Sail state used by execution. -/
theorem memoryInitialFrontier_content_of_byte {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ witness.allTables, table.ChannelGuarantees byteChannel.toRaw)
    {loc : MemLoc} {message : MemoryMsg (ZMod p)}
    (present : memoryInitialFrontier witness loc = some message) :
    MemoryMsg.locOf message = loc ∧ MemoryBoundary.SnapshotSpec source.sail.memorySnapshot message ∧
      locContent source.sail.realize loc = some (Word.toBitVec64 message.value) := by
  have member := List.mem_filter.mp (List.mem_of_head? present)
  have same := of_decide_eq_true member.2
  have authentic := (SnapshotMemoryEnsemble.inventory source.sail.memorySnapshot).records_valid_of_tables
    (sourceWitness witness) (sourceTables_spec_of_byte witness constraints bytes) _ member.1
  refine ⟨same, authentic, ?_⟩
  rw [← same]
  exact authentic.locContent (public_contract_of_byte witness constraints (bytes _ witness.mem_allTables_verifierTable)).2.1.memory

/-- The complete local AIR supplies the source and verifier Byte guarantees. -/
theorem memoryInitialFrontier_content {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {loc : MemLoc} {message : MemoryMsg (ZMod p)}
    (present : memoryInitialFrontier witness loc = some message) :
    MemoryMsg.locOf message = loc ∧ MemoryBoundary.SnapshotSpec source.sail.memorySnapshot message ∧
      locContent source.sail.realize loc = some (Word.toBitVec64 message.value) :=
  memoryInitialFrontier_content_of_byte witness constraints
    (fun table member => (finishedChannel_guarantees image source witness constraints balanced table member).1) present

/-- Source constraints and Byte guarantees supply the complete live-memory invariant at local genesis.
No memory-truth or source-timestamp premise is supplied by the caller. -/
theorem memoryInitialFrontier_liveOK_of_byte {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (bytes : ∀ table ∈ witness.allTables, table.ChannelGuarantees byteChannel.toRaw)
    (trajectory : Trajectory) (timeline : Timeline)
    (initial : trajectory 0 = some source.sail.realize) :
    LiveOKG trajectory source.sail.realize timeline (timeline.start 0) (memoryInitialFrontier witness) := by
  intro loc message present
  obtain ⟨same, authentic, content⟩ := memoryInitialFrontier_content_of_byte witness constraints bytes present
  have atStart : LocalValueAtG trajectory source.sail.realize timeline loc (timeline.start 0) message.value :=
    (localValueAtG_stepStart_iff initial).mpr content
  refine ⟨same, ⟨authentic.1, authentic.2.1, ?_⟩, atStart, ?_⟩
  · rw [same, authentic.2.2.1]
    by_cases zero : timeline.start 0 = 0
    · simpa only [zero] using atStart
    · simpa only [LocalValueAtG, microValueG, if_pos (Nat.pos_of_ne_zero zero)] using content
  · rw [authentic.2.2.1]
    exact Nat.zero_le _

/-- The complete local AIR supplies the source and verifier Byte guarantees. -/
theorem memoryInitialFrontier_liveOK {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (trajectory : Trajectory) (timeline : Timeline)
    (initial : trajectory 0 = some source.sail.realize) :
    LiveOKG trajectory source.sail.realize timeline (timeline.start 0) (memoryInitialFrontier witness) :=
  memoryInitialFrontier_liveOK_of_byte witness constraints
    (fun table member => (finishedChannel_guarantees image source witness constraints balanced table member).1) trajectory timeline initial

end SP1Clean.Soundness.LocalCore
