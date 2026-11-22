import SP1Clean.Proofs.Completeness.WriteObservationPacket
import SP1Clean.Soundness.WriteVersionIntervals
import SP1Clean.Soundness.HostHintReadExecutionPath

/-! # The WRITE operand observer on installed physical prefixes

The installed host assembly supplies the ordered active rows, genesis, and all row step/frame
facts. Every cut, including genesis and the final state, admits the same read-only WRITE checks
on arbitrary supplied operands. The call being queried need not be a member of that assembly.
-/

namespace SP1Clean.TraceGen.WriteObservations

open Circuit Air.Flat Channels Semantics Machine Soundness Soundness.NativeCore
open Soundness.HostHintReadCPU Soundness.HostHintReadLocal Soundness.TimedGrounding
open Soundness.WriteObservationHistory

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
variable {extra : List (Component (ZMod p))} [GroundingResources extra]
variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}
variable [HostFinalMemory.Registration image source extra HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints) channels]
  {sourceNames : HostFinalMemory.UniqueNames image source extra HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints)}

private local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Original physical event footprints in the order authenticated by the State channel, including
guest RAM pushes owned by earlier HINT_READ transfers. -/
noncomputable def physicalRows {witness : HostHintQueueBoundary.SourceWitness image source final
    bankFinal extra channels sourceNames} (carrier : GroundingCarrier witness) : List (RowFacts p) :=
  carrier.ordered.map (eventFacts witness.data (TransitionView.readIndexedActiveRows
    HintReadCoverage.variants HintReadCoverage.view (wordTables (HostHintQueueBoundary.projected witness))))

private theorem installed_held (witness : HostHintQueueBoundary.SourceWitness image source final
    bankFinal extra channels sourceNames) (checked : witness.Constraints)
    (balanced : HostHintQueueBoundary.Balanced witness) :
    ∃ (valid : image.Valid) (carrier : GroundingCarrier witness), ∀ cut ≤ carrier.ordered.length,
      ∃ current, carrier.pairedTrajectory valid cut = some current ∧
        ∀ (loc : MemLoc), loc.busAddress < 2 ^ 48 →
          let word := wordAt source.sail.memorySnapshot (physicalRows carrier) cut loc
          word.isU64 ∧ locContent current.sail loc = some word.toBitVec64 := by
  have ordering := HostHintQueueBoundary.SourceWitness.orderingChannels witness checked balanced
  have sourceValid := (LocalCore.public_contract_of_byte _ ordering.sourceChecks ordering.verifierByte).2.1
  have valid := sourceValid.1.1
  obtain ⟨carrier⟩ := source_grounding_carrier valid witness checked balanced
  have checkedCore := HostLocalCore.localWitness_constraints _
    (HostHintQueueBoundary.projected_constraints witness checked)
  have encoding := LocalCore.source_state_encoding_of_checks _ ordering.sourceChecks
  rw [HostHintQueueBoundary.SourceWitness.localPublicInput] at encoding
  have initialState := LocalCore.initialStateTruth_of_checks valid _ ordering.sourceChecks
    (carrier.trajectory valid) carrier.timeline (carrier.trajectory_zero valid) (carrier.timeline_start.trans encoding.1)
  rw [HostHintQueueBoundary.SourceWitness.localPublicInput] at initialState
  have initialMemory := LocalCore.memoryInitialFrontier_liveOK_of_channels _ checkedCore
    ordering.sourceChecks ordering.byte (source_membership_balance witness balanced) (carrier.trajectory valid)
    carrier.timeline (carrier.trajectory_zero valid)
  rw [carrier.timeline_start] at initialMemory
  obtain ⟨_, path, _⟩ := carrier.execution valid checked balanced
  refine ⟨valid, carrier, ?_⟩
  intro cut within
  obtain ⟨current, atCut, _⟩ := path.replay_split cut
  have before : carrier.trajectory valid cut = some current.sail := congrArg (Option.map ExecutionState.sail) atCut
  refine ⟨current, atCut, fun loc bound => ?_⟩
  have held := wordAt_carrier carrier (carrier.trajectory_zero valid) sourceValid.memory initialState initialMemory
    (fun event member => by
      cases event with
      | instruction row => exact carrier.instruction_engineFacts valid checked balanced member
      | syscall row => exact carrier.syscall_engineFacts valid checked balanced member
      | halt row => exact carrier.halt_engineFacts valid checked balanced member) within loc bound
  exact ⟨held.1, (localValueAt_stepStart_iff before).mp held.2⟩

/-- Every probe on the physical host assembly selects one genuine version defined by its
original Memory pushes. Its four limbs reproduce the paired replay on that cut, including
untouched snapshot cells and versions surviving through the final cut. -/
theorem installed_versions (witness : HostHintQueueBoundary.SourceWitness image source final
    bankFinal extra channels sourceNames) (checked : witness.Constraints)
    (balanced : HostHintQueueBoundary.Balanced witness) :
    ∃ (valid : image.Valid) (carrier : GroundingCarrier witness), ∀ cut ≤ carrier.ordered.length,
      ∃ current, carrier.pairedTrajectory valid cut = some current ∧
        ∀ (loc : MemLoc), loc.busAddress < 2 ^ 48 →
          ∃ v, (versionIntervals (physicalRows carrier) loc).filter (·.coversClock (carrier.timeline.start cut)) = [v] ∧
            let word := v.value (Target.bitVecToWord (source.sail.memorySnapshot.read loc))
            word.isU64 ∧ locContent current.sail loc = some word.toBitVec64 := by
  obtain ⟨valid, carrier, all⟩ := installed_held witness checked balanced
  refine ⟨valid, carrier, fun cut within => ?_⟩
  obtain ⟨current, reached, held⟩ := all cut within
  refine ⟨current, reached, fun loc bound => ?_⟩
  obtain ⟨v, unique, eq⟩ := versionIntervals_at source.sail.memorySnapshot (physicalRows carrier) loc
    (by simpa [physicalRows] using within)
  refine ⟨v, ?_, eq.symm ▸ held loc bound⟩
  rw [versionIntervals_clock _ loc (by simpa [physicalRows] using within)]
  · exact unique
  · intro i row present
    rw [physicalRows, List.getElem?_map, Option.map_eq_some_iff] at present
    obtain ⟨event, seen, rfl⟩ := present
    exact carrier.time_of_ordered_at seen

/-- Raw constraints and ledger closure suffice for every possible probe at every actual cut of
the installed host prefix. Every accepted packet is checked against the same paired replay. -/
theorem installed_cuts (witness : HostHintQueueBoundary.SourceWitness image source final
    bankFinal extra channels sourceNames) (checked : witness.Constraints)
    (balanced : HostHintQueueBoundary.Balanced witness) :
    ∃ (valid : image.Valid) (carrier : GroundingCarrier witness), ∀ cut ≤ carrier.ordered.length,
      ∃ current, carrier.pairedTrajectory valid cut = some current ∧
        ∀ (call : CoreSyscallEvent) (length : Word (ZMod p)) (buffer : List (Word (ZMod p))),
          checkWriteInputs source.sail.memorySnapshot (physicalRows carrier) cut call length buffer = true ↔
            (current.sail.get_reg? 5 = some call.rawCode ∧ current.sail.get_reg? 10 = some call.arg1 ∧
              current.sail.get_reg? 11 = some call.arg2) ∧ length.isU64 ∧ (∀ word ∈ buffer, word.isU64) ∧
              read? current.sail call = some (length.toBitVec64, buffer.map Word.toBitVec64) := by
  obtain ⟨valid, carrier, all⟩ := installed_held witness checked balanced
  refine ⟨valid, carrier, fun cut within => ?_⟩
  obtain ⟨current, reached, held⟩ := all cut within
  exact ⟨current, reached, checkWriteInputs_iff held⟩

end SP1Clean.TraceGen.WriteObservations
