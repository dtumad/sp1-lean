import SP1Clean.Soundness.HostHintReadTrajectory
import SP1Clean.Soundness.HostLocalCoreRom
import SP1Clean.Soundness.CoreInstructionExecution

/-! # Ordinary execution on the complete instruction and hint carrier

Every ordinary instruction retains its original footprint: authenticated hint ownership excludes
added RAM rows at its clock. Byte and Program guarantees supply the registered chip contracts,
and the extended permission ledger protects ROM. The resulting step/frame facts use the same
paired Sail/host replay as the hint handlers, with all instruction cases internal to the registry.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance instructionLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance instructionLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {channels : List (RawChannel (ZMod p))}

private theorem source_data
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)) :
    (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)).data = witness.data := rfl

private theorem instruction_staticInputs
    (witness : EnsembleWitness (LocalCore.ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (byte : ∀ table ∈ witness.allTables, table.ChannelGuarantees byteChannel.toRaw)
    (program : ∀ table ∈ witness.allTables, table.ChannelGuarantees programChannel.toRaw)
    {row : DecodedInstructionRow p} (member : row ∈ LocalCore.instructionRows witness) :
    DecodedRowStaticInputs row witness.data :=
  ⟨mem_chip_of_mem_decodeInstructionTables member,
    LocalCore.instructionRows_constraints witness constraints row member,
    channelGuarantees_of_mem_decodeInstructionTables witness.data _ (LocalCore.instructionTables_aligned witness)
      (fun table tableMem => byte table (LocalCore.instructionTables_mem witness tableMem)) row member,
    channelGuarantees_of_mem_decodeInstructionTables witness.data _ (LocalCore.instructionTables_aligned witness)
      (fun table tableMem => program table (LocalCore.instructionTables_mem witness tableMem)) row member⟩

private theorem instruction_inputs (valid : image.Valid)
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p}
    (member : ExecutionRow.instruction row ∈
      LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))) :
    DecodedRowStaticInputs row witness.data ∧
      Target.decodedInROM (image.toGuestProgram valid) (programAccess (row.toChipRow witness.data).view).toRow := by
  have checks := HostHintQueueBoundary.expanded_constraints witness constraints
  have balance := HostHintQueueBoundary.expanded_balanced witness balanced
  have checked := HostLocalCore.localWitness_constraints _ checks
  have ordering := HostLocalCore.orderingChannels _
    (auxiliaryInterface (HostHintQueueBoundary.expanded_interface (source_interface source.host.io.hints))) checks balance
  have active : row ∈ LocalCore.instructionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)) ∧
      (row.toChipRow (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)).data).is_real = 1 := by
    simpa [LocalCore.executionRows, LocalCore.activeInstructionRows] using member
  have programBalance : (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)).BalancedChannel
      programChannel.toRaw := by
    change BalancedInteractions ((HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)).interactionsWith _)
    rw [HostLocalCore.localWitness_program _ (source_program_silent source final)]
    exact balance _ (by simp [HostLocalCore.ensemble, ProtectedLocalCore.ensemble, LocalCore.ensemble, sp1Ensemble_channels])
  have program := LocalCore.program_guarantees_of_balance image source _ checked programBalance
  have inputs := instruction_staticInputs _ checked ordering.byte program active.1
  have committed := LocalCore.instructionRows_program_committed_of_balance valid _ checked programBalance active.1 active.2
  rw [source_data] at inputs committed active
  refine ⟨inputs, ?_⟩
  exact committed.decoded_of_opcode_ne
    (supportedChip_fetchDiscriminantShape row.chip inputs.registered witness.data row.physical
      inputs.constraints inputs.byte active.2)

private theorem trajectory_ordinary (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p}
    (member : ExecutionRow.instruction row ∈
      LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)))
    (decoded : Target.decodedInROM (image.toGuestProgram valid) (programAccess (row.toChipRow witness.data).view).toRow)
    (pull : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
      (row.ordinaryRowFacts witness.data).statePull)
    (n : ℕ) (time : StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePull = carrier.timeline.start n) :
    carrier.trajectory valid (n + 1) = (carrier.trajectory valid n).bind Machine.stepOnce := by
  obtain ⟨m, state, present, atIndex, pc, _, configured⟩ := pull
  have same : m = n := start_injective carrier.timeline (atIndex.symm.trans time)
  subst m
  change (carrier.pairedTrajectory valid n).map ExecutionState.sail = some state at present
  obtain ⟨whole, paired, sail⟩ := Option.map_eq_some_iff.mp present
  have atPc : whole.sail.regs.get? LeanRV64D.Defs.Register.PC =
      some (Target.pcBitsOfRow (programAccess (row.toChipRow witness.data).view).toRow) := by
    rw [sail, program_pc_eq_statePull]
    exact pc
  have notEcall := decoded.notEcall (by rwa [sail]) atPc
  obtain ⟨_, _, fetched, _, _⟩ := decoded
  have running := carrier.pairedTrajectory_running_of_fetch valid constraints balanced member paired atPc fetched
  change (ExecutionCarrier.pairedTrajectory carrier _ _ _ (n + 1)).map ExecutionState.sail = _
  rw [ExecutionCarrier.pairedTrajectory_succ carrier _ _ _ member time]
  change ((carrier.pairedTrajectory valid n).bind _).map ExecutionState.sail = _
  rw [paired, Option.bind_some]
  change (replayStep? _ (image.toGuestProgram valid) whole .ordinary).map ExecutionState.sail = _
  rw [replayStep?_ordinary_sail _ _ _ running notEcall]
  simp only [GroundingCarrier.trajectory, paired, Option.map_some, Option.bind_some]

/-- All 25 ordinary instruction families supply complete step/frame facts on the same carrier
as the hint handlers. ROM preservation and absence of added hint accesses follow from the AIR. -/
theorem GroundingCarrier.instruction_engineFacts (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final HostCallReceivers.available
      (sourceResources source.host.io.hints) channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : DecodedInstructionRow p}
    (member : ExecutionRow.instruction row ∈
      LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness))) :
    LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
        (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.expanded witness))) (.instruction row)) ∧
      FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
        (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.expanded witness))) (.instruction row)) := by
  have noWords := source_wordsAt_nil_of_not_read witness constraints balanced (.instruction row) member
    (fun _ impossible => by cases impossible)
  simp only [eventFacts, noWords, List.map_nil, List.append_nil]
  change LocalStepFactG _ _ _ _ (row.ordinaryRowFacts witness.data) ∧
    FrameFactG _ _ _ _ (row.ordinaryRowFacts witness.data)
  have checked := instruction_inputs valid witness constraints balanced member
  have contracts := supportedChip_groundingContracts row.chip checked.1.registered
  have active : row ∈ LocalCore.instructionRows (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)) ∧
      (row.toChipRow (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)).data).is_real = 1 := by
    simpa [LocalCore.executionRows, LocalCore.activeInstructionRows] using member
  have checks := HostHintQueueBoundary.expanded_constraints witness constraints
  have balance := HostHintQueueBoundary.expanded_balanced witness balanced
  have permission := HostLocalCore.instructionRows_write_permitted (HostHintQueueBoundary.expanded witness)
    (auxiliary_permission_pulls (HostQueueCurrent.source_permission_pulls source final)) checks balance active.1 active.2
  rw [source_data] at permission active
  apply contracts.engineFactsLocalG_of_rowEffect witness.data row rfl checked.1 active.2 _ checked.2
    (carrier.trajectory valid) source.sail.realize carrier.timeline
    (fun _ effect loaded => effect.romLoaded_of_writePermission valid permission loaded)
  · intro n time
    have successor := ExecutionCarrier.originalTimeStep carrier member n time
    have ordering := HostLocalCore.orderingChannels _
      (auxiliaryInterface (HostHintQueueBoundary.expanded_interface (source_interface source.host.io.hints))) checks balance
    have duration := (LocalCore.executionRows_advancing_of_orderingChannels _
      (HostLocalCore.localWitness_constraints _ checks) ordering member).2
    rw [source_data, ExecutionRow.edge_eq_facts] at duration
    change StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePush =
      StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePull + 8 at duration
    change StateMsg.timeNat (row.ordinaryRowFacts witness.data).statePush = carrier.timeline.start (n + 1) at successor
    exact successor.symm.trans (duration.trans (congrArg (fun clock => clock + 8) time))
  · exact trajectory_ordinary valid carrier constraints balanced member checked.2

end SP1Clean.Soundness.HostHintReadCPU
