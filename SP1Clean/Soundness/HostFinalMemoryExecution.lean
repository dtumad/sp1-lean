import SP1Clean.Soundness.HostFinalMemorySoundness
import SP1Clean.Soundness.HostHintReadFinalSnapshot
import SP1Clean.Soundness.HostCommitDeclarations

/-! # Execution of the complete-memory host assembly

The Memory proof view retains every physical table, including the target validators, and
balances every channel except the three final-memory receipt channels. That is exactly what the
host grounding proofs read, so raw acceptance of the complete assembly yields their local
execution path. The installed finite target comparison and the path's own final-record
characterization read the same physical finalizer rows; together they identify every integer
register and the entire Sail RAM map of the path's final state with the supplied outgoing
snapshot. Each commitment call of the path also requests its declaration in the witness ledger
(`CommitmentEnsemble.Declared`). Complete outgoing Sail/host equality remains separate.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Model.Core Semantics
open LeanRV64D.Defs (Register)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance executionLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance executionClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot} {outgoing : MemorySnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

/-- The installed complete-memory assembly with the concrete six-call host registry. -/
abbrev Installed (image : ProgramImage) (source : ExecutionSnapshot) (outgoing : MemorySnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState) (channels : List (RawChannel (ZMod p))) :=
  ensemble image source outgoing final bankFinal HostCallReceivers.available
    (HostHintReadLocal.sourceResources source.host.io.hints) channels (source_unique_names image source outgoing)

/-- Balance on every registered channel except commitment declarations. The verifier-owned
statement provider that supplies them is installed above this assembly. -/
def DeclarationsOpen (witness : EnsembleWitness (Installed image source outgoing final bankFinal channels)) : Prop :=
  ∀ channel ∈ (Installed image source outgoing final bankFinal channels).channels,
    channel ≠ CommitmentDeclaration.channel.toRaw → witness.BalancedChannel channel

/-- Complete balance in particular balances everything but the declarations. -/
theorem DeclarationsOpen.of_balancedChannels
    {witness : EnsembleWitness (Installed image source outgoing final bankFinal channels)}
    (balanced : witness.BalancedChannels) : DeclarationsOpen witness :=
  fun channel member _ => balanced channel member

/-- The Memory proof view balances every channel the host proofs read. -/
theorem baseWitness_hostBalanced (witness : EnsembleWitness (Installed image source outgoing final bankFinal channels))
    (balanced : DeclarationsOpen witness) : HostHintQueueBoundary.Balanced (baseWitness witness) := by
  intro channel registered visible
  have receipt (ram : Bool) : channel ≠ (FinalMemoryValue.channel ram).toRaw := by
    rintro rfl
    exact visible (by cases ram <;> simp [HostHintQueueBoundary.hiddenChannels])
  apply baseWitness_balancedChannel witness channel registered (receipt false) (receipt true)
    (by rintro rfl; exact visible (by simp [HostHintQueueBoundary.hiddenChannels]))
  apply balanced
  · simp only [ensemble, ClosedVerifier.install, ClosedVerifier.withInteractions, withReceipts, withRegisters,
      FinalReceiptEnsemble.install, Ensemble.replaceComponent, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl registered)))
  · rintro rfl
    exact visible (by simp [HostHintQueueBoundary.hiddenChannels])

/-- The installed target comparison needs Byte closure and its private Memory channels only. -/
theorem checkFinal_of_declarationsOpen
    (witness : EnsembleWitness (Installed image source outgoing final bankFinal channels))
    (checked : witness.Constraints) (balanced : DeclarationsOpen witness) :
    source.sail.memorySnapshot.checkFinal outgoing
      ((finalRecords witness).map fun record => (MemoryMsg.locOf record, Word.toBitVec64 record.value)) = true := by
  apply checkFinal_of_channels witness (source_privacy outgoing source.host.io.hints) checked
    (byte_guarantees witness (HostHintReadLocal.source_interface source.host.io.hints) checked
      (balanced _ ?_ (by simp [CommitmentDeclaration.channel, Channels.byteChannel, Channel.toRaw])))
  · intro channel member
    apply balanced
    · simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;>
        simp [ensemble, ClosedVerifier.install, ClosedVerifier.withInteractions, withReceipts, withRegisters,
          FinalReceiptEnsemble.install, Ensemble.replaceComponent,
          FinalMemoryChangeBoundary.closed, FinalMemoryChangeBoundary.circuit, circuit_norm]
      all_goals apply Or.inl
      all_goals simp [base, HostHintQueueBoundary.ensemble, HaltPadding.install, Ensemble.replaceComponent,
        ClosedVerifier.install, ClosedVerifier.withInteractions, HostHintReadLocal.ensemble, HostLocalHandoff.ensemble,
        HostLocalCore.ensemble, PublicVerifier.install, HostLocalCore.baseEnsemble,
        FinalMemoryChecks.checkTables, StaticTable.component, StaticTable.provider, circuit_norm]
    · simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;>
        simp [CommitmentDeclaration.channel, FinalMemoryValue.channel, FinalMemoryChange.channel,
          FinalRegisterValue.membership, InitialMemoryLookup.membership, StaticTable.channel, Channel.toRaw]
  · simp [ensemble, ClosedVerifier.install, ClosedVerifier.withInteractions, withReceipts, withRegisters,
      FinalReceiptEnsemble.install, Ensemble.replaceComponent, base, HostHintQueueBoundary.ensemble,
      HaltPadding.install, HostHintReadLocal.ensemble, HostLocalHandoff.ensemble, HostLocalCore.ensemble,
      PublicVerifier.install, HostLocalCore.baseEnsemble, LocalCore.baseEnsemble, sp1Ensemble_channels]

/-- **Complete-memory execution.** Constraints and balance outside the commitment declarations
yield one local RISC-V/host path from the complete source. Its final integer registers and entire RAM map are the
supplied outgoing snapshot; the remaining endpoint observations are those of the host proofs. -/
theorem source_execution (valid : image.Valid)
    (witness : EnsembleWitness (Installed image source outgoing final bankFinal channels))
    (constraints : witness.Constraints) (balanced : DeclarationsOpen witness) :
    ∃ events target hints, ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize events target ∧
      ExecutionPath.WritesPermitted ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize events ∧
      target.clock = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) ∧
      target.sail.regs.get? Register.PC =
        some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput)) ∧
      (∀ index, target.sail.get_reg? index = some (outgoing.read (.reg index))) ∧
      target.sail.mem = outgoing.memory.toSailMemory (2 ^ 48) ∧
      (target.sail.cycleCount = source.sail.cycleCount ∧ target.sail.sailOutput = source.sail.output) ∧
      target.sail.regs.get? Register.nextPC = nextPcAfter events
        (source.sail.registers.get? Register.nextPC)
        (some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput))) ∧
      (target.sail.regs.get? Register.minstret_increment =
        (if events.countP Machine.ExecutionEvent.isOrdinary = 0
          then source.sail.registers.get? Register.minstret_increment
          else some (retirementEnabled source.sail.realize)) ∧
        target.sail.regs.get? Register.minstret = (source.sail.registers.get? Register.minstret).map
          (fun value => value + BitVec.ofNat 64
            (if retirementEnabled source.sail.realize then events.countP Machine.ExecutionEvent.isOrdinary else 0))) ∧
      (∀ R : Register, R ≠ Register.PC → R ≠ Register.nextPC → R ≠ Register.minstret →
        R ≠ Register.minstret_increment → (∀ index : BitVec 5, R ≠ reg_idx_to_Register index) →
          target.sail.regs.get? R = source.sail.registers.get? R) ∧
      HintQueue.decode? (HintQueue.ofList source.host.io.hints).1 (Address.toNat final.head) = some hints ∧
      target.host = { source.host with
        io.hints := hints
        committed := bankFinal.committed
        deferred := bankFinal.deferred
        exitCode := bankFinal.exitCode } ∧
      (∀ code : BitVec 32, source.host.exitCode = none → target.host.exitCode = some code →
        code.toNat = witness.publicInput.exit_code.val) ∧
      CommitmentEnsemble.Declared witness events := by
  have checked := checkFinal_of_declarationsOpen witness constraints balanced
  have baseConstraints := baseWitness_constraints witness constraints
  have baseBalanced := baseWitness_hostBalanced witness balanced
  obtain ⟨events, target, hints, path, permitted, inventory, clock, pc, -, -, runtime, nextPC, retirement,
    preserved, decoded, host, exit, memory⟩ :=
    HostHintReadCPU.source_execution_with_memory valid (baseWitness witness) baseConstraints baseBalanced
  rw [finalRecords_eq_core] at checked
  obtain ⟨registers, ram⟩ := (memory outgoing).mp checked
  rw [baseWitness_publicInput] at clock pc nextPC exit
  have declared := (HostCommitDeclarations.rows_declared valid (baseWitness witness) baseConstraints
    baseBalanced).of_perm inventory
  refine ⟨events, target, hints, path, permitted, clock, pc, registers, ram, runtime, nextPC, retirement,
    preserved, decoded, host, exit, declared.transfer fun interaction member => ?_⟩
  rw [baseWitness_interactions witness _ (by simp [CommitmentDeclaration.channel, FinalMemoryValue.channel,
    Channel.toRaw]) (by simp [CommitmentDeclaration.channel, FinalMemoryValue.channel, Channel.toRaw])] at member
  exact ClosedVerifier.mem_interactionsWith_of_project _ witness member

end SP1Clean.Soundness.HostFinalMemory
