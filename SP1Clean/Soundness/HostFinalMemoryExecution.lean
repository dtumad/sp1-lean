import SP1Clean.Soundness.HostFinalMemorySoundness
import SP1Clean.Soundness.HostHintReadFinalSnapshot

/-! # Execution of the complete-memory host assembly

The Memory proof view retains every physical table, including the target validators, and
balances every channel except the three final-memory receipt channels. That is exactly what the
host grounding proofs read, so raw acceptance of the complete assembly yields their local
execution path. The installed finite target comparison and the path's own final-record
characterization read the same physical finalizer rows; together they identify every integer
register and the entire Sail RAM map of the path's final state with the supplied outgoing
snapshot. Complete outgoing Sail/host equality remains separate.
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

/-- Raw balance supplies every channel the host proofs read in the Memory proof view. -/
theorem baseWitness_hostBalanced (witness : EnsembleWitness (Installed image source outgoing final bankFinal channels))
    (balanced : witness.BalancedChannels) : HostHintQueueBoundary.Balanced (baseWitness witness) := by
  intro channel registered visible
  have receipt (ram : Bool) : channel ≠ (FinalMemoryValue.channel ram).toRaw := by
    rintro rfl
    exact visible (by cases ram <;> simp [HostHintQueueBoundary.hiddenChannels])
  apply baseWitness_balancedChannel witness channel registered (receipt false) (receipt true)
    (by rintro rfl; exact visible (by simp [HostHintQueueBoundary.hiddenChannels]))
  apply balanced
  simp only [ensemble, ClosedVerifier.install, ClosedVerifier.withInteractions, withReceipts, withRegisters,
    FinalReceiptEnsemble.install, Ensemble.replaceComponent, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl registered)))

/-- **Complete-memory execution.** Raw acceptance of the installed assembly yields one local
RISC-V/host path from the complete source. Its final integer registers and entire RAM map are the
supplied outgoing snapshot; the remaining endpoint observations are those of the host proofs. -/
theorem source_execution (valid : image.Valid)
    (witness : EnsembleWitness (Installed image source outgoing final bankFinal channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
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
        code.toNat = witness.publicInput.exit_code.val) := by
  have checked := source_checkFinal witness constraints balanced
  obtain ⟨events, target, hints, path, permitted, -, clock, pc, -, -, runtime, nextPC, retirement,
    preserved, decoded, host, exit, memory⟩ :=
    HostHintReadCPU.source_execution_with_memory valid (baseWitness witness)
      (baseWitness_constraints witness constraints) (baseWitness_hostBalanced witness balanced)
  rw [finalRecords_eq_core] at checked
  obtain ⟨registers, ram⟩ := (memory outgoing).mp checked
  rw [baseWitness_publicInput] at clock pc nextPC exit
  exact ⟨events, target, hints, path, permitted, clock, pc, registers, ram, runtime, nextPC, retirement,
    preserved, decoded, host, exit⟩

end SP1Clean.Soundness.HostFinalMemory
