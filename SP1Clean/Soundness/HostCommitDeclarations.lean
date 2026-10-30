import SP1Clean.Soundness.HostHintReadBankAgreement
import SP1Clean.Soundness.CommitmentEnsemble

/-! # Commitment calls request their declarations

Each COMMIT or COMMIT_DEFERRED event of the installed local execution is the call of an active
handler row of its bank. That row asserts the call's slot argument and requests the declaration
of that slot with the call's own word. The CPU tape and the bank rows are identified by the
existing bank replay; no order, provider or statement premise is added. Agreement with an
immutable statement follows once a provider authenticates the requests (`Declared.agrees`).
-/

namespace SP1Clean.Soundness.HostCommitDeclarations

open Circuit Air.Flat Model.Core Semantics NativeCore HostCommitBank

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
variable {outgoing : MemorySnapshot}
local instance declarationsLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

/-- Every commitment event of the actual instruction inventory requests its declaration. -/
theorem rows_declared (valid : image.Valid)
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (outgoing := outgoing) (channels := channels))
    (constraints : witness.Constraints) (balanced : HostHintQueueBoundary.Balanced witness) :
    CommitmentEnsemble.Declared witness ((LocalCore.executionRows
      (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))).map ExecutionRow.event) := by
  intro deferred call member code
  obtain ⟨carrier⟩ := HostHintReadCPU.source_grounding_carrier valid witness constraints balanced
  obtain ⟨calls, bankExhaustive, bankSorted, -⟩ := HostHintReadBanks.ordered_calls deferred witness
    constraints balanced ⟨{ readOnly := image.readOnly }, p⟩ rfl (.ofSail source.sail.realize)
  have projected := HostBankCPUReplay.cpu_projection deferred witness constraints balanced
    carrier.exhaustive carrier.cpuWalk bankExhaustive bankSorted
  obtain ⟨row, rowMem, rowEvent⟩ := List.mem_map.mp member
  have stamped : HostBankCPUReplay.stampedCPU deferred witness.data row =
      some (StateMsg.timeNat (row.edge witness.data).1, (call.arg1, call.arg2)) := by
    simp only [HostBankCPUReplay.stampedCPU, rowEvent, bankEvent?, bankCall?, code, if_true,
      Option.map_some]
  have tape : (StateMsg.timeNat (row.edge witness.data).1, (call.arg1, call.arg2)) ∈
      carrier.ordered.filterMap (HostBankCPUReplay.stampedCPU deferred witness.data) :=
    List.mem_filterMap.mpr ⟨row, carrier.exhaustive.mem_iff.mpr rowMem, stamped⟩
  rw [projected] at tape
  obtain ⟨message, messageMem, labelled⟩ := List.mem_map.mp tape
  obtain ⟨⟨index, env⟩, entryMem, called⟩ := List.mem_filterMap.mp (bankExhaustive.mem_iff.mp messageMem)
  cases index with
  | none => simp [call?] at called
  | some slot =>
      simp only [call?, Option.map_some, Option.some.injEq] at called
      obtain ⟨spec, pulled⟩ := HostHintReadBanks.active_slot deferred witness constraints balanced entryMem
      have arguments := congrArg Prod.snd labelled
      simp only [HostBankCPUReplay.label, Prod.mk.injEq] at arguments
      refine ⟨slot, _, pulled, ?_, ?_⟩
      · rw [← arguments.1, ← called, spec.1.2.1, HostCommitChip.toBitVec64_slotWord]
      · rw [← arguments.2, ← called]

end SP1Clean.Soundness.HostCommitDeclarations
