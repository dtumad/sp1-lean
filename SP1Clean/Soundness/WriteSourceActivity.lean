import SP1Clean.Soundness.WriteSourceRows
import SP1Clean.Soundness.CoreMemoryBalance

/-! # Boolean activity of all original WRITE source receipts

The source tables determine the enable gate even before the read-back ledger is balanced.
Ordinary, ECALL and HINT_READ sites use their original Memory interactions, while both final
providers and the refresh use their own original selector checks.
-/

namespace SP1Clean.WriteProbe.AccessInventory

open Circuit Air.Flat Soundness Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem ordinary_binary (id : InstructionChipId) : NativeCore.MemoryBinary (ProtectedOrdinaryReceipt.component (p := p) id) := by
  have original := NativeCore.instruction_memoryBinary (supportedChipFor (p := p) id).table
    (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨id, InstructionChipId.mem_all id, rfl⟩, rfl⟩)
  intro data physical checked interaction member
  refine original data physical ?_ interaction ?_
  · simpa only [Operations.ConstraintsHold, ProtectedOrdinaryReceipt.constraints, ProtectedOrdinaryReceipt.provider_constraints,
      ProtectedOrdinaryReceipt.lookups, ProtectedOrdinaryReceipt.provider_lookups] using checked
  · simpa only [Operations.interactionValuesWith, ProtectedOrdinaryReceipt.interactions id memoryChannel.toRaw (by
      intro same; exact Bool.noConfusion (congrArg (fun (c : RawChannel (ZMod p)) => c.name == "SP1Memory") same)),
      ProtectedOrdinaryReceipt.provider_interactions id memoryChannel.toRaw (by
      intro same; exact Bool.noConfusion (congrArg (fun (c : RawChannel (ZMod p)) => c.name == "SP1Memory") same))] using member

private theorem host_binary (family : HostSources.Family) : NativeCore.MemoryBinary (HostSources.original (p := p) family) := by
  intro data physical checked i member
  cases family with
  | ecall =>
    rw [show (HostSources.original (p := p) .ecall).operations.interactionValuesWith memoryChannel.toRaw _ = _ from
      HostCallProjection.memory_values _] at member
    exact NativeCore.syscall_memoryBinary data physical (HostCallProjection.constraints_original _ checked) i member
  | word last =>
    rw [show (HostSources.original (p := p) (.word last)).operations.interactionValuesWith memoryChannel.toRaw _ = _ from
      HintReadWriteLedger.row_memory_values (last, Environment.fromArray physical data)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    have binary := HintReadCoverage.row_activity_binary (last, Environment.fromArray physical data) checked
    rcases member with rfl | rfl <;> exact binary

private theorem final_binary (ram : Bool) (env : Environment (ZMod p)) (checked : (originalFinal ram).operations.ConstraintsHold env) :
    IsBool (valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env).2 := by
  have activity : (valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env).2 =
      env (FinalMemoryEnsemble.activity (p := p)) := by
    rw [← eval_varFromOffset_valueFromOffset, eval_pair (α := OrderedMemoryProvider.Inputs MemoryMsg) (β := field)]
    simp only [FinalMemoryEnsemble.activity, varFromOffset_pair, ProvableType.varFromOffset_field, ProvableType.eval_field, Nat.zero_add]
  rw [activity]
  cases ram
  · have localChecks : FinalMemoryEnsemble.registerView.component.operations.ConstraintsHold env := by
      change (OrderedFinalProvider.registerCircuit.instantiate.operations 0).ConstraintsHold env
      change ((FinalMemoryReceipt.circuit false OrderedFinalProvider.registerCircuit).instantiate.operations 0).ConstraintsHold env at checked
      simpa only [Operations.ConstraintsHold, FinalMemoryReceipt.constraints, FinalMemoryReceipt.lookups] using checked
    have on := FinalMemoryEnsemble.registerView.activity_of_constraints env localChecks
    rw [FinalMemoryEnsemble.registerView_activity] at on
    exact on
  · have localChecks : FinalMemoryEnsemble.ramView.component.operations.ConstraintsHold env := by
      change (OrderedFinalProvider.ramCircuit.instantiate.operations 0).ConstraintsHold env
      change ((FinalMemoryReceipt.circuit true OrderedFinalProvider.ramCircuit).instantiate.operations 0).ConstraintsHold env at checked
      simpa only [Operations.ConstraintsHold, FinalMemoryReceipt.constraints, FinalMemoryReceipt.lookups] using checked
    have on := FinalMemoryEnsemble.ramView.activity_of_constraints env localChecks
    rw [FinalMemoryEnsemble.ramView_activity] at on
    exact on

private theorem final_row_binary (ram : Bool) (env : Environment (ZMod p))
    (valid : (originalFinal ram).operations.ConstraintsHold env)
    (r : ZMod p × Readback (ZMod p)) (seen : r ∈ rowRecords (.finalizer ram) env) : IsBool r.1 := by
  simp only [rowRecords, List.mem_singleton] at seen
  simp only [seen]
  exact final_binary (p := p) ram env valid

/-- No externally supplied selector premise is needed for any registered source family. -/
theorem records_binary (raw : Source → Table (ZMod p)) (registered : ∀ id, (raw id).component = original id)
    (checked : ∀ id, (raw id).Constraints) : ∀ r ∈ records raw, IsBool r.1 := by
  intro r member
  obtain ⟨id, _, inTable⟩ := List.mem_flatMap.mp member
  obtain ⟨physical, rowMem, seen⟩ := List.mem_flatMap.mp inTable
  have valid := checked id physical rowMem
  rw [registered] at valid
  cases id with
  | ordinary instruction =>
    obtain ⟨site, used, rfl⟩ := List.mem_map.mp seen
    exact ordinary_binary instruction _ physical valid _ (OrdinarySources.protected_pull instruction _ site used)
  | host family =>
    obtain ⟨site, used, rfl⟩ := List.mem_map.mp seen
    exact host_binary family _ physical valid _ (HostSources.actual_pull family _ site used)
  | refresh =>
    obtain rfl := List.mem_singleton.mp seen
    have shallow := shallowConstraints_of_componentConstraints MemoryBumpChip.circuit _ valid
    have on := MemoryBumpChip.selectorBinary_of_shallow _ _ _ shallow
    rw [← eval_varFromOffset_valueFromOffset]
    simpa only [IsBool, circuit_norm] using on
  | finalizer ram =>
    exact final_row_binary (p := p) ram ((raw (.finalizer ram)).environment physical) valid r seen

end SP1Clean.WriteProbe.AccessInventory
