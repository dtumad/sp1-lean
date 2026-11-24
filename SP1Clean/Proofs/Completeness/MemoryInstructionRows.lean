import SP1Clean.Proofs.Completeness.EventBuckets
import SP1Clean.Proofs.Completeness.InstalledInstructionTables

/-! # Original address-circuit specifications on compiled load and store rows

All nine physical Memory families reuse their typed event inputs and their original output cells
when the registered permission and ordinary receipt circuits wrap the instruction.
-/

namespace SP1Clean.TraceGen

open Circuit Air.Flat Soundness

private abbrev F := ZMod SP1Prime
private abbrev installed := ProtectedOrdinaryReceipt.component (p := SP1Prime)

/-- The Memory event carried by a routed load or store. -/
def RoutedEvent.memoryEvent? : RoutedEvent → Option MemoryEvent
  | ⟨.loadByte, e⟩ | ⟨.loadHalf, e⟩ | ⟨.loadWord, e⟩ | ⟨.loadDouble, e⟩ | ⟨.loadX0, e⟩
    | ⟨.storeByte, e⟩ | ⟨.storeHalf, e⟩ | ⟨.storeWord, e⟩ | ⟨.storeDouble, e⟩ => some e
  | _ => none

namespace InstalledInstructionTables

private theorem ram_soundness_inputs (id : InstructionChipId) (e : id.Event) {ram : MemoryEvent}
    (family : RoutedEvent.memoryEvent? ⟨id, e⟩ = some ram) (data : ProverData F) :
    (installed id).circuit.Assumptions (InstalledInstructionTables.activeInput id e) data := by
  cases id <;> simp only [RoutedEvent.memoryEvent?, reduceCtorEq] at family
  case loadByte | loadHalf | loadWord | loadDouble | loadX0 =>
    exact ⟨wordOfNat_isU64 _, wordOfNat_isU64 _, wordOfNat_isU64 _⟩
  case storeDouble => exact ⟨wordOfNat_isU64 _, wordOfNat_isU64 _⟩
  case storeByte => exact ⟨wordOfNat_isU64 _, wordOfNat_isU64 _, fun _ => storeLimb_isU64 _ _ (storeByteLimb_lt _ _ _)⟩
  case storeHalf => exact ⟨wordOfNat_isU64 _, wordOfNat_isU64 _, fun _ => storeLimb_isU64 _ _ (Nat.mod_lt _ (by decide))⟩
  case storeWord => exact ⟨wordOfNat_isU64 _, wordOfNat_isU64 _, fun _ => storeWordValue_isU64 _ _ _⟩

private theorem generated_outputs (id : InstructionChipId) (env : Environment F) :
    (installed id).rowOutput env = (supportedChipFor id).table.rowOutput env := by
  cases id <;> rfl

/-- The generated active Memory row satisfies its bundled spec in the generation data, with
its original address and output columns recoverable in any evaluation of those committed cells. -/
theorem active_memory_spec (id : InstructionChipId) (e : id.Event) (valid : id.Valid e)
    {ram : MemoryEvent} (family : RoutedEvent.memoryEvent? ⟨id, e⟩ = some ram)
    (data evaluation : ProverData F) (hint : ProverHint F) :
    let input := activeInput id e
    let cells := (installed id).buildRow input data hint
    (installed id).circuit.Spec input ((supportedChipFor id).table.rowOutput
      (Environment.fromArray cells evaluation)) data := by
  intro input cells
  have spec := ((installed id).buildRow_spec_requirements input data hint (activeInput_valid id e valid data hint)
    (ram_soundness_inputs id e family data)).1
  change (installed id).circuit.Spec ((installed id).rowInput (Environment.fromArray cells data))
    ((installed id).rowOutput (Environment.fromArray cells data)) data at spec
  rwa [(installed id).rowInput_buildRow input data data hint, generated_outputs id,
    Component.rowOutput_congr (supportedChipFor id).table (env := Environment.fromArray cells data)
      (env' := Environment.fromArray cells evaluation) rfl] at spec

end InstalledInstructionTables
end SP1Clean.TraceGen
