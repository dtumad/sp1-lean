import SP1Clean.Soundness.ProtectedStoreFootprints
import SP1Clean.Soundness.LocalCoreDecode

/-! # Uniform write footprints of decoded local instructions

A property of every supported decoded instruction row follows from its store cases alone: the
other instruction views have no memory write. The host assembly's ROM write exclusion applies this
to its authenticated store footprints.
-/

namespace SP1Clean.Soundness.ProtectedLocalCore

open Circuit Air.Flat SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Only the four store families need byte permissions; all other instruction views have no RAM write. -/
theorem supported_write_property (property : Trace.RowView (ZMod p) → Prop)
    (noWrite : ∀ row, row.commit.memWrite = none → property row) (id : InstructionChipId)
    (env : Environment (ZMod p))
    (byte : id = .storeByte →
      (({ circuit := StoreByteChip.circuit, Assumptions := (StoreByteChip.circuit).Assumptions, generation := StoreByteChip.generation } : Component (ZMod p)).rowInput env).is_real = 1 →
      property (StoreByteChip.rowView
        (({ circuit := StoreByteChip.circuit, Assumptions := (StoreByteChip.circuit).Assumptions, generation := StoreByteChip.generation } : Component (ZMod p)).rowInput env)
        (({ circuit := StoreByteChip.circuit, Assumptions := (StoreByteChip.circuit).Assumptions, generation := StoreByteChip.generation } : Component (ZMod p)).rowOutput env)))
    (half : id = .storeHalf →
      (({ circuit := StoreHalfChip.circuit, Assumptions := (StoreHalfChip.circuit).Assumptions, generation := StoreHalfChip.generation } : Component (ZMod p)).rowInput env).is_real = 1 →
      property (StoreHalfChip.rowView
        (({ circuit := StoreHalfChip.circuit, Assumptions := (StoreHalfChip.circuit).Assumptions, generation := StoreHalfChip.generation } : Component (ZMod p)).rowInput env)
        (({ circuit := StoreHalfChip.circuit, Assumptions := (StoreHalfChip.circuit).Assumptions, generation := StoreHalfChip.generation } : Component (ZMod p)).rowOutput env)))
    (word : id = .storeWord →
      (({ circuit := StoreWordChip.circuit, Assumptions := (StoreWordChip.circuit).Assumptions, generation := StoreWordChip.generation } : Component (ZMod p)).rowInput env).is_real = 1 →
      property (StoreWordChip.rowView
        (({ circuit := StoreWordChip.circuit, Assumptions := (StoreWordChip.circuit).Assumptions, generation := StoreWordChip.generation } : Component (ZMod p)).rowInput env)
        (({ circuit := StoreWordChip.circuit, Assumptions := (StoreWordChip.circuit).Assumptions, generation := StoreWordChip.generation } : Component (ZMod p)).rowOutput env)))
    (double : id = .storeDouble →
      (({ circuit := StoreDoubleChip.circuit, Assumptions := (StoreDoubleChip.circuit).Assumptions, generation := StoreDoubleChip.generation } : Component (ZMod p)).rowInput env).is_real = 1 →
      property (StoreDoubleChip.rowView
        (({ circuit := StoreDoubleChip.circuit, Assumptions := (StoreDoubleChip.circuit).Assumptions, generation := StoreDoubleChip.generation } : Component (ZMod p)).rowInput env)
        (({ circuit := StoreDoubleChip.circuit, Assumptions := (StoreDoubleChip.circuit).Assumptions, generation := StoreDoubleChip.generation } : Component (ZMod p)).rowOutput env)))
    : let chip := (supportedChipFor (p := p) id)
      (chip.kind.view (chip.table.rowInput env) (chip.table.rowOutput env)).is_real = 1 →
      property (chip.kind.view (chip.table.rowInput env) (chip.table.rowOutput env)) := by
  dsimp only
  cases id with
  | storeByte =>
    intro active
    exact byte rfl active
  | storeHalf =>
    intro active
    exact half rfl active
  | storeWord =>
    intro active
    exact word rfl active
  | storeDouble =>
    intro active
    exact double rfl active
  | jal | jalr | uType =>
    intro _
    apply noWrite
    exact Trace.CommitEffect.destination_memWrite _
  | _ => intro _; exact noWrite _ rfl

end SP1Clean.Soundness.ProtectedLocalCore
