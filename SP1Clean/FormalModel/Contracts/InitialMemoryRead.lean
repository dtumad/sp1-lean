import SP1Clean.FormalModel.Contracts.InitialMemory
import SP1Clean.Model.Core.MemoryWord
import SP1Clean.Model.Core.Boot

/-! # The native initial-memory word-read contract

The eight byte lookups are internal columns. The public contract states that the returned word
is the little-endian initial memory value and that its complete byte footprint is in bounds.
-/

namespace SP1Clean.InitialMemoryRead

open SP1Clean.Model.Core

structure Inputs (F : Type) where
  bytes : Vector (InitialMemoryLookup.Inputs F) 8
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

variable {p : ℕ} [Fact p.Prime]

/-- A full in-bounds 64-bit read from the canonical initial image. -/
def Spec (memory : ByteMemory) (input : Inputs (ZMod p)) (output : Word (ZMod p)) : Prop :=
  Word.isU64 input.bytes[0].address ∧ Word.toNat input.bytes[0].address + 8 ≤ 2 ^ 48 ∧
    Word.isU64 output ∧
      Word.toBitVec64 output = memory.readWord (Word.toNat input.bytes[0].address)

/-- The native word-read contract reaches the actual initial Sail memory, without a provider premise. -/
theorem Spec.initialSailState (image : ProgramImage) (input : Inputs (ZMod p)) (output : Word (ZMod p))
    (spec : Spec image.initialMemory input output) :
    Semantics.ramWord64? image.initialSailState (Word.toBitVec64 input.bytes[0].address) =
      some (Word.toBitVec64 output) := by
  have footprint : (Word.toBitVec64 input.bytes[0].address).toNat + 8 ≤ 2 ^ 48 := by
    rw [Word.toBitVec64_toNat spec.1]
    exact spec.2.1
  rw [image.initialSailState_word _ footprint, Word.toBitVec64_toNat spec.1, spec.2.2.2]

end SP1Clean.InitialMemoryRead
