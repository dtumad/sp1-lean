import SP1Clean.Model.Core.MemoryTable
import SP1Clean.Extracted.LtOperationUnsigned

/-! # Native initial-memory byte lookup contract

The public meaning is a byte read from the canonical sparse initial image. Interval endpoints and
comparison columns are internal row data; callers of the semantic theorem only see the bounded
address and its byte value. The executable input constructor supplies those internal columns.
-/

namespace SP1Clean.InitialMemoryLookup

open SP1Clean.Model.Core

structure Inputs (F : Type) where
  address : Word F
  interval : MemoryIntervalRow F
  lowerCompare : Extracted.LtOperationUnsigned F
  upperCompare : Extracted.LtOperationUnsigned F
deriving ProvableStruct

variable {p : ℕ} [Fact p.Prime]

/-- The lookup establishes the byte at an in-range address in the fixed initial memory. -/
def Spec (memory : ByteMemory) (limit : ℕ) (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.address ∧ Word.toNat input.address < limit ∧
    input.interval.value = (memory.read (Word.toNat input.address)).toNat

end SP1Clean.InitialMemoryLookup
