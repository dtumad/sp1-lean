import SP1Clean.Model.Core.MemoryIntervals
import SP1Clean.Model.Core.SailMemory

/-! # Sparse memory lookup and Sail-map regressions -/

namespace SP1CleanTest.Core.MemoryIntervals

open SP1Clean.Model.Core

private def memory : ByteMemory := ⟨[(7, 42), (0, 13), (7, 9), (15, 255), (16, 99)]⟩

example : (List.range 17).map (fun query =>
    (memory.intervalAt? 16 query).map (·.value)) =
    [some 13, some 0, some 0, some 0, some 0, some 0, some 0, some 42,
      some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 255, none] := by
  native_decide

example : (memory.intervals 16).length ≤ 2 * memory.entries.length + 1 :=
  memory.intervals_length_le 16

example : (memory.intervalAt? 0 0).isSome = false := by native_decide

example : ((ByteMemory.mk []).intervalAt? (2 ^ 48) (2 ^ 48 - 1)).map (·.value) = some 0 := by
  native_decide

example : ((ByteMemory.mk []).intervalAt? (2 ^ 48) (2 ^ 48)).isSome = false := by native_decide

example : (memory.toSailMemory 16).get? 7 = some 42 := by native_decide

example : (memory.toSailMemory 16).get? 16 = none := by native_decide

example : ((memory.writeBytes 6 [1, 2, 3]).toSailMemory 16).get? 7 = some 2 := by native_decide

end SP1CleanTest.Core.MemoryIntervals
