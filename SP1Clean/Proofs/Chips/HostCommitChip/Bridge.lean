import SP1Clean.Proofs.Chips.HostCommitChip.Formal
import SP1Clean.Model.Core.HostExecution

/-! # Native commitment rows implement mutable host slots

Decode the bank carried by the state ledger and compare with the independent host interpreter.
The complete host effect changes only the selected slot; previously committed values may differ
from the new one. The state and instruction ledgers still need assembly into the mixed machine.
-/

namespace SP1Clean.HostCommitChip

open SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def State.decode (state : State (ZMod p)) : Vector (BitVec 32) 8 :=
  state.values.map fun word => (Word.toBitVec64 word).setWidth 32

def State.apply (state : State (ZMod p)) (deferred : Bool) (host : HostState) : HostState :=
  if deferred then { host with deferred := state.decode } else { host with committed := state.decode }

private theorem slot_bound (slot : Fin 8) : Word.isU64 (slotWord (R := ZMod p) slot) := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  apply Word.isU64_of_cases <;> simp only [slotWord, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero]
  · rw [ZMod.val_natCast_of_lt (by have := slot.isLt; omega)]
    exact lt_trans slot.isLt (by norm_num)
  all_goals norm_num

private theorem slot_value (slot : Fin 8) : Word.toNat (slotWord (R := ZMod p) slot) = slot.val := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  simp only [Word.toNat, slotWord, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero, zero_mul, add_zero]
  rw [ZMod.val_natCast_of_lt (by have := slot.isLt; omega)]

omit [Fact (2 ^ 25 < p)] in
/-- The decoded state changes exactly the selected 32-bit slot. -/
theorem next_decode (input : Inputs (ZMod p)) (slot : Fin 8) :
    (input.next slot).decode = input.previous.decode.set slot (Word.toBitVec64 input.call.arg2 |>.setWidth 32) := by
  simp only [State.decode, Inputs.next, Vector.map_set]

/-- One native commitment transition is exactly the independent host interpreter's complete effect. -/
theorem executeKind_of_spec (deferred : Bool) (slot : Fin 8) (input : Inputs (ZMod p))
    (valid : Spec deferred slot input) (host : HostState) (policy : HostPolicy)
    (characteristic : policy.characteristic = p) (context : HostReadContext) :
    (input.previous.apply deferred host).executeKind policy context
      (if deferred then .commitDeferred else .commit)
      (Word.toBitVec64 input.call.arg1) (Word.toBitVec64 input.call.arg2) =
      some ⟨(input.next slot).apply deferred host, none⟩ := by
  have index := valid.1.2.1
  have word : Word.isU64 input.call.arg2 := valid.1.2.2.2.2.1
  have value : Word.toNat input.call.arg2 < bound p deferred := valid.1.2.2.2.2.2
  have indexNat : (Word.toBitVec64 input.call.arg1).toNat = slot.val := by
    rw [index, Word.toBitVec64_toNat (slot_bound slot), slot_value]
  have valueNat : (Word.toBitVec64 input.call.arg2).toNat = Word.toNat input.call.arg2 :=
    Word.toBitVec64_toNat word
  cases deferred
  · simp only [bound, Bool.false_eq_true, ↓reduceIte] at value
    simp only [State.apply, Bool.false_eq_true, ↓reduceIte, HostState.executeKind, indexNat,
      dif_pos slot.isLt, valueNat, if_pos value, next_decode]
  · simp only [bound, ↓reduceIte, lt_min_iff] at value
    simp only [State.apply, ↓reduceIte, HostState.executeKind, indexNat,
      dif_pos slot.isLt, valueNat, characteristic, if_pos value, next_decode]

end SP1Clean.HostCommitChip
