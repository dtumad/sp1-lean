import SP1Clean.Native.Operations.CommitmentStatement

/-! # Fixed declarations imply semantic statement agreement

Membership is supplied by the fixed declaration provider and the complete balanced ledger.
This bridge decodes that authenticated payload into the independent execution-event contract;
it does not assume that the mutable final bank contains every statement word.
-/

namespace SP1Clean.CommitmentDeclaration

open Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private theorem index_injective (a b : Fin 8) (same : (a.val : ZMod p) = b.val) : a = b := by
  apply Fin.ext
  have small (i : Fin 8) : i.val < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    omega
  have equal := congrArg ZMod.val same
  simpa only [ZMod.val_natCast_of_lt (small a), ZMod.val_natCast_of_lt (small b)] using equal

private theorem fixed_word (statement : CommitmentStatement) (deferred : Bool) (slot : Fin 8)
    (value : Word (ZMod p)) (index : Fin 8)
    (same : encode statement deferred index =
      (⟨if deferred then 1 else 0, slot.val, value, 1⟩ : Row (ZMod p))) :
    (if deferred then statement.commitDeferred else statement.commit) = true ∧
      Word.toBitVec64 value = ((statement.bank deferred)[slot]).setWidth 64 := by
  have sameIndex := index_injective index slot (congrArg Row.slot same)
  subst index
  have flag := congrArg Row.flag same
  have word := congrArg Row.value same
  constructor
  · by_contra disabled
    simp [encode, disabled] at flag
  · dsimp only at word
    rw [← word]
    exact Soundness.Target.toBitVec64_bitVecToWord _

/-- An active authenticated request has the statement's flag and exact 32-bit word. -/
theorem agreement_of_member (statement : CommitmentStatement) (deferred : Bool) (slot : Fin 8)
    (value : Word (ZMod p))
    (member : (⟨if deferred then 1 else 0, slot.val, value, 1⟩ : Row (ZMod p)) ∈ rows statement) :
    (if deferred then statement.commitDeferred else statement.commit) = true ∧
      Word.toBitVec64 value = ((statement.bank deferred)[slot]).setWidth 64 := by
  rcases List.mem_append.mp member with member | member
  all_goals obtain ⟨index, same⟩ := List.mem_ofFn.mp member
  · cases deferred
    · exact fixed_word statement false slot value index same
    · have impossible := congrArg Row.deferred same
      simp [encode] at impossible
  · cases deferred
    · have impossible := congrArg Row.deferred same
      simp [encode] at impossible
    · exact fixed_word statement true slot value index same

/-- The provider authenticates actual syscall observations, including partial declarations. -/
theorem matches_declaration_of_member (statement : CommitmentStatement) (deferred : Bool) (slot : Fin 8)
    (value : Word (ZMod p)) (event : Machine.CoreSyscallEvent)
    (member : (⟨if deferred then 1 else 0, slot.val, value, 1⟩ : Row (ZMod p)) ∈ rows statement)
    (argument : event.arg1 = BitVec.ofNat 64 slot.val)
    (word : event.arg2 = Word.toBitVec64 value) : statement.MatchesDeclaration deferred event := by
  intro _
  obtain ⟨flag, agreement⟩ := agreement_of_member statement deferred slot value member
  exact ⟨flag, slot, argument, word.trans agreement⟩

end SP1Clean.CommitmentDeclaration
