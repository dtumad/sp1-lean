import SP1Clean.FormalModel.Contracts.HintQueueSnapshot

/-! # Fixed cursor positions inside a target hint buffer -/

namespace SP1Clean.HostHintSnapshot

variable {p : ℕ} [Fact p.Prime]

/-- The cursor before a buffer word, or just past its last word. -/
def position (start : ℕ) (links : Links (ZMod p)) (words i : ℕ) : Cursor (ZMod p) :=
  ⟨Address.ofNat (start + i), if i = words then links.tail else links.head,
    if 0 < i ∧ i < words then links.tail else 0⟩

/-- Every actual field-valued link pair follows the fixed buffer schedule at both ends. -/
theorem step_positions (start : ℕ) (links : Links (ZMod p)) (length i : ℕ) (word : BitVec 64) (live : i < length / 8 + 1) :
    let s := shape (p := p) (start + i) i length word
    s.before links = position start links (length / 8 + 1) i ∧
      s.after links = position start links (length / 8 + 1) (i + 1) := by
  have before : i ≠ length / 8 + 1 := by omega
  have nextPositive : 0 < i + 1 := by omega
  have begins : 0 < i ↔ i ≠ 0 := by omega
  have ends : i + 1 = length / 8 + 1 ↔ i = length / 8 := by omega
  have continues : i + 1 < length / 8 + 1 ↔ i ≠ length / 8 := by omega
  have erased : links.tail.map (fun _ => (0 : ZMod p)) = 0 := by
    ext j hj
    simp
  simp only [Shape.before, Shape.after, position, shape, before, live, nextPositive, begins, ends,
    continues, and_true, true_and, ↓reduceIte]
  by_cases first : i = 0 <;> by_cases last : i = length / 8
  all_goals
    first | have hf : (i = 0) = True := eq_true first | have hf : (i = 0) = False := eq_false first
    first | have hl : (i = length / 8) = True := eq_true last | have hl : (i = length / 8) = False := eq_false last
    simp [ne_eq, hf, hl, erased, Nat.add_assoc]

end SP1Clean.HostHintSnapshot
