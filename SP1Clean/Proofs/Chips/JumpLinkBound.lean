import SP1Clean.Math.SP1Field
import SP1Clean.Proofs.Chips.JalChip.Formal
import SP1Clean.Proofs.Chips.JalrChip.Formal
import SP1Clean.Semantics.ISA.JumpLink

/-! # Released physical link-write bounds

Both native jump chips constrain the high link limb to zero and use the same gated 64-bit addition
as the released AIR. The bound follows for every satisfying row assignment in the SP1 field.
-/

namespace SP1Clean.JumpLink
open Circuit Semantics

/-- Assemble the same word the two link additions receive from the CPU state. -/
def pcWord (pc : Vector (ZMod SP1Prime) 3) : Word (ZMod SP1Prime) := #v[pc[0], pc[1], pc[2], 0]

private theorem below48 {word : Word (ZMod SP1Prime)} (valid : word.isU64) (high : word[3] = 0) :
    word.toNat < 2 ^ 48 := by
  obtain ⟨a, b, c, _⟩ := Word.lt_cases_of_isU64 valid
  rw [Word.toNat_def, high, ZMod.val_zero]
  omega

private theorem bound_of_sum {pc link : Word (ZMod SP1Prime)} (pcBound : pc.isU64) (pcHigh : pc[3] = 0)
    (linkBound : link.isU64) (linkHigh : link[3] = 0)
    (sum : link.toBitVec64 = pc.toBitVec64 + Word.toBitVec64 (#v[4, 0, 0, 0] : Word (ZMod SP1Prime))) :
    pc.toNat + 4 < 2 ^ 48 := by
  have hp := below48 pcBound pcHigh
  have hl := below48 linkBound linkHigh
  rw [show Word.toBitVec64 (#v[4, 0, 0, 0] : Word (ZMod SP1Prime)) = 4#64 from by decide] at sum
  have total := congrArg BitVec.toNat sum
  rw [Word.toBitVec64_toNat linkBound, BitVec.toNat_add, Word.toBitVec64_toNat pcBound] at total
  change link.toNat = (pc.toNat + 4) % 2 ^ 64 at total
  rw [Nat.mod_eq_of_lt (by omega)] at total
  exact total ▸ hl

private def Overflow (pc : Vector (ZMod SP1Prime) 3) (gate : ZMod SP1Prime) : Prop :=
  gate = 1 ∧ (pcWord pc).isU64 ∧ 2 ^ 48 ≤ (pcWord pc).toNat + 4

open SP1Clean.JalChip in
private theorem jal_rejects : GeneralFormalCircuit.Soundness (ZMod SP1Prime) JalChip.main
    (fun input _ => Overflow input.state.pc (input.is_real - input.adapter.op_a_0)) (fun _ _ _ => False) := by
  circuit_proof_start
  obtain ⟨gate, pcBound, overflow⟩ := h_assumptions
  obtain ⟨_, _, _, add, top, _⟩ := h_holds
  obtain ⟨bound, value⟩ := add ⟨fun _ => ⟨pcBound, Word.isU64_four⟩, Or.inr gate⟩ gate
  exact (Nat.not_lt_of_ge overflow (bound_of_sum pcBound rfl bound top value)).elim

open SP1Clean.JalrChip in
private theorem jalr_rejects : GeneralFormalCircuit.Soundness (ZMod SP1Prime) JalrChip.main
    (fun input _ => Overflow input.state.pc (input.is_real - input.adapter.op_a_0)) (fun _ _ _ => False) := by
  circuit_proof_start
  obtain ⟨gate, pcBound, overflow⟩ := h_assumptions
  obtain ⟨_, _, _, _, add, top, _⟩ := h_holds
  obtain ⟨bound, value⟩ := add ⟨fun _ => ⟨pcBound, Word.isU64_four⟩, Or.inr gate⟩ gate
  exact (Nat.not_lt_of_ge overflow (bound_of_sum pcBound rfl bound top value)).elim

/-- Soundness of the actual JAL link gate at the released field characteristic. -/
theorem jal : GeneralFormalCircuit.Soundness (ZMod SP1Prime) JalChip.main JalChip.Assumptions
    (fun input _ _ => JumpLinkFits (pcWord input.state.pc).toNat (input.is_real - input.adapter.op_a_0 = 1)) := by
  intro offset env vars input eq assumptions holds
  refine ⟨fun enabled => ?_, (JalChip.soundness offset env vars input eq assumptions holds).2⟩
  by_contra! overflow
  exact (jal_rejects offset env vars input eq ⟨enabled, assumptions.2, overflow⟩ holds).1

/-- Soundness of the actual JALR link gate, independently of its masked jump target. -/
theorem jalr : GeneralFormalCircuit.Soundness (ZMod SP1Prime) JalrChip.main JalrChip.Assumptions
    (fun input _ _ => JumpLinkFits (pcWord input.state.pc).toNat (input.is_real - input.adapter.op_a_0 = 1)) := by
  intro offset env vars input eq assumptions holds
  refine ⟨fun enabled => ?_, (JalrChip.soundness offset env vars input eq assumptions holds).2⟩
  by_contra! overflow
  exact (jalr_rejects offset env vars input eq ⟨enabled, assumptions.2.2, overflow⟩ holds).1

end SP1Clean.JumpLink
