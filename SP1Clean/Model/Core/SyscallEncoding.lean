module

public import SP1Clean.Model.Core.SyscallCode
public import SP1Clean.Model.Semantics.Decode
public import SP1Clean.Math.WordEquality

/-! # Canonical field encoding of the native syscall profile

The four-limb representation preserves the complete register, including zero upper limbs.
Membership in the encoded semantic inventory is independent of prover data or a lookup mechanism.
-/

@[expose] public section

namespace SP1Clean.Model.Core.SyscallKind

open SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Encode the full register as four little-endian 16-bit limbs. -/
def encode (kind : SyscallKind) : Word (ZMod p) := bitVecToWord kind.code

/-- Enumerating the encoded inventory is exactly the semantic full-word profile. -/
theorem mem_encoded_iff (word : Word (ZMod p)) :
    word ∈ all.map encode ↔ word.isU64 ∧ Supported word.toBitVec64 := by
  rw [List.mem_map]
  constructor
  · rintro ⟨kind, _, rfl⟩
    exact ⟨isU64_bitVecToWord _, kind, (toBitVec64_bitVecToWord _).symm⟩
  · rintro ⟨bound, kind, equal⟩
    refine ⟨kind, mem_all kind, Word.eq_of_toBitVec64_eq (isU64_bitVecToWord _) bound ?_⟩
    exact (toBitVec64_bitVecToWord _).trans equal

end SP1Clean.Model.Core.SyscallKind
