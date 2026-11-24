import SP1Clean.Math.Address
import SP1Clean.Semantics.Transition.MicroTime
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Canonical 48-bit clocks shared by State, Memory and native read-only observations -/

namespace SP1Clean

open Semantics

/-- Split the middle of a 48-bit timestamp at both native bus boundaries. -/
structure ClockParts (F : Type) where
  /-- Bits 0 through 15. -/
  low : F
  /-- Bits 16 through 23. -/
  midLow : F
  /-- Bits 24 through 31. -/
  midHigh : F
  /-- Bits 32 through 47. -/
  high : F
deriving ProvableStruct
provable_struct_eval_lemmas ClockParts

/-- Upper Memory bus timestamp limb. -/
def ClockParts.high24 {F} [Add F] [Mul F] [OfNat F 256] (parts : ClockParts F) : F :=
  parts.midHigh + parts.high * 256

/-- Lower Memory bus timestamp limb. -/
def ClockParts.low24 {F} [Add F] [Mul F] [OfNat F 65536] (parts : ClockParts F) : F :=
  parts.low + parts.midLow * 65536

/-- Version bus timestamp in its three 16-bit limbs. -/
def ClockParts.address {F} [Add F] [Mul F] [OfNat F 256] (parts : ClockParts F) : fields 3 F :=
  #v[parts.low, parts.midLow + parts.midHigh * 256, parts.high]

/-- Each of the four chunks fits its place in both timestamp encodings. -/
def ClockParts.Bounded {p} (parts : ClockParts (ZMod p)) :=
  parts.low.val < 2 ^ 16 ∧ parts.midLow.val < 2 ^ 8 ∧
    parts.midHigh.val < 2 ^ 8 ∧ parts.high.val < 2 ^ 16

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
private theorem pack (x y : ZMod p) (k : ℕ) (fits : x.val + y.val * k < p) :
    (x + y * (k : ZMod p)).val = x.val + y.val * k := by
  have cast : ((x.val + y.val * k : ℕ) : ZMod p) = x + y * (k : ZMod p) := by simp
  rw [← cast, ZMod.val_natCast_of_lt fits]

/-- A bounded split timestamp gives a canonical three-limb address on the observer bus. -/
theorem ClockParts.address_bounded (parts : ClockParts (ZMod p)) (bound : parts.Bounded) : Address.Bounded parts.address := by
  obtain ⟨lo, midLo, midHi, hi⟩ := bound
  have field := Fact.out (p := 2 ^ 24 < p)
  have mid := pack parts.midLow parts.midHigh 256 (by omega)
  simp only [Nat.cast_ofNat] at mid
  intro i
  fin_cases i
  · exact lo
  · change (parts.midLow + parts.midHigh * 256).val < _
    rw [mid]; omega
  · exact hi

/-- In either representation, the physical timestamp denotes exactly the same natural. -/
theorem ClockParts.time (parts : ClockParts (ZMod p)) (bound : parts.Bounded) :
    Address.toNat parts.address = clkNat parts.high24 parts.low24 := by
  obtain ⟨low, midLow, midHigh, high⟩ := bound
  have field := Fact.out (p := 2 ^ 24 < p)
  have lo := pack parts.low parts.midLow 65536 (by omega)
  have mid := pack parts.midLow parts.midHigh 256 (by omega)
  have hi := pack parts.midHigh parts.high 256 (by omega)
  change (parts.low.val + (parts.midLow + parts.midHigh * 256).val * 65536 + parts.high.val * 4294967296) =
    (parts.midHigh + parts.high * 256).val * 16777216 + (parts.low + parts.midLow * 65536).val
  simp only [Nat.cast_ofNat] at mid hi lo
  rw [mid, hi, lo]
  omega

/-- Construct the four pieces from the two bounded Memory limbs. -/
def ClockParts.split (hi lo : ZMod p) : ClockParts (ZMod p) :=
  ⟨(lo.val % 65536 : ℕ), (lo.val / 65536 : ℕ), (hi.val % 256 : ℕ), (hi.val / 256 : ℕ)⟩

theorem ClockParts.split_spec (hi lo : ZMod p) (hiBound : hi.val < 2 ^ 24) (loBound : lo.val < 2 ^ 24) :
    (split hi lo).Bounded ∧ (split hi lo).high24 = hi ∧ (split hi lo).low24 = lo := by
  have primeBound := Fact.out (p := 2 ^ 24 < p)
  refine ⟨?_, ?_, ?_⟩
  · unfold split Bounded
    repeat' rw [ZMod.val_natCast_of_lt (by omega)]
    exact ⟨by omega, by omega, by omega, by omega⟩
  · have recombine : hi.val % 256 + hi.val / 256 * 256 = hi.val := by omega
    simpa only [split, high24, low24, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
      using congrArg (fun n : ℕ => (n : ZMod p)) recombine
  · have recombine : lo.val % 65536 + lo.val / 65536 * 65536 = lo.val := by omega
    simpa only [split, high24, low24, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
      using congrArg (fun n : ℕ => (n : ZMod p)) recombine

end SP1Clean
