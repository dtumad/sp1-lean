import SP1Clean.FormalModel.Contracts.SailBoundary

/-! # Reading the Sail retirement count from the terminal word -/

namespace SP1Clean.Soundness.HostObserved

open Semantics SP1Clean.OrdinaryObservation
open LeanRV64D (Register)

private theorem present_counter {initial outgoing : Option (BitVec 64)} {delta : ℕ}
    (left : initial.isSome) (right : outgoing.isSome)
    (same : outgoing.getD 0 = initial.getD 0 + BitVec.ofNat 64 delta) :
    outgoing = initial.map (fun value => value + BitVec.ofNat 64 delta) := by
  cases initial <;> cases outgoing <;> simp_all

private theorem enabled_count {p : ℕ} [Fact p.Prime] (snapshot : SailSnapshot) (n : ℕ) :
    n * (startFor (p := p) snapshot).enabled.val = if retirementEnabled snapshot.realize then n else 0 := by
  have flag : retirementEnabled snapshot.skeleton = retirementEnabled snapshot.realize := by
    unfold retirementEnabled
    rfl
  change n * ((if retirementEnabled snapshot.skeleton then 1 else 0 : ZMod p)).val = _
  rw [flag]
  cases retirementEnabled snapshot.realize <;> simp [ZMod.val_one'' (Fact.out (p := p.Prime)).ne_one]

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The terminal counter and the exact ordinary count determine the complete optional Sail
entry, including 64-bit wraparound. Source and target validation authenticate both keys. -/
theorem retirement_of_counter {image : ProgramImage} {source target : ExecutionSnapshot}
    {header : SP1PublicIO (ZMod p)} {counter : Word (ZMod p)} {n : ℕ}
    (valid : ExecutionSourceValid image source) (boundary : SailBoundary.Spec source target header)
    (terminal : counter = (finalFor source.sail target.sail).counter)
    (sum : Word.toBitVec64 counter = Word.toBitVec64 (startFor (p := p) source.sail).counter +
      BitVec.ofNat 64 (n * (startFor (p := p) source.sail).enabled.val)) :
    target.sail.registers.get? Register.minstret = (source.sail.registers.get? Register.minstret).map
      (fun value => value + BitVec.ofNat 64 (if retirementEnabled source.sail.realize then n else 0)) := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
  have startValue : Word.toBitVec64 (startFor (p := p) source.sail).counter =
      (source.sail.registers.get? Register.minstret).getD 0 :=
    Target.toBitVec64_bitVecToWord _
  have finalValue : Word.toBitVec64 (finalFor (p := p) source.sail target.sail).counter =
      (target.sail.registers.get? Register.minstret).getD 0 :=
    Target.toBitVec64_bitVecToWord _
  exact present_counter (Std.ExtDHashMap.isSome_get?_iff_mem.mpr (valid.2.1.init Register.minstret))
    (Std.ExtDHashMap.isSome_get?_iff_mem.mpr (boundary.initialized Register.minstret))
    (by simpa only [terminal, finalValue, startValue, enabled_count] using sum)

end SP1Clean.Soundness.HostObserved
