import SP1Clean.FormalModel.Contracts.ResourceBoundary
import SP1Clean.FormalModel.Contracts.OrdinaryObservationBoundary
import SP1Clean.Semantics.Execution.SailFinalCheck

/-! # Supplied Sail target: invariant fields and actual public endpoints

This is one part of complete Sail target binding. Register presence and invariant values are
checked as finite snapshot data. The public clock and PC are tied to the same target. Dynamic
nextPC and retirement, and full host-field reconstruction, are separate remaining obligations.
-/

namespace SP1Clean.SailBoundary

open Semantics Soundness.Target
open LeanRV64D (Register)

/-- Equal clocks force an empty segment. All optional bookkeeping then stays exactly at
its incoming value, including the full retirement count and the full-width next PC. -/
def checkRetirement (source target : ExecutionSnapshot) : Bool :=
  if source.clock = target.clock then
    OrdinaryObservation.quiet source.sail target.sail &&
      (target.sail.registers.get? Register.minstret : Option (BitVec 64)) ==
        source.sail.registers.get? Register.minstret
  else
    OrdinaryObservation.quiet source.sail target.sail || OrdinaryObservation.refreshed source.sail target.sail

/-- Check invariant Sail fields, endpoint ranges and the possible ordinary-retirement modes. -/
def checkStatic (source target : ExecutionSnapshot) : Bool :=
  source.sail.checkFrame target.sail && decide (target.clock < 2 ^ 48) &&
    decide (target.pc.toNat < 2 ^ 48) &&
    checkRetirement source target

/-- Equal realized boundaries pass the executable identity check whenever the incoming
architectural state is initialized and representable. Their finite RAM histories may differ. -/
theorem checkStatic_of_realize_eq {source target : ExecutionSnapshot}
    (same : source.realize = target.realize) (initialized : source.sail.skeleton.isInitialized)
    (clockBound : source.clock < 2 ^ 48) (pcBound : source.pc.toNat < 2 ^ 48) :
    checkStatic source target = true := by
  have clock : source.clock = target.clock := congrArg ExecutionState.clock same
  have sail : source.sail.realize = target.sail.realize := congrArg ExecutionState.sail same
  obtain ⟨regs, _, cycles, output⟩ := (SailSnapshot.realize_eq_iff ..).mp sail
  have frame : source.sail.checkFrame target.sail = true := by
    apply (SailSnapshot.checkFrame_iff ..).mpr
    refine ⟨?_, fun _ _ => by rw [regs], cycles, output⟩
    change ∀ r, r ∈ target.sail.registers
    rw [← regs]
    exact initialized
  have pc : source.pc = target.pc := by simp only [ExecutionSnapshot.pc, regs]
  have quiet := (OrdinaryObservation.quiet_iff source.sail target.sail).mpr (by simp only [regs, and_self])
  simp [checkStatic, frame, ← clock, ← pc, checkRetirement, quiet, regs]
  exact ⟨clockBound, pcBound⟩

/-- The outgoing public State token is the canonical clock and PC of the supplied target. -/
def TargetFor {p : ℕ} [Fact p.Prime] (target : ExecutionSnapshot) (input : SP1PublicIO (ZMod p)) : Prop :=
  ResourceBoundary.ClockFor target input ∧
    input.final_pc0 = (bitVecToWord target.pc)[0] ∧
    input.final_pc1 = (bitVecToWord target.pc)[1] ∧
    input.final_pc2 = (bitVecToWord target.pc)[2]

/-- SP1's execution flag records a change of the authenticated timestamp. -/
def executionShardFlag {F : Type} [Zero F] [One F] (source target : ExecutionSnapshot) : F :=
  if source.clock = target.clock then 0 else 1

/-- The invariant-field, shard flag, and public-endpoint portion of complete Sail target validation. -/
def Spec {p : ℕ} [Fact p.Prime] (source target : ExecutionSnapshot) (input : SP1PublicIO (ZMod p)) : Prop :=
  checkStatic source target = true ∧ TargetFor target input ∧
    input.is_execution_shard = executionShardFlag source target

/-- The existing canonical clock decoder identifies the supplied target's natural clock. -/
theorem TargetFor.clock {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]
    {target : ExecutionSnapshot} {input : SP1PublicIO (ZMod p)}
    (bound : target.clock < 2 ^ 48) (binding : TargetFor target input) :
    Semantics.clkNat input.final_clk_high input.final_clk_low = target.clock :=
  ResourceBoundary.ClockFor.clock bound binding.1

/-- Reuse the source endpoint decoder on the same public limbs viewed as the outgoing endpoint. -/
theorem TargetFor.pc {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
    {target : ExecutionSnapshot} {input : SP1PublicIO (ZMod p)}
    (bound : target.pc.toNat < 2 ^ 48) (binding : TargetFor target input) :
    Semantics.pcBits input.final_pc0 input.final_pc1 input.final_pc2 = target.pc := by
  let incoming : SP1PublicIO (ZMod p) := { input with
    init_clk_0_16 := input.final_clk_0_16
    init_clk_16_24 := input.final_clk_16_24
    init_clk_24_32 := input.final_clk_24_32
    init_clk_32_48 := input.final_clk_32_48
    init_pc0 := input.final_pc0
    init_pc1 := input.final_pc1
    init_pc2 := input.final_pc2 }
  have source : incoming.SourceFor target := ⟨binding.1.1, binding.1.2, binding.2⟩
  exact SP1PublicIO.SourceFor.pc bound source

/-- The static assertion enforces the complete invariant-field check. -/
theorem Spec.frame {p : ℕ} [Fact p.Prime]
    {source target : ExecutionSnapshot} {input : SP1PublicIO (ZMod p)} (spec : Spec source target input) :
    source.sail.checkFrame target.sail = true := by
  have checked := spec.1
  simp only [checkStatic, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.1.1.1

/-- Endpoint ranges are checked before any reduction modulo the AIR characteristic. -/
theorem Spec.ranges {p : ℕ} [Fact p.Prime]
    {source target : ExecutionSnapshot} {input : SP1PublicIO (ZMod p)} (spec : Spec source target input) :
    target.clock < 2 ^ 48 ∧ target.pc.toNat < 2 ^ 48 := by
  have checked := spec.1
  simp only [checkStatic, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨checked.1.1.2, checked.1.2⟩

/-- The supplied bookkeeping admits the empty-retirement case or the refreshed case. -/
theorem Spec.retirementModes {p : ℕ} [Fact p.Prime]
    {source target : ExecutionSnapshot} {input : SP1PublicIO (ZMod p)} (spec : Spec source target input) :
    OrdinaryObservation.quiet source.sail target.sail = true ∨
      OrdinaryObservation.refreshed source.sail target.sail = true := by
  have checked := spec.1
  simp only [checkStatic, Bool.and_eq_true] at checked
  have modes := checked.2
  unfold checkRetirement at modes
  split at modes
  · simp only [Bool.and_eq_true] at modes
    exact Or.inl modes.1
  · simpa only [Bool.or_eq_true] using modes

/-- The accepted static assertion checks all optional retirement bookkeeping on an identity. -/
theorem Spec.equal_clock {p : ℕ} [Fact p.Prime]
    {source target : ExecutionSnapshot} {input : SP1PublicIO (ZMod p)}
    (spec : Spec source target input) (clock : source.clock = target.clock) :
    OrdinaryObservation.quiet source.sail target.sail = true ∧
      target.sail.registers.get? Register.minstret = source.sail.registers.get? Register.minstret := by
  have checked := spec.1
  simp only [checkStatic, Bool.and_eq_true] at checked
  simpa only [checkRetirement, ite_eq_left clock, Bool.and_eq_true, beq_iff_eq] using checked.2

/-- No missing target GPR can be hidden by the Memory projection's zero fallback. -/
theorem Spec.initialized {p : ℕ} [Fact p.Prime]
    {source target : ExecutionSnapshot} {input : SP1PublicIO (ZMod p)} (spec : Spec source target input) :
    target.sail.skeleton.isInitialized := (SailSnapshot.checkFrame_iff _ _).mp spec.frame |>.1

/-- The checked target's Memory projection is its real Sail register/memory observation. -/
theorem Spec.memorySnapshot_realizes {p : ℕ} [Fact p.Prime]
    {source target : ExecutionSnapshot} {input : SP1PublicIO (ZMod p)} (spec : Spec source target input) :
    target.sail.memorySnapshot.Realizes target.sail.realize :=
  target.sail.memorySnapshot_realizes spec.initialized

end SP1Clean.SailBoundary
