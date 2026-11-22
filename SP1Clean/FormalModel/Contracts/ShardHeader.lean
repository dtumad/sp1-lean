import SP1Clean.FormalModel.Contracts.CommitmentBoundary
import SP1Clean.FormalModel.Contracts.SailBoundary

/-! # Public header of a local execution

The public clock and PC describe the two complete endpoints. Exit records a HALT in this
segment, while the commitment fields encode the verifier's immutable statement.
-/

namespace SP1Clean.SP1StateBoundary
open Semantics Soundness.Target

variable {p : ℕ} [Fact p.Prime]

/-- Encode the two clocks in SP1's (16, 8, 8, 16) layout, the two PCs in 16-bit limbs,
and the segment exit and commitment statement in their released public formats. -/
def ofEndpoints (initClk : ℕ) (initPc : BitVec 64) (finalClk : ℕ) (finalPc : BitVec 64)
    (exit : ℕ) (statement : CommitmentStatement) : SP1StateBoundary (ZMod p) where
  init_clk_0_16 := (initClk % 2 ^ 16 : ℕ)
  init_clk_16_24 := (initClk / 2 ^ 16 % 2 ^ 8 : ℕ)
  init_clk_24_32 := (initClk / 2 ^ 24 % 2 ^ 8 : ℕ)
  init_clk_32_48 := (initClk / 2 ^ 32 % 2 ^ 16 : ℕ)
  init_pc0 := (bitVecToWord initPc)[0]
  init_pc1 := (bitVecToWord initPc)[1]
  init_pc2 := (bitVecToWord initPc)[2]
  final_clk_0_16 := (finalClk % 2 ^ 16 : ℕ)
  final_clk_16_24 := (finalClk / 2 ^ 16 % 2 ^ 8 : ℕ)
  final_clk_24_32 := (finalClk / 2 ^ 24 % 2 ^ 8 : ℕ)
  final_clk_32_48 := (finalClk / 2 ^ 32 % 2 ^ 16 : ℕ)
  final_pc0 := (bitVecToWord finalPc)[0]
  final_pc1 := (bitVecToWord finalPc)[1]
  final_pc2 := (bitVecToWord finalPc)[2]
  exit_code := exit
  is_execution_shard := if initClk = finalClk then 0 else 1
  committed_value_digest := CommitmentBoundary.committed statement
  deferredProofsDigest := CommitmentBoundary.deferred statement
  commitSyscall := if statement.commit then 1 else 0
  commitDeferredSyscall := if statement.commitDeferred then 1 else 0

/-- The new exit receipt for this segment, including a real HALT with code zero. -/
def haltCode (source target : ExecutionSnapshot) : Option (BitVec 32) :=
  if source.host.exitCode = none then target.host.exitCode else none

/-- The public header constructed from exactly the complete endpoints and statement. -/
def ofExecution (source target : ExecutionSnapshot) (statement : CommitmentStatement) :
    SP1StateBoundary (ZMod p) :=
  ofEndpoints source.clock source.pc target.clock target.pc ((haltCode source target).getD 0).toNat statement

private theorem clock_low (n : ℕ) :
    ((n % 2 ^ 16 : ℕ) : ZMod p) + (n / 2 ^ 16 % 2 ^ 8 : ℕ) * 65536 = (n % 2 ^ 24 : ℕ) := by
  change _ + _ * ((65536 : ℕ) : ZMod p) = _
  rw [← Nat.cast_mul, ← Nat.cast_add]
  exact congrArg (Nat.cast : ℕ → ZMod p) (show n % 2 ^ 16 + (n / 2 ^ 16 % 2 ^ 8) * 65536 = n % 2 ^ 24 by omega)

private theorem clock_high (n : ℕ) (bound : n < 2 ^ 48) :
    ((n / 2 ^ 24 % 2 ^ 8 : ℕ) : ZMod p) + (n / 2 ^ 32 % 2 ^ 16 : ℕ) * 256 = (n / 2 ^ 24 : ℕ) := by
  change _ + _ * ((256 : ℕ) : ZMod p) = _
  rw [← Nat.cast_mul, ← Nat.cast_add]
  exact congrArg (Nat.cast : ℕ → ZMod p) (show n / 2 ^ 24 % 2 ^ 8 + (n / 2 ^ 32 % 2 ^ 16) * 256 = n / 2 ^ 24 by omega)

variable (source target : ExecutionSnapshot) (statement : CommitmentStatement)

theorem ofExecution_source (bound : source.clock < 2 ^ 48) :
    SP1PublicIO.SourceFor source (ofExecution (p := p) source target statement) :=
  ⟨clock_high _ bound, clock_low _, rfl, rfl, rfl⟩

theorem ofExecution_target (bound : target.clock < 2 ^ 48) :
    SailBoundary.TargetFor target (ofExecution (p := p) source target statement) :=
  ⟨⟨clock_high _ bound, clock_low _⟩, rfl, rfl, rfl⟩

theorem ofExecution_commitment (valid : statement.WellFormed p) :
    CommitmentBoundary.Spec statement (ofExecution (p := p) source target statement) :=
  ⟨valid, rfl, rfl, rfl, rfl⟩

theorem ofExecution_limbBounds : (ofExecution (p := p) source target statement).LimbBounds := by
  have limb {n bits : ℕ} (h : n < 2 ^ bits) : (n : ZMod p).val < 2 ^ bits := by
    rw [ZMod.val_natCast]
    exact (Nat.mod_le _ _).trans_lt h
  unfold LimbBounds
  repeat' apply And.intro
  all_goals apply limb
  all_goals first | exact BitVec.isLt _ | exact Nat.mod_lt _ (by decide)

end SP1Clean.SP1StateBoundary
