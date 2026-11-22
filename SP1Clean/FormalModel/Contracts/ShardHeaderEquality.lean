import SP1Clean.FormalModel.Contracts.ShardHeader

/-! # Uniqueness of the range-checked public shard header -/

namespace SP1Clean.SP1StateBoundary
open Semantics
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

private theorem unpack {lo hi lo' hi' : ZMod p} (radix upper : ℕ)
    (width : upper * radix = 2 ^ 24) (a : lo.val < radix) (b : hi.val < upper)
    (c : lo'.val < radix) (d : hi'.val < upper)
    (same : lo + hi * radix = lo' + hi' * radix) : lo = lo' ∧ hi = hi' := by
  have small (x y : ZMod p) (low : x.val < radix) (high : y.val < upper) :
      x.val + y.val * radix < p := by
    calc
      _ < (y.val + 1) * radix := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]; omega
      _ ≤ upper * radix := Nat.mul_le_mul_right _ high
      _ < p := width ▸ Fact.out (p := 2 ^ 24 < p)
  have embed (x y : ZMod p) : ((x.val + y.val * radix : ℕ) : ZMod p) = x + y * radix := by
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [← embed, ← embed lo' hi'] at same
  have natural := congrArg ZMod.val same
  rw [ZMod.val_natCast_of_lt (small _ _ a b), ZMod.val_natCast_of_lt (small _ _ c d)] at natural
  have low := congrArg (fun n => n % radix) natural
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a, Nat.mod_eq_of_lt c] at low
  rw [low, Nat.add_right_inj] at natural
  exact ⟨ZMod.val_injective p low, ZMod.val_injective p (Nat.eq_of_mul_eq_mul_right (by omega) natural)⟩

/-- The two recombined clocks, three PC limbs at each end, and the remaining named fields
determine the literal header once all raw clock limbs have their physical range bounds. -/
theorem eq_of_bindings {source target : ExecutionSnapshot} {statement : CommitmentStatement}
    {input : SP1PublicIO (ZMod p)}
    (limbs : input.LimbBounds) (sourceBound : source.clock < 2 ^ 48)
    (targetBound : target.clock < 2 ^ 48) (incoming : input.SourceFor source)
    (outgoing : SailBoundary.TargetFor target input) (flag : input.is_execution_shard = SailBoundary.executionShardFlag source target)
    (commit : CommitmentBoundary.Spec statement input)
    (exitValue : input.exit_code = (((haltCode source target).getD 0).toNat : ZMod p)) :
    input = ofExecution source target statement := by
  obtain ⟨a, b, c, d, _, _, _, e, f, g, h, _⟩ := limbs
  obtain ⟨a', b', c', d', _, _, _, e', f', g', h', _⟩ := ofExecution_limbBounds (p := p) source target statement
  have src := ofExecution_source (p := p) source target statement sourceBound
  have dst := ofExecution_target (p := p) source target statement targetBound
  obtain ⟨i₀, i₁⟩ := unpack 65536 256 rfl a b a' b' (incoming.2.1.trans src.2.1.symm)
  obtain ⟨i₂, i₃⟩ := unpack 256 65536 rfl c d c' d' (incoming.1.trans src.1.symm)
  obtain ⟨t₀, t₁⟩ := unpack 65536 256 rfl e f e' f' (outgoing.1.2.trans dst.1.2.symm)
  obtain ⟨t₂, t₃⟩ := unpack 256 65536 rfl g h g' h' (outgoing.1.1.trans dst.1.1.symm)
  obtain ⟨_, _, ip₀, ip₁, ip₂⟩ := incoming
  obtain ⟨_, tp₀, tp₁, tp₂⟩ := outgoing
  obtain ⟨_, digest, deferred, committed, deferredFlag⟩ := commit
  cases input
  unfold ofExecution ofEndpoints
  congr 1
end SP1Clean.SP1StateBoundary
