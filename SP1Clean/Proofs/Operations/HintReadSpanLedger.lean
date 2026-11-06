import SP1Clean.Proofs.Operations.HintReadSpan
import ToClean.Circuit.InteractionRecovery
import ToClean.Air.ChannelClosure

/-! # The checked span's exact external assumptions

Only the existing Byte range provider is needed by the address additions. The span has no
Memory, hint, or host-call traffic of its own; a consumer must use its endpoints to build and
verify complete word coverage on those ledgers.
-/

namespace SP1Clean.HintReadSpan

open Circuit Air.Flat Channels
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem main_other_interactions (target : RawChannel (ZMod p)) (notByte : target ≠ byteChannel.toRaw)
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith target = [] := by
  apply InteractionRecovery.interactionsWith_main_eq_nil circuit.base target input offset
  simp [circuit, circuit_norm, notByte]

/-- The bundled circuit's contract follows from its row constraints and Byte guarantees. -/
theorem row_spec_of_byte (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((circuit.main input).operations offset).ConstraintsHold env)
    (byte : ((circuit.main input).operations offset).ChannelGuarantees byteChannel.toRaw env) :
    circuit.Spec (eval env input) (eval env ((circuit.main input).output offset)) env.data := by
  apply (circuit.original_full_soundness offset env input (by trivial) constraints ?_).1
  rw [Operations.guarantees_iff _ _ _ (circuit.in_channels_or_guarantees_full input offset env)]
  intro selected member
  have same : selected = byteChannel.toRaw := by simpa [circuit, circuit_norm] using member
  simpa only [same] using byte

end SP1Clean.HintReadSpan
