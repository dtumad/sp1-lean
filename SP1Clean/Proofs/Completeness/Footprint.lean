import SP1Clean.Proofs.Completeness.Assembly
import ToClean.Air.Footprint

/-!
# Exact native interaction footprint

Clean's balance predicate includes one non-algebraic capacity condition: each channel's complete
interaction list must be shorter than the field characteristic.  This module gives that condition a
small, explicit carrier.  It is deliberately separate from semantic trace readiness and from
provider multiplicity: aggregate provider counts may wrap as field elements without harming field
balance, while the number of interaction *occurrences* may not reach the characteristic.

`NativeTraceFootprint.ofTrace` retains the five named legacy projections. The active ordinary
compiler now consumes `EnsembleWitness.ChannelCapacity` over every registered channel; its
compatibility equivalence lives next to that constructor in `NativeTraceCompiler.lean` and uses
the ordinary trace's two silent host channels. It is not an equivalence for mixed host traces.
-/

namespace SP1Clean.Soundness

open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel exitChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Legacy five-channel projection. New consumers use `EnsembleWitness.ChannelCapacity` over
every registered channel; this record remains only for source compatibility. -/
structure NativeTraceFootprint where
  state : ℕ
  byte : ℕ
  program : ℕ
  memory : ℕ
  exit : ℕ
deriving DecidableEq, Repr

namespace NativeTraceFootprint

/-- Clean's interaction-count capacity condition, stated without any multiplicity bound. -/
def Fits (footprint : NativeTraceFootprint) (characteristic : ℕ) : Prop :=
  footprint.state < characteristic ∧
    footprint.byte < characteristic ∧
    footprint.program < characteristic ∧
    footprint.memory < characteristic ∧
    footprint.exit < characteristic

/-- Measure the five legacy channels of the actual generated native witness. -/
noncomputable def ofTrace (trace : SupportedCoreTraceWitness p) : NativeTraceFootprint where
  state := (trace.witness.allTablesWitness.interactionsWith stateChannel.toRaw).length
  byte := (trace.witness.allTablesWitness.interactionsWith byteChannel.toRaw).length
  program := (trace.witness.allTablesWitness.interactionsWith programChannel.toRaw).length
  memory := (trace.witness.allTablesWitness.interactionsWith memoryChannel.toRaw).length
  exit := (trace.witness.allTablesWitness.interactionsWith exitChannel.toRaw).length

/-- The generic all-channel capacity implies the retained five-channel compatibility view. -/
theorem fits_of_channelCapacity (trace : SupportedCoreTraceWitness p)
    (capacity : trace.witness.ChannelCapacity p) : (ofTrace trace).Fits p := by
  have bounds := (Air.Flat.EnsembleWitness.channelCapacity_iff _ _).mp capacity
  exact ⟨bounds stateChannel.toRaw (by simp [sp1Ensemble_channels]),
    bounds byteChannel.toRaw (by simp [sp1Ensemble_channels]),
    bounds programChannel.toRaw (by simp [sp1Ensemble_channels]),
    bounds memoryChannel.toRaw (by simp [sp1Ensemble_channels]),
    bounds exitChannel.toRaw (by simp [sp1Ensemble_channels])⟩

theorem fits_of_balancedChannels (trace : SupportedCoreTraceWitness p)
    (balanced : trace.witness.BalancedChannels) : (ofTrace trace).Fits p := by
  apply fits_of_channelCapacity
  simpa only [ZMod.ringChar_zmod_n] using trace.witness.channelCapacity_of_balanced balanced
    (by simpa only [ZMod.ringChar_zmod_n] using (Fact.out : p.Prime).pos)

end NativeTraceFootprint

end SP1Clean.Soundness
