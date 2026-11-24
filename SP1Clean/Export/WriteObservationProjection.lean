import SP1Clean.Export.WriteObservationAssembly

/-! # Projecting the public WRITE verifiers onto their installed physical tables

The public cursor endpoint emits on two private channels. All other registered channels
keep exactly the same ordered verifier and table traffic after both public projections.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics

private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
attribute [local irreducible] preprocessing

/-- Retain all physical tables and their canonical data beneath the public verifiers. -/
def observed (w : EnsembleWitness (assembly image source target final)) : EnsembleWitness (preprocessing image source target final) :=
  w.withEnsemble _ (by unfold assembly withCursors; rfl)

theorem observed_constraints (w : EnsembleWitness (assembly image source target final)) :
    w.Constraints ↔ (observed w).Constraints := Iff.rfl

/-- An old registered channel other than the two cursor endpoint channels has exactly its
original signed occurrences after erasing the two public verifiers. -/
theorem observed_ledger (w : EnsembleWitness (assembly image source target final)) (ch : RawChannel F)
    (registered : ch ∈ (preprocessing image source target final).channels)
    (silent : ch.name ∉ [(WriteEffects.cursorChannel (p := SP1Prime)).name, (WriteEffects.closeChannel (p := SP1Prime)).name]) :
    (observed w).interactionsWith ch = w.interactionsWith ch := by
  have cursor : (WriteEffects.cursorChannel (p := SP1Prime)).toRaw ≠ ch :=
    fun eq => silent (congrArg RawChannel.name eq ▸ List.mem_cons_self)
  have close : (WriteEffects.closeChannel (p := SP1Prime)).toRaw ≠ ch :=
    fun eq => silent (congrArg RawChannel.name eq ▸ List.mem_cons_of_mem _ List.mem_cons_self)
  let checker := WriteEffects.checker (p := SP1Prime) source.host target.host
  let cursors := withCursors image source target final
  let prev := checker.project (ens := cursors) w
  have installed : ch ∈ cursors.channels := by unfold cursors withCursors; exact registered
  have checkerLedger : prev.interactionsWith ch = w.interactionsWith ch :=
    checker.project_interactions _ ch (fun eq => checker.channel_not_mem cursors (eq ▸ installed))
  apply Eq.trans _ checkerLedger
  change (preprocessing image source target final).verifierOperations.interactionValuesWith ch w.data.publicEnvironment ++
    w.toTables.interactionsWith ch = (withCursors image source target final).verifierOperations.interactionValuesWith ch w.data.publicEnvironment ++ _
  rw [withCursors_ledger]
  simp [Channel.pushedValue, Channel.pulledValue, cursor, close, prev]
  rfl

/-- Per-channel balance transports across both public projections precisely on silent channels. -/
theorem observed_balance (w : EnsembleWitness (assembly image source target final)) (fit : w.InteractionsFit .logUp)
    (balanced : w.Balanced .logUp) (ch : RawChannel F) (registered : ch ∈ (preprocessing image source target final).channels)
    (silent : ch.name ∉ [(WriteEffects.cursorChannel (p := SP1Prime)).name, (WriteEffects.closeChannel (p := SP1Prime)).name]) :
    (observed w).BalancedChannel ch := by
  rw [EnsembleWitness.BalancedChannel, observed_ledger w ch registered silent]
  apply EnsembleWitness.balancedChannels_of_balanced fit balanced ch
  unfold assembly withCursors
  exact List.mem_append_left _ registered

end SP1Clean.Export.WriteObservationAssembly
