import SP1Clean.Export.WriteAllocationOrder

/-! # Authentic incoming persistent allocation frontier

The original verifier checks the 48-bit incoming node count. Its singleton assertion
channel remains funded by raw acceptance of the complete native installation.
-/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness HostHintQueue WriteSourceRegistry
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : State F}

/-- The complete installation preserves the supervisor assertion ledger on each original single-field channel. -/
theorem prior_assertion_balance (w : EnsembleWitness (assembly image source target final))
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (ch : RawChannel F)
    (registered : ch ∈ (base image source target final).channels) (width : ch.arity = 1) :
    (supervisor (observed w)).BalancedChannel ch := by
  let seen := observed w
  let install := appended image source target final
  have prior : ch ∈ (withSources image source target final).channels := List.mem_cons_of_mem _ registered
  have used : ch ∈ (preprocessing image source target final).channels := List.mem_append_right _ prior
  have distinct {other : RawChannel F} (m : other ∈ (preprocessing image source target final).channels)
      (arity : other.arity ≠ 1) : ch.name ≠ other.name := by
    intro eq
    have same := List.inj_on_of_nodup_map (preprocessing image source target final).unique_channel_names used m eq
    exact arity (same ▸ width)
  have reg (i : Fin channels.length) := protocol_installed image source target final _ (List.getElem_mem i.isLt)
  have quiet : ch.name ∉ [(WriteEffects.cursorChannel (p := SP1Prime)).name,(WriteEffects.closeChannel (p := SP1Prime)).name] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨distinct (reg ⟨11,by decide⟩) (by decide),distinct (reg ⟨15,by decide⟩) (by decide)⟩
  have paid := observed_balance w fit raw ch used quiet
  have absent : 1 ∉ (tables source target).flatMap (fun c => c.circuit.channels.map RawChannel.arity) := of_decide_eq_true rfl
  have removed := install.ledger_of_silent seen ch (fun c member found =>
    absent (width ▸ List.mem_flatMap.mpr ⟨c,member,List.mem_map_of_mem (f := RawChannel.arity) found⟩))
  have original := project_ledger (install.project seen) ch (fun eq => by
    have impossible := (congrArg RawChannel.arity eq).symm.trans width
    exact (by decide : (WriteProbe.readbackChannel (p := SP1Prime)).toRaw.arity ≠ 1) impossible)
  change BalancedInteractions (seen.interactionsWith ch) at paid
  rw [removed,← original] at paid
  exact paid

/-- The incoming frontier equals the genuine initial persistent store size. The original
verifier's length check remains mandatory even if an oversized source inventory is empty. -/
theorem native_initial_frontier (w : EnsembleWitness (native image source target))
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    source.host.io.hints.length < 2^48 ∧
    Address.toNat (SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) source.host.io.hints).allocated =
      (HintQueue.ofList source.host.io.hints).1.size := by
  let endQueue := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) target.host.io.hints
  let orig : EnsembleWitness (HostObserved.ensemble image source target endQueue) := supervisor (observed w)
  let memory := HostObserved.baseWitness orig
  let boundary := HostFinalMemory.baseWitness memory
  let ch := HostHintQueueBoundary.assertionChannel boundary
  have arity : ch.arity = 1 := rfl
  have reg := HostHintQueueBoundary.assertionChannel_registered boundary
  have fmReg : ch ∈ (HostFinalMemory.Installed image source target endQueue).channels := List.mem_append_left _ reg
  have top : ch ∈ (base image source target endQueue).channels := List.mem_append_left _ fmReg
  have ne {other : RawChannel F} (width : other.arity ≠ 1) : ch ≠ other := fun same => width (same ▸ arity)
  have fm := HostFinalMemory.baseWitness_silent_interactions memory ch reg (ne (by decide)) (ne (by decide)) (ne (by decide))
  have obs := HostObserved.baseWitness_interactions orig ch fmReg (ne (by decide)) (ne (by decide))
  have paid := prior_assertion_balance w fit raw ch top arity
  change BalancedInteractions (orig.interactionsWith ch) at paid
  rw [← obs,← fm] at paid
  have checks := HostHintQueueBoundary.checks_of_assertionChannel boundary paid
  unfold ClosedVerifier.Checks ClosedVerifier.operations at checks
  rw [HostBoundary.closed_main] at checks
  have bound := SP1Clean.HostBoundary.source_bound _ _ _ _ _ _ _ _ checks
  exact ⟨bound,(SP1Clean.HostHintQueueBoundary.initial_binds (p := SP1Prime) source.host.io.hints bound).2.2.1⟩

end SP1Clean.Export.WriteObservationAssembly
