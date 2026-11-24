import SP1Clean.Export.WriteObservationSources
import SP1Clean.Soundness.WriteProbeReadAuthentication
import SP1Clean.Soundness.WriteProbeConsumers
import ToClean.Air.AppendedAuthentication

/-! # Authentication of the physically installed x12 and RAM probes -/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics WriteProbe WriteProbe.AccessInventory WriteSourceRegistry

private abbrev F := ZMod SP1Prime

variable (image : ProgramImage) (source target : ExecutionSnapshot) (final : HostHintQueue.State F)

/-- The observer receiving counted versions and furnishing host-facing probe receipts. -/
def probeSlot : TableSlot (preprocessing image source target final).tables WriteProbe.component :=
  slot image source target final 1

private theorem channels_installed : (preprocessing image source target final).channels =
    channels ++ (withSources image source target final).channels := rfl

attribute [local irreducible] base withSources preprocessing

private theorem protocol_fresh (ch : RawChannel F) (member : ch ∈ channels) :
    ch ∉ (withSources image source target final).channels := by
  have names := (preprocessing image source target final).unique_channel_names
  rw [channels_installed, List.map_append, List.nodup_append] at names
  intro prior
  exact names.2.2 _ (List.mem_map_of_mem member) _ (List.mem_map_of_mem prior) rfl

private theorem protocol_installed (ch : RawChannel F) (member : ch ∈ channels) :
    ch ∈ (preprocessing image source target final).channels := by
  rw [channels_installed]
  exact List.mem_append_left _ member

private theorem silent_of_names {cs : List (Component F)} {ch : RawChannel F}
    (silent : ch.name ∉ cs.flatMap (fun c => c.circuit.channels.map RawChannel.name))
    {c : Component F} (member : c ∈ cs) : ch ∉ c.circuit.channels :=
  fun used => silent (List.mem_flatMap.mpr ⟨c, member, List.mem_map_of_mem used⟩)

private theorem version_consumers (property : Version F → Prop) (c : Component F) (member : c ∈ tables source.host target.host)
    (other : c ≠ ReadbackSupply.component) : c.Authenticates versionChannel property := by
  let rest := (tables source.host target.host).drop 2
  change c ∈ ReadbackSupply.component :: WriteProbe.component :: rest at member
  rcases List.mem_cons.mp member with installed | restEntries
  · exact (other installed).elim
  rcases List.mem_cons.mp restEntries with rfl | inTail
  · exact no_version_push property
  · apply Component.Authenticates.of_silent
    apply silent_of_names (cs := rest) _ inTail
    exact of_decide_eq_true rfl

private theorem read_consumers (property : Read F → Prop) (c : Component F) (member : c ∈ tables source.host target.host)
    (other : c ≠ WriteProbe.component) : c.Authenticates readChannel property := by
  let rest := (tables source.host target.host).drop 5
  change c ∈ ReadbackSupply.component :: WriteProbe.component :: WritePacket.component ::
    WriteBuffer.spanComponent :: WriteBuffer.wordComponent :: rest at member
  simp only [List.mem_cons] at member
  rcases member with rfl | same | rfl | rfl | rfl | inTail
  · apply Component.Authenticates.of_silent
    exact silent_of_names (cs := [ReadbackSupply.component]) (of_decide_eq_true rfl) List.mem_cons_self
  · exact (other same).elim
  · exact WritePacket.no_read_push property
  · apply Component.Authenticates.of_silent
    exact silent_of_names (cs := [WriteBuffer.spanComponent]) (of_decide_eq_true rfl) List.mem_cons_self
  · exact WriteBuffer.no_read_push property
  · apply Component.Authenticates.of_silent
    apply silent_of_names (cs := rest) _ inTail
    exact of_decide_eq_true rfl

variable {image source target final}

/-- Every physical probe receipt exposes its authentic source word and the two original
clock endpoints bounding this exact incoming clock. -/
theorem probe_reads (w : EnsembleWitness (preprocessing image source target final))
    (checked : w.Constraints) (balanced : w.BalancedChannels) :
    ((probeSlot image source target final).table w).Authenticates readChannel
      (ReadMeaning (rawSource ((appended image source target final).project w))) := by
  let install := appended image source target final
  let probes := probeSlot image source target final
  let property := Meaning (rawSource (install.project w))
  have versions : (versionChannel (p := SP1Prime)).toRaw ∈ channels := List.mem_cons_self
  have readback : (readbackChannel (p := SP1Prime)).toRaw ∈ (preprocessing image source target final).channels := by
    rw [channels_installed, channels_eq]
    exact List.mem_append_right _ List.mem_cons_self
  apply authenticates_reads _ _ (probes.table_component w) (probes.table_constraints w checked)
  intro version emitted
  exact install.authenticated_pull w versionChannel (protocol_fresh image source target final _ versions)
    (supplySlot image source target final) property (authenticates_versions w checked (balanced _ readback))
    (version_consumers source target property) checked (balanced _ (protocol_installed image source target final _ versions))
    version (probes.table_interactions_subset w _ emitted)

/-- Every actual unit read demand in the physical witness, including both the packet's
x12 length and each buffer-word request, has the original word at its requested clock. -/
theorem read_origin (w : EnsembleWitness (preprocessing image source target final))
    (checked : w.Constraints) (balanced : w.BalancedChannels) (read : Read F)
    (requested : readChannel.pulledValue read ∈ w.interactionsWith readChannel.toRaw) :
    ReadMeaning (rawSource ((appended image source target final).project w)) read := by
  let property := ReadMeaning (rawSource ((appended image source target final).project w))
  have reads : (readChannel (p := SP1Prime)).toRaw ∈ channels := List.mem_cons_of_mem _ List.mem_cons_self
  exact (appended image source target final).authenticated_pull w readChannel
    (protocol_fresh image source target final _ reads) (probeSlot image source target final) property
    (probe_reads w checked balanced) (read_consumers source target property) checked
    (balanced _ (protocol_installed image source target final _ reads)) read requested

/-- Raw LogUp acceptance of the host stream verifier authenticates each real probe push. -/
theorem assembled_probe_reads (w : EnsembleWitness (assembly image source target final))
    (checked : w.Constraints) (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    let observed := (WriteEffects.checker source.host target.host).project
      (ens := preprocessing image source target final) w
    ((probeSlot image source target final).table observed).Authenticates readChannel
      (ReadMeaning (rawSource ((appended image source target final).project observed))) := by
  let checker := WriteEffects.checker (p := SP1Prime) source.host target.host
  let seen := preprocessing image source target final
  exact probe_reads (checker.project (ens := seen) w) ((checker.project_constraints w).mp checked)
    ((checker.project_balanced_iff (ens := seen) w).mp (EnsembleWitness.balancedChannels_of_balanced fit raw)).1

/-- At the public stream checker, a requested x12 or RAM receipt identifies its original
physical source and both inclusive clocks under raw LogUp acceptance. -/
theorem assembled_read_origin (w : EnsembleWitness (assembly image source target final))
    (checked : w.Constraints) (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (read : Read F)
    (requested : readChannel.pulledValue read ∈ w.interactionsWith readChannel.toRaw) :
    let observed := (WriteEffects.checker source.host target.host).project
      (ens := preprocessing image source target final) w
    ReadMeaning (rawSource ((appended image source target final).project observed)) read := by
  let checker := WriteEffects.checker (p := SP1Prime) source.host target.host
  let seen := preprocessing image source target final
  have reads := protocol_installed image source target final _ (show (readChannel (p := SP1Prime)).toRaw ∈ channels
    from List.mem_cons_of_mem _ List.mem_cons_self)
  have ledger := checker.project_interactions (ens := seen) w readChannel.toRaw
    (fun same => checker.channel_not_mem seen (same ▸ reads))
  exact read_origin (checker.project (ens := seen) w) ((checker.project_constraints w).mp checked)
    ((checker.project_balanced_iff (ens := seen) w).mp (EnsembleWitness.balancedChannels_of_balanced fit raw)).1 read (ledger.symm ▸ requested)

end SP1Clean.Export.WriteObservationAssembly
