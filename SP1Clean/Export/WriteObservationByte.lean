import SP1Clean.Export.WriteObservationSources
import SP1Clean.Soundness.HostObservedConsumer

/-! # Byte funding across the complete native WRITE observation installation

The old providers continue to prove Byte requirements after source decoration. Every new
consumer proves its outgoing requirements from constrained rows. Only the complete physical
Byte ledger is balanced, and the resulting guarantees reach each original memory source.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics WriteProbe WriteSourceRegistry Channels Soundness

private abbrev F := ZMod SP1Prime

variable (image : ProgramImage) (source target : ExecutionSnapshot) (final : HostHintQueue.State F)

private theorem byte_prior {c : Component F} (member : c ∈ (base image source target final).tables)
    (env : Environment F) (checked : c.operations.ConstraintsHold env) : c.operations.ChannelRequirements byteChannel.toRaw env := by
  exact HostObserved.component_byte_requirements (image := image) (source := source) (target := target) (final := final) c member env checked

private theorem verifier_of_eq {a b : Ensemble F SP1PublicIO} (equal : a.verifier = b.verifier)
    {data : ProverData F} (prior : b.VerifierChannelRequirements data byteChannel.toRaw) :
    a.VerifierChannelRequirements data byteChannel.toRaw := by
  simpa only [Ensemble.VerifierChannelRequirements, Ensemble.verifierOperations, equal] using prior

private theorem verifier_byte (data : ProverData F) :
    (preprocessing image source target final).VerifierChannelRequirements data byteChannel.toRaw := by
  have old : (base image source target final).VerifierChannelRequirements data byteChannel.toRaw := by
    unfold base
    exact HostObserved.verifier_byte_requirements (image := image) (source := source) (target := target) (final := final) data
  exact verifier_of_eq ((appended image source target final).verifier.trans (verifier_eq image source target final)) old

private theorem suffix_byte (c : Component F) (member : c ∈ tables source target)
    (env : Environment F) (checked : c.operations.ConstraintsHold env) : c.operations.ChannelRequirements byteChannel.toRaw env := by
  apply Operations.requirements_of_not_mem _ _ _ (c.inChannelsOrRequirements_of_constraints env checked) _
  have absent : (byteChannel (p := SP1Prime)).name ∉ (tables source target).flatMap
      (fun t => t.circuit.channelsWithRequirements.map RawChannel.name) := of_decide_eq_true rfl
  exact fun used => absent (List.mem_flatMap.mpr ⟨c, member, List.mem_map_of_mem used⟩)

attribute [local irreducible] base withSources preprocessing

variable {image source target final}

/-- Whole-ensemble Byte validity from raw signed balance and constraints on the actual rows. -/
theorem byte_guarantees (w : EnsembleWitness (preprocessing image source target final))
    (checked : w.Constraints) (funded : w.BalancedChannel byteChannel.toRaw) :
    (preprocessing image source target final).VerifierChannelGuarantees w.data byteChannel.toRaw ∧
      ∀ t ∈ w.tables, t.ChannelGuarantees byteChannel.toRaw := by
  apply w.channelGuarantees_of_component_requirements _ checked funded (verifier_byte image source target final)
  intro c member
  rw [(appended image source target final).tables] at member
  rcases List.mem_append.mp member with old | added
  · exact (sameRows image source target final).channelRequirements byteChannel.toRaw
      (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))
      (fun _ h => byte_prior image source target final h) c old
  · exact suffix_byte source target c added

private theorem byte_data {i : Interaction F} {a b : ProverData F} (onByte : i.channel = byteChannel.toRaw)
    (valid : i.Guarantees a) : i.Guarantees b := by
  rcases i with ⟨ch, dir, mult, msg, size⟩
  change ch = _ at onByte
  subst ch
  exact valid

/-- Removing the WRITE tables can remove Byte consumers. Every retained original record still
inherits the actual provider's guarantee at the original supervisor's canonical data. -/
theorem supervisor_byte (w : EnsembleWitness (preprocessing image source target final))
    (checked : w.Constraints) (funded : w.BalancedChannel byteChannel.toRaw) :
    ∀ t ∈ (supervisor w).tables, t.ChannelGuarantees byteChannel.toRaw := by
  obtain ⟨verifier, all⟩ := byte_guarantees w checked funded
  let install := appended image source target final
  have prior := project_ledger (install.project w) byteChannel.toRaw (fun eq =>
    Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))
  intro t included
  rw [t.channelGuarantees_iff_forall]
  intro i emitted
  have inOld : i ∈ (supervisor w).interactionsWith byteChannel.toRaw :=
    EnsembleWitness.mem_interactionsWith.mpr (Or.inr ⟨t, included, emitted⟩)
  have full : i ∈ w.interactionsWith byteChannel.toRaw := by
    rw [install.ledger]
    exact List.mem_append_left _ (prior ▸ inOld)
  apply byte_data (EnsembleWitness.channel_eq_of_mem_interactionsWith full) (a := w.data)
  rcases EnsembleWitness.mem_interactionsWith.mp full with seen | ⟨row, member, seen⟩
  · exact EnsembleWitness.verifierChannelGuarantees_iff_forall.mp verifier i seen
  · have data : row.data = w.data := w.same_data row member
    rw [← data]
    exact (row.channelGuarantees_iff_forall _).mp (all row member) i seen

/-- Both original HINT_READ word tables, at positions 84 and 85, have authentic Byte reads. -/
theorem hint_word_bytes (w : EnsembleWitness (preprocessing image source target final))
    (checked : w.Constraints) (funded : w.BalancedChannel byteChannel.toRaw) (last : Bool) :
    (raw (supervisor w) (.host (.word last))).ChannelGuarantees byteChannel.toRaw :=
  supervisor_byte w checked funded _ ((originalSlot image source target final _).table_mem (supervisor w))

/-- The public cursor and endpoint verifiers preserve balance of the installed Byte ledger. -/
theorem observed_byte_balance (w : EnsembleWitness (assembly image source target final))
    (fit : w.InteractionsFit .logUp) (balanced : w.Balanced .logUp) : (observed w).BalancedChannel byteChannel.toRaw := by
  let seen := preprocessing image source target final
  let span : TableSlot seen.tables WriteBuffer.spanComponent := slot image source target final 3
  have registered : byteChannel.toRaw ∈ seen.channels := seen.tables_channels _ (span.component_eq ▸ List.getElem_mem span.index.isLt)
    (show byteChannel.toRaw ∈ WriteBuffer.spanComponent.circuit.channels from List.mem_cons_self)
  exact observed_balance w fit balanced _ registered (of_decide_eq_true rfl)

/-- At the installed public checker, raw LogUp acceptance authenticates every byte of
both original hint-word tables using the complete native Byte ledger. -/
theorem assembled_hint_word_bytes (w : EnsembleWitness (assembly image source target final))
    (checked : w.Constraints) (fit : w.InteractionsFit .logUp) (balanced : w.Balanced .logUp) (last : Bool) :
    (raw (supervisor (observed w)) (.host (.word last))).ChannelGuarantees byteChannel.toRaw :=
  hint_word_bytes (observed w) ((observed_constraints w).mp checked) (observed_byte_balance w fit balanced) last

end SP1Clean.Export.WriteObservationAssembly
