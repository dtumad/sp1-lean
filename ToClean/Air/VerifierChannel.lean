module

public import ToClean.Air.EnsembleBuild
public import ToClean.Circuit.VerifierAssertions
public import ToClean.Circuit.VerifierInteractions

/-! # Fresh verifier channels

Clean has no channel allocator for verifier extensions. This addition derives a name from both
the complete registered channel inventory, then proves the original ledger
is empty on that channel. It belongs beside Clean's ensemble verifier composition API; remove it
when upstream provides automatic channel separation.
-/

@[expose] public section

namespace Air.Flat.VerifierChannel
open Circuit
variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- The ensemble registry covers every verifier and component interaction. -/
def channelNames (ens : Ensemble F PublicIO) : List String :=
  ens.channels.map (·.name)

private theorem length_le_nameBound {names : List String} {name : String} (member : name ∈ names) :
    name.length ≤ names.foldr (fun name bound => max name.length bound) 0 := by
  induction names with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left ..
    · exact le_trans (ih member) (Nat.le_max_right ..)

/-- A name longer than every registered or actually used name, preserving the check's stem. -/
def channelName (stem : String) (ens : Ensemble F PublicIO) : String :=
  stem ++ String.ofList
    (List.replicate ((channelNames ens).foldr (fun name bound => max name.length bound) 0 + 1) '_')

/-- The dedicated channel enforcing zero values, fresh for the entire original ensemble. -/
def channel (stem : String) (ens : Ensemble F PublicIO) : RawChannel F :=
  (Verifier.zeroChannel (F := F) (channelName stem ens)).toRaw

private theorem channel_ne (stem : String) (ens : Ensemble F PublicIO) (other : RawChannel F)
    (member : other.name ∈ channelNames ens) : channel stem ens ≠ other := by
  intro same
  have bound := length_le_nameBound member
  have lengths := congrArg (fun channel : RawChannel F => channel.name.length) same
  simp only [channel, Verifier.zeroChannel, Channel.toRaw, channelName,
    String.length_append, String.length_ofList, List.length_replicate] at lengths
  omega

/-- The allocated name is absent even before comparing dependent channel predicates. -/
theorem name_not_mem (stem : String) (ens : Ensemble F PublicIO) :
    (channel stem ens).name ∉ ens.channels.map (·.name) := by
  intro member
  have bound := length_le_nameBound (names := channelNames ens)
    member
  simp only [channel, Verifier.zeroChannel, Channel.toRaw, channelName,
    String.length_append, String.length_ofList, List.length_replicate] at bound
  omega

/-- Static evidence that the check channel has no pre-existing producer or consumer. -/
structure Fresh (stem : String) (ens : Ensemble F PublicIO) : Prop where
  /-- The channel is newly registered by installation. -/
  unregistered : channel stem ens ∉ ens.channels
  /-- The original verifier emits no occurrence on the new channel. -/
  verifier : ∀ env, ens.verifierOperations.interactionValuesWith (channel stem ens) env = []
  /-- No physical component emits an occurrence on the new channel. -/
  tables : ∀ component ∈ ens.tables, ∀ env,
    component.operations.interactionValuesWith (channel stem ens) env = []

theorem fresh (stem : String) (ens : Ensemble F PublicIO) : Fresh stem ens := by
  classical
  have absent (ops : Operations F)
      (included : ∀ interaction ∈ ops.interactions, interaction.channel.name ∈ channelNames ens)
      (env : Environment F) : ops.interactionValuesWith (channel stem ens) env = [] := by
    have empty : ops.interactionsWith (channel stem ens) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro interaction member
      simpa using (channel_ne stem ens interaction.channel (included interaction member)).symm
    simp only [Operations.interactionValuesWith, empty, List.map_nil]
  refine ⟨?_, ?_, ?_⟩
  · intro member
    exact channel_ne stem ens (channel stem ens)
      (List.mem_map.mpr ⟨_, member, rfl⟩) rfl
  · apply absent
    intro interaction member
    apply List.mem_map.mpr
    refine ⟨interaction.channel, ens.verifier_channels ?_, rfl⟩
    rw [Verifier.Program.mem_channels_iff, Operations.channels]
    exact List.mem_map.mpr ⟨interaction, member, rfl⟩
  · intro component member
    apply absent
    intro interaction occurrence
    apply List.mem_map.mpr
    refine ⟨interaction.channel, ens.tables_channels component member ?_, rfl⟩
    rw [Component.interactions_eq] at occurrence
    exact component.circuit.channels_subset component.rowInputVar component.rowOffset
      (List.mem_map.mpr ⟨interaction, occurrence, rfl⟩)

/-- Static separation makes the original witness's entire check-channel ledger empty. -/
theorem Fresh.empty_ledger (stem : String) {ens : Ensemble F PublicIO} (fresh : Fresh stem ens)
    (witness : EnsembleWitness ens) : witness.interactionsWith (channel stem ens) = [] := by
  change ens.verifierOperations.interactionValuesWith (channel stem ens)
    (Environment.fromInput witness.publicInput witness.data) ++
      witness.tables.flatMap (fun table => table.interactionsWith (channel stem ens)) = []
  rw [fresh.verifier, List.nil_append]
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  apply List.flatMap_eq_nil_iff.mpr
  intro row _
  exact fresh.tables table.component (EnsembleWitness.component_mem_tables_of_mem member) _

end Air.Flat.VerifierChannel
