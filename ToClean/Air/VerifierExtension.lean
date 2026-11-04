module

public import ToClean.Air.VerifierChannel
public import ToClean.Circuit.VerifierInteractions
public import Clean.Circuit.Foundations
public import ToClean.Circuit.InteractionRecovery

/-! # Exactly-once closed circuits in an ensemble verifier

Clean's public verifier can run a closed circuit's certified interactions and enforce its raw
assertions through a fresh zero-check channel. This adapter reuses the circuit's semantic proof
and Clean's verifier operations. The physical table inventory and its canonical prover data stay
unchanged. The source boundary is represented by its literal operation ledger at explicit data.

Zero witness length alone does not establish independence from ambient cells. The adapter also
requires the circuit's static transport laws, absent lookups, and Clean's unconditional admission
proof for each verifier interaction. These are construction obligations, not execution premises.
Move this adapter upstream when Clean supplies equivalent circuit-to-verifier composition.
-/

@[expose] public section

namespace Air.Flat
open Circuit

variable {F : Type} [FiniteField F]

/-- A proved closed boundary admitted to Clean's public verifier. -/
structure ClosedVerifier (F : Type) [FiniteField F] where
  /-- Stable stem used when allocating this boundary's fresh assertion channel. -/
  name : String
  circuit : GeneralFormalCircuit F unit unit
  assumptions : ∀ data, circuit.Assumptions () data
  length_zero : circuit.localLength () = 0
  lookups : ((circuit.main ()).operations 0).lookups = []
  public_interactions : ∀ interaction ∈ ((circuit.main ()).operations 0).interactions, ∀ env,
    interaction.direction = .pull → interaction.Requirements env
  constraints : ∀ offset env, ((circuit.main ()).operations offset).ConstraintsHold env ↔
    ((circuit.main ()).operations 0).ConstraintsHold (Environment.fromInput (Input := unit) () env.data)
  interactions : ∀ offset env channel,
    ((circuit.main ()).operations offset).interactionValuesWith channel env =
      ((circuit.main ()).operations 0).interactionValuesWith channel
        (Environment.fromInput (Input := unit) () env.data)

namespace ClosedVerifier
variable (closed : ClosedVerifier F)

/-- Literal raw operations of the proved circuit, at its closed input. -/
abbrev operations : Operations F := (closed.circuit.main ()).operations 0

/-- Acceptance of the source circuit at the ensemble's explicit data. -/
def Checks (data : ProverData F) : Prop :=
  closed.operations.ConstraintsHold (Environment.fromInput (Input := unit) () data)

/-- The added check ledger spends two occurrences for every assertion. -/
def CountBound : Prop :=
  2 * closed.operations.constraints.length < ringChar F

/-- The boundary's literal ledger, without manufacturing a physical table. -/
noncomputable def interactionsWith (data : ProverData F) (channel : RawChannel F) : List (Interaction F) :=
  closed.operations.interactionValuesWith channel (Environment.fromInput (Input := unit) () data)

theorem interactionsWith_nil_of_channel_not_mem (data : ProverData F) (channel : RawChannel F)
    (silent : channel ∉ closed.circuit.channels) : closed.interactionsWith data channel = [] := by
  unfold interactionsWith Operations.interactionValuesWith
  rw [InteractionRecovery.interactionsWith_main_eq_nil closed.circuit.base channel () 0 silent]
  rfl

/-- Every source interaction is admitted through Clean's own verifier operation constructor. -/
def emit : VerifierM F Unit :=
  Verifier.ofInteractions closed.operations.interactions closed.public_interactions

theorem emit_interactions : closed.emit.circuitOperations.interactions = closed.operations.interactions :=
  Verifier.ofInteractions_interactions _ _

theorem emit_values (env : Environment F) (channel : RawChannel F) :
    closed.emit.circuitOperations.interactionValuesWith channel env =
      closed.operations.interactionValuesWith channel (Environment.fromInput (Input := unit) () env.data) := by
  rw [emit, Verifier.ofInteractions_values]
  exact closed.interactions 0 env channel

variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Interaction-only projection, used to choose a channel disjoint from all existing traffic. -/
def interactionProgram : Verifier.Program F PublicIO where
  main _ := closed.emit
  Spec _ _ := True
  soundness _ _ := trivial

/-- The source ledger uses only channels declared by its formal circuit. -/
theorem interactionProgram_channels : (closed.interactionProgram (PublicIO := PublicIO)).channels ⊆ closed.circuit.channels := by
  intro channel member
  rw [Verifier.Program.mem_channels_iff] at member
  change channel ∈ closed.emit.circuitOperations.channels at member
  rw [Operations.channels, closed.emit_interactions] at member
  exact closed.circuit.base.channels_subset () 0 member

/-- Retain the source interactions on the ensemble's existing channel registry. -/
def withInteractions (ens : Ensemble F PublicIO)
    (registered : closed.circuit.channels ⊆ ens.channels) : Ensemble F PublicIO :=
  { ens with
    verifier := ens.verifier.andThen closed.interactionProgram
    verifier_channels := by
      intro channel member
      rcases (Verifier.Program.mem_andThen_channels ens.verifier closed.interactionProgram channel).mp member
        with old | added
      · exact ens.verifier_channels old
      · exact registered (closed.interactionProgram_channels (PublicIO := PublicIO) added) }

/-- Freshness includes every registered boundary interaction. -/
abbrev channelName (ens : Ensemble F PublicIO) : String :=
  VerifierChannel.channelName closed.name ens

/-- Dedicated channel for the boundary's raw assertions. -/
abbrev channel (ens : Ensemble F PublicIO) : RawChannel F :=
  VerifierChannel.channel closed.name ens

/-- Reuse the proved circuit's semantic specification in Clean's public verifier. -/
def program (ens : Ensemble F PublicIO) : Verifier.Program F PublicIO where
  main _ := do
    closed.emit
    Verifier.checkZeros (closed.channelName ens) closed.operations.constraints
  Spec _ data := closed.circuit.Spec () () data
  soundness := by
    intro data guarantees
    let env := data.publicEnvironment
    simp only [Verifier.operations_bind, Verifier.Operations.circuitOperations,
      Verifier.Operations.interactions, List.map_append, Operations.FullGuarantees,
      Operations.interactions_append, List.forall_mem_append] at guarantees
    have original : closed.operations.FullGuarantees env := by
      rw [Operations.FullGuarantees, ← closed.emit_interactions]
      exact guarantees.1
    have checks := (Verifier.checkZeros_guarantees (closed.channelName ens)
      closed.operations.constraints env).mp guarantees.2
    have checked : closed.operations.ConstraintsHold env := by
      refine ⟨checks, ?_⟩
      simp [operations, closed.lookups]
    exact (closed.circuit.original_full_soundness 0 env () (closed.assumptions _)
      checked original).1

/-- Invoke the boundary once, preserving the physical inventory and input metadata. -/
def install (ens : Ensemble F PublicIO)
    (registered : closed.circuit.channels ⊆ ens.channels) : Ensemble F PublicIO :=
  { ens with
    channels := ens.channels ++ [closed.channel ens]
    unique_channel_names := by
      rw [List.map_append, List.nodup_append]
      refine ⟨ens.unique_channel_names, by simp, ?_⟩
      intro a ha b hb same
      have hb' : b = (closed.channel ens).name := by simpa using hb
      apply VerifierChannel.name_not_mem closed.name ens
      rwa [same, hb'] at ha
    verifier := ens.verifier.andThen (closed.program ens)
    tables_channels := fun table member _ used =>
      List.mem_append_left _ (ens.tables_channels table member used)
    verifier_channels := by
      intro channel member
      rcases (Verifier.Program.mem_andThen_channels ens.verifier (closed.program ens) channel).mp member
        with old | added
      · exact List.mem_append_left _ (ens.verifier_channels old)
      · change channel ∈ (closed.emit >>= fun _ =>
          Verifier.checkZeros (closed.channelName ens) closed.operations.constraints).operations.channelsWithGuarantees ++
          (closed.emit >>= fun _ => Verifier.checkZeros (closed.channelName ens)
            closed.operations.constraints).operations.channelsWithRequirements at added
        simp only [Verifier.operations_bind, Verifier.Operations.channelsWithGuarantees,
          Verifier.Operations.channelsWithRequirements, List.filterMap_append, List.mem_append] at added
        rcases added with (source | checks) | (source | checks)
        · exact List.mem_append_left _ (registered (closed.interactionProgram_channels (PublicIO := PublicIO) (List.mem_append.mpr (Or.inl source))))
        · exact List.mem_append_right _ (Verifier.checkZeros_channels _ closed.operations.constraints (List.mem_append.mpr (Or.inl checks)))
        · exact List.mem_append_left _ (registered (closed.interactionProgram_channels (PublicIO := PublicIO) (List.mem_append.mpr (Or.inr source))))
        · exact List.mem_append_right _ (Verifier.checkZeros_channels _ closed.operations.constraints (List.mem_append.mpr (Or.inr checks))) }


/-- The assertion adapter supplies its own requirements; the source interactions retain theirs. -/
theorem program_requirements (ens : Ensemble F PublicIO) (env : Environment F)
    (requirements : closed.operations.FullRequirements env) :
    (closed.program ens).circuitOperations.FullRequirements env := by
  change (closed.emit >>= fun _ =>
    Verifier.checkZeros (closed.channelName ens) closed.operations.constraints).circuitOperations.FullRequirements env
  simp only [VerifierM.circuitOperations, Verifier.operations_bind, Verifier.Operations.circuitOperations,
    Verifier.Operations.interactions, List.map_append, Operations.FullRequirements,
    Operations.interactions_append, List.forall_mem_append]
  constructor
  · change closed.emit.circuitOperations.FullRequirements env
    unfold Operations.FullRequirements
    rw [closed.emit_interactions]
    exact requirements
  · exact Verifier.checkZeros_requirements _ _ _

/-- Forget the boundary while retaining all committed rows. -/
def project {ens : Ensemble F PublicIO}
    {registered : closed.circuit.channels ⊆ ens.channels} (witness : EnsembleWitness (closed.install ens registered)) :
    EnsembleWitness ens :=
  witness.withEnsemble ens rfl

@[simp] theorem project_tables {ens : Ensemble F PublicIO}
    {registered : closed.circuit.channels ⊆ ens.channels} (witness : EnsembleWitness (closed.install ens registered)) :
    (closed.project witness).tables = witness.tables := rfl

@[simp] theorem project_data {ens : Ensemble F PublicIO}
    {registered : closed.circuit.channels ⊆ ens.channels} (witness : EnsembleWitness (closed.install ens registered)) :
    (closed.project witness).data = witness.data := rfl

@[simp] theorem project_publicInput {ens : Ensemble F PublicIO}
    {registered : closed.circuit.channels ⊆ ens.channels} (witness : EnsembleWitness (closed.install ens registered)) :
    (closed.project witness).publicInput = witness.publicInput := rfl

/-- Raw physical constraints are unchanged; verifier assertions are enforced by balance. -/
theorem project_constraints {ens : Ensemble F PublicIO}
    {registered : closed.circuit.channels ⊆ ens.channels} (witness : EnsembleWitness (closed.install ens registered)) :
    witness.Constraints ↔ (closed.project witness).Constraints := Iff.rfl

/-- Forget only the assertion checks, keeping the exactly-once boundary interactions. -/
def interactionView {ens : Ensemble F PublicIO}
    {registered : closed.circuit.channels ⊆ ens.channels} (witness : EnsembleWitness (closed.install ens registered)) :
    EnsembleWitness (closed.withInteractions ens registered) :=
  witness.withEnsemble _ rfl

@[simp] theorem interactionView_data {ens : Ensemble F PublicIO}
    {registered : closed.circuit.channels ⊆ ens.channels}
    (witness : EnsembleWitness (closed.install ens registered)) :
    (closed.interactionView witness).data = witness.data := rfl

/-- Exact verifier ledger, including all old traffic and two occurrences per new assertion. -/
theorem verifier_interactions (ens : Ensemble F PublicIO)
    (registered : closed.circuit.channels ⊆ ens.channels) (env : Environment F) (selected : RawChannel F) :
    (closed.install ens registered).verifierOperations.interactionValuesWith selected env =
      (closed.withInteractions ens registered).verifierOperations.interactionValuesWith selected env ++
        (Verifier.checkZeros (closed.channelName ens) closed.operations.constraints).circuitOperations.interactionValuesWith
          selected env := by
  simp only [install, withInteractions, Ensemble.verifierOperations, Verifier.Program.andThen_values]
  change _ ++ ((closed.emit >>= fun _ => Verifier.checkZeros (closed.channelName ens)
    closed.operations.constraints).circuitOperations.interactionValuesWith selected env) = _
  simp only [VerifierM.circuitOperations, Verifier.operations_bind, Verifier.Operations.circuitOperations,
    Verifier.Operations.interactions, List.map_append, Operations.interactionValuesWith,
    Operations.interactionsWith, Operations.interactions_append, List.filter_append, List.map_append,
    List.append_assoc]
  rfl

/-- On every other channel, removing assertion checks preserves the complete literal ledger. -/
theorem interactionView_interactions {ens : Ensemble F PublicIO}
    {registered : closed.circuit.channels ⊆ ens.channels}
    (witness : EnsembleWitness (closed.install ens registered)) (selected : RawChannel F)
    (different : closed.channel ens ≠ selected) :
    (closed.interactionView witness).interactionsWith selected = witness.interactionsWith selected := by
  change _ = (closed.install ens registered).verifierOperations.interactionValuesWith selected
    (Environment.fromInput witness.publicInput witness.data) ++ _
  rw [closed.verifier_interactions ens registered,
    Verifier.checkZeros_other_values _ _ _ _ different, List.append_nil]
  rfl

/-- Only the added assertion program can emit on its fresh channel. -/
theorem installed_check_interactions {ens : Ensemble F PublicIO}
    {registered : closed.circuit.channels ⊆ ens.channels}
    (witness : EnsembleWitness (closed.install ens registered)) :
    witness.interactionsWith (closed.channel ens) =
      (Verifier.checkZeros (closed.channelName ens) closed.operations.constraints).circuitOperations.interactionValuesWith
        (closed.channel ens) (Environment.fromInput witness.publicInput witness.data) := by
  have fresh := VerifierChannel.fresh closed.name (closed.withInteractions ens registered)
  have physical : witness.toTables.interactionsWith (closed.channel ens) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    apply List.flatMap_eq_nil_iff.mpr
    intro row _
    exact fresh.tables table.component
      (EnsembleWitness.component_mem_tables_of_mem (witness := closed.interactionView witness) member) _
  change (closed.install ens registered).verifierOperations.interactionValuesWith (closed.channel ens)
    (Environment.fromInput witness.publicInput witness.data) ++ _ = _
  have verifierEmpty : (closed.withInteractions ens registered).verifierOperations.interactionValuesWith
      (closed.channel ens) (Environment.fromInput witness.publicInput witness.data) = [] :=
    fresh.verifier _
  rw [closed.verifier_interactions ens registered, verifierEmpty, List.nil_append, physical, List.append_nil]

/-- Abstract balance on the new channel enforces exactly the original closed checks. -/
theorem check_balanced_iff {ens : Ensemble F PublicIO}
    {registered : closed.circuit.channels ⊆ ens.channels}
    (witness : EnsembleWitness (closed.install ens registered)) :
    witness.BalancedChannel (closed.channel ens) ↔ closed.Checks witness.data := by
  rw [EnsembleWitness.BalancedChannel, closed.installed_check_interactions]
  change BalancedInteractions ((Verifier.checkZeros (closed.channelName ens) closed.operations.constraints).circuitOperations.interactionValuesWith
    (Verifier.zeroChannel (closed.channelName ens)).toRaw (Environment.fromInput witness.publicInput witness.data)) ↔ _
  rw [Verifier.checkZeros_balanced_iff]
  have transport := closed.constraints 0 (Environment.fromInput witness.publicInput witness.data)
  simpa [Checks, Operations.ConstraintsHold, closed.lookups] using transport

/-- The assertion channel is separate from the existing registry. -/
theorem channel_not_mem (ens : Ensemble F PublicIO) :
    closed.channel ens ∉ ens.channels :=
  (VerifierChannel.fresh closed.name ens).unregistered

/-- On any channel other than the fresh assertion channel, installation adds exactly the source
circuit's literal emissions. The assertion channel contributes no occurrence there, including zero
multiplicities. -/
theorem install_verifier_interactions_of_ne (ens : Ensemble F PublicIO)
    (registered : closed.circuit.channels ⊆ ens.channels) (env : Environment F)
    (selected : RawChannel F) (different : closed.channel ens ≠ selected) :
    (closed.install ens registered).verifierOperations.interactionValuesWith selected env =
      ens.verifierOperations.interactionValuesWith selected env ++
        closed.operations.interactionValuesWith selected
          (Environment.fromInput (Input := unit) () env.data) := by
  change (ens.verifier.andThen (closed.program ens)).circuitOperations.interactionValuesWith selected env = _
  rw [Verifier.Program.andThen_values]
  have append : (closed.program ens).circuitOperations.interactionValuesWith selected env =
      closed.emit.circuitOperations.interactionValuesWith selected env ++
        (Verifier.checkZeros (closed.channelName ens) closed.operations.constraints).circuitOperations.interactionValuesWith
          selected env := by
    simp only [Verifier.Program.circuitOperations, Verifier.Program.operations, program,
      VerifierM.circuitOperations, Verifier.operations_bind, Verifier.Operations.circuitOperations,
      Verifier.Operations.interactions, List.map_append, Operations.interactionValuesWith,
      Operations.interactionsWith, Operations.interactions_append, List.filter_append]
  rw [append, Verifier.checkZeros_other_values _ _ _ _ different, List.append_nil, closed.emit_values]

/-- A registered channel is never the fresh assertion channel. -/
theorem install_verifier_interactions_of_mem (ens : Ensemble F PublicIO)
    (registered : closed.circuit.channels ⊆ ens.channels) (env : Environment F)
    (selected : RawChannel F) (member : selected ∈ ens.channels) :
    (closed.install ens registered).verifierOperations.interactionValuesWith selected env =
      ens.verifierOperations.interactionValuesWith selected env ++
        closed.operations.interactionValuesWith selected
          (Environment.fromInput (Input := unit) () env.data) :=
  closed.install_verifier_interactions_of_ne ens registered env selected fun same =>
    closed.channel_not_mem ens (same ▸ member)

/-- Removing only the new checks leaves the original ledger plus one boundary invocation.
The permutation moves that invocation past the physical rows without dropping any occurrence. -/
theorem interactionView_interactions_perm {ens : Ensemble F PublicIO}
    {registered : closed.circuit.channels ⊆ ens.channels}
    (witness : EnsembleWitness (closed.install ens registered)) (selected : RawChannel F) :
    ((closed.interactionView witness).interactionsWith selected).Perm
      ((closed.project witness).interactionsWith selected ++
        closed.interactionsWith witness.data selected) := by
  change ((ens.verifier.andThen closed.interactionProgram).circuitOperations.interactionValuesWith selected
    (Environment.fromInput witness.publicInput witness.data) ++
      witness.tables.flatMap (fun table => table.interactionsWith selected)).Perm _
  rw [Verifier.Program.andThen_values]
  change ((_ ++ closed.emit.circuitOperations.interactionValuesWith selected
    (Environment.fromInput witness.publicInput witness.data)) ++ _).Perm _
  rw [closed.emit_values]
  change ((_ ++ closed.interactionsWith witness.data selected) ++ _).Perm
    ((_ ++ witness.tables.flatMap (fun table => table.interactionsWith selected)) ++ _)
  simp only [List.append_assoc]
  exact (List.perm_append_comm ..).append_left _

/-- Channels unused by the boundary retain balance and the full original occurrence bound. -/
theorem project_balancedChannel {ens : Ensemble F PublicIO}
    {registered : closed.circuit.channels ⊆ ens.channels}
    (witness : EnsembleWitness (closed.install ens registered)) (selected : RawChannel F)
    (member : selected ∈ ens.channels) (silent : selected ∉ closed.circuit.channels)
    (balanced : witness.BalancedChannel selected) : (closed.project witness).BalancedChannel selected := by
  have different : closed.channel ens ≠ selected := by
    intro same
    exact closed.channel_not_mem ens (show closed.channel ens ∈ ens.channels from same ▸ member)
  have empty : closed.interactionsWith witness.data selected = [] :=
    closed.interactionsWith_nil_of_channel_not_mem witness.data selected silent
  have permutation := closed.interactionView_interactions_perm witness selected
  rw [closed.interactionView_interactions witness selected different, empty, List.append_nil] at permutation
  exact BalancedInteractions.of_perm balanced permutation

/-- Accepted boundaries retain the original interactions and enforce every assertion. -/
theorem balanced_iff {ens : Ensemble F PublicIO}
    {registered : closed.circuit.channels ⊆ ens.channels} (witness : EnsembleWitness (closed.install ens registered)) :
    witness.BalancedChannels ↔ (closed.interactionView witness).BalancedChannels ∧
      closed.Checks witness.data := by
  have fresh := VerifierChannel.fresh closed.name (closed.withInteractions ens registered)
  have different (selected : RawChannel F) (member : selected ∈ (closed.withInteractions ens registered).channels) :
      closed.channel ens ≠ selected := by
    intro same
    exact fresh.unregistered (show closed.channel ens ∈ (closed.withInteractions ens registered).channels from same ▸ member)
  constructor
  · intro balanced
    refine ⟨?_, (closed.check_balanced_iff witness).mp (balanced _ (by simp [install]))⟩
    intro selected member
    change BalancedInteractions ((closed.interactionView witness).interactionsWith selected)
    rw [closed.interactionView_interactions witness selected (different selected member)]
    exact balanced selected (List.mem_append_left _ member)
  · rintro ⟨original, checked⟩ selected member
    rcases List.mem_append.mp member with member | member
    · change BalancedInteractions (witness.interactionsWith selected)
      rw [← closed.interactionView_interactions witness selected (different selected member)]
      exact original selected member
    · obtain rfl := List.mem_singleton.mp member
      exact (closed.check_balanced_iff witness).mpr checked

/-- The installed verifier only appends, so forgetting the boundary keeps every occurrence of the
remaining ledger on every channel. -/
theorem mem_interactionsWith_of_project {ens : Ensemble F PublicIO}
    {registered : closed.circuit.channels ⊆ ens.channels}
    (witness : EnsembleWitness (closed.install ens registered)) {selected : RawChannel F} {interaction : Interaction F}
    (member : interaction ∈ (closed.project witness).interactionsWith selected) :
    interaction ∈ witness.interactionsWith selected := by
  rcases EnsembleWitness.mem_interactionsWith.mp member with emitted | ⟨table, tableMem, emitted⟩
  · refine EnsembleWitness.mem_interactionsWith.mpr (Or.inl ?_)
    change interaction ∈ (ens.verifier.andThen (closed.program ens)).circuitOperations.interactionValuesWith
      selected (Environment.fromInput witness.publicInput witness.data)
    rw [Verifier.Program.andThen_values]
    exact List.mem_append_left _ emitted
  · exact EnsembleWitness.mem_interactionsWith.mpr (Or.inr ⟨table, tableMem, emitted⟩)

end ClosedVerifier
end Air.Flat
