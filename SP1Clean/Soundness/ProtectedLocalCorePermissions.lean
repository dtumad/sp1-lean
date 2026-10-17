import SP1Clean.Soundness.ProtectedStorePermissions
import SP1Clean.Soundness.ProtectedLocalCoreProjection
import SP1Clean.Soundness.LocalCoreChannels

/-! # Authenticated byte permissions in the complete protected local AIR

The component inventory is exhaustive: only the fixed writable-interval table supplies permission;
the four store wrappers emit gated pulls; source, final, instruction and system rows, plus the
public verifier, otherwise remain silent. Consequently raw constraints and the ensemble's own count-bounded balance
authenticate every active permission request, with no separate provider-validity premise.
-/

namespace SP1Clean.Soundness.ProtectedLocalCore

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

private theorem old_component_silent (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (LocalCore.ensemble image source).tables) :
    WritePermissionProvider.channel.toRaw ∉ component.circuit.channels := by
  intro used
  exact old_channel_ne_permission _
    (List.mem_append_left _ (LocalCore.component_channels_subset image source component member used)) rfl

/-- The fixed provider is the only possible positive contributor to permission balance. -/
theorem component_permission_source (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image source).tables) :
    component = ({ circuit := WritePermissionProvider.circuit image, Assumptions := (WritePermissionProvider.circuit image).Assumptions } : Component (ZMod p)) ∨
      WritePermission.Pulls component := by
  change component ∈ tables image source at member
  rcases List.mem_append.mp member with stores | fixed
  · right
    rcases List.mem_or_eq_of_mem_set stores with stores | rfl
    · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
      · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
        · rcases List.mem_or_eq_of_mem_set stores with original | rfl
          · exact WritePermission.pulls_of_silent component
              (old_component_silent image source component original)
          · exact WritePermission.byte_pulls
        · exact WritePermission.half_pulls
      · exact WritePermission.word_pulls
    · exact WritePermission.double_pulls
  · rcases List.mem_cons.mp fixed with fixed | fixed
    · exact Or.inl fixed
    · right
      rw [List.mem_singleton.mp fixed]
      apply WritePermission.pulls_of_silent
      change WritePermissionProvider.channel.toRaw ∉ [image.writePermissionTable.channel.toRaw]
      simp [WritePermissionProvider.channel, StaticTable.channel, ProgramImage.writePermissionTable,
        StaticTable.ofRows, Channel.toRaw]

/-- The fixed interval table is the only component that may provide membership. -/
theorem component_membership_source (image : ProgramImage) (source : ExecutionSnapshot)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image source).tables) :
    component = WritePermissionProvider.membershipComponent image ∨
      image.writePermissionTable.channel.toRaw ∉ component.circuit.channelsWithRequirements := by
  change component ∈ tables image source at member
  rcases List.mem_append.mp member with stores | fixed
  · right
    have original (component : Component (ZMod p))
        (member : component ∈ (LocalCore.ensemble image source).tables) :
        image.writePermissionTable.channel.toRaw ∉ component.circuit.channelsWithRequirements := by
      intro used
      exact old_channel_ne_membership _ (List.mem_append_left _
        (LocalCore.component_channels_subset image source component member
          (List.mem_append_right _ used))) rfl
    rcases List.mem_or_eq_of_mem_set stores with stores | rfl
    · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
      · rcases List.mem_or_eq_of_mem_set stores with stores | rfl
        · rcases List.mem_or_eq_of_mem_set stores with old | rfl
          · exact original component old
          · have absent := original _ (List.getElem_mem (n := 25) (by
              change 25 < (LocalCore.tables (p := p) image source).length
              rw [LocalCore.tables_length]; decide))
            exact absent
        · have absent := original _ (List.getElem_mem (n := 26) (by
            change 26 < (LocalCore.tables (p := p) image source).length
            rw [LocalCore.tables_length]; decide))
          exact absent
      · have absent := original _ (List.getElem_mem (n := 27) (by
          change 27 < (LocalCore.tables (p := p) image source).length
          rw [LocalCore.tables_length]; decide))
        exact absent
    · have absent := original _ (List.getElem_mem (n := 28) (by
        change 28 < (LocalCore.tables (p := p) image source).length
        rw [LocalCore.tables_length]; decide))
      exact absent
  · rcases List.mem_cons.mp fixed with fixed | fixed
    · right
      rw [fixed]
      change image.writePermissionTable.channel.toRaw ∉ [WritePermissionProvider.channel.toRaw]
      simp [WritePermissionProvider.channel, StaticTable.channel, ProgramImage.writePermissionTable,
        StaticTable.ofRows, Channel.toRaw]
    · exact Or.inl (List.mem_singleton.mp fixed)

/-- Physical fixed prefixes and complete interval balance authenticate every permission row. -/
theorem membership_guarantees {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints)
    (balanced : witness.BalancedChannel image.writePermissionTable.channel.toRaw) :
    ∀ table ∈ witness.tables, table.ChannelGuarantees image.writePermissionTable.channel.toRaw := by
  apply (image.writePermissionTable.guarantees_of_balance
    (WritePermissionProvider.membership_height_lt_uint64 image) witness constraints balanced ?_
    (component_membership_source image source)).2
  intro interaction emitted _
  exact LocalCore.verifier_requirements image source _ interaction emitted

/-- The actual public verifier emits no permission traffic. Source checks keep their fresh channel. -/
theorem verifier_permission_silent (image : ProgramImage) (source : ExecutionSnapshot)
    (env : Environment (ZMod p)) :
    (ensemble image source).verifierOperations.interactionValuesWith
      WritePermissionProvider.channel.toRaw env = [] := by
  have different := old_channel_ne_permission (p := p) (LocalCore.sourceChannel image source)
    (List.mem_append_right _ (List.mem_singleton_self _))
  change ((LocalSourceBoundary.checker image source).install
    (LocalCore.baseEnsemble image source)).verifierOperations.interactionValuesWith _ env = []
  rw [PublicVerifier.install_verifier_interactions _ _ _ _ different]
  apply LocalCore.boundaryVerifier_silent image source
  intro member
  exact old_channel_ne_permission _ (List.mem_append_left _ member) rfl

/-- Every active permission request in the protected ledger names a writable native byte address. -/
theorem permission_pull_permitted {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (address : fields 3 (ZMod p)) (interaction : Interaction (ZMod p))
    (member : interaction ∈ witness.interactionsWith WritePermissionProvider.channel.toRaw)
    (active : interaction.mult = -1) (payload : interaction.msg = (toElements address).toArray) :
    WritePermissionProvider.Permitted image address :=
  WritePermission.pull_permitted_of_sources image witness constraints
    (balanced _ (List.mem_cons_self ..))
    (by intro input data emitted member
        rw [verifier_permission_silent] at member
        exact (List.not_mem_nil member).elim)
    (component_permission_source image source)
    (membership_guarantees witness constraints (balanced _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    address interaction member active payload

/-- A concrete active pull in any physical row inherits its provider's byte permission. -/
theorem row_pull_permitted {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (table : Table (ZMod p)) (tableMem : table ∈ witness.tables)
    (physical : Array (ZMod p)) (physicalMem : physical ∈ table.table)
    (gate : Expression (ZMod p)) (address : Var (fields 3) (ZMod p))
    (emitted : (WritePermissionProvider.channel.pulledIf gate address).toRaw ∈
      table.component.operations.interactionsWith WritePermissionProvider.channel.toRaw)
    (active : Expression.eval (Environment.fromArray physical witness.data) gate = 1) :
    WritePermissionProvider.Permitted image (eval (Environment.fromArray physical witness.data) address) := by
  apply permission_pull_permitted witness constraints balanced _
    ((WritePermissionProvider.channel.pulledIf gate address).toRaw.eval (Environment.fromArray physical witness.data))
  · apply EnsembleWitness.mem_interactionsWith.mpr
    refine Or.inr ⟨table, tableMem, List.mem_flatMap.mpr ⟨physical, physicalMem, ?_⟩⟩
    have shared : table.data = witness.data := witness.same_data table tableMem
    simpa only [Table.environment, shared, Operations.interactionValuesWith] using List.mem_map_of_mem emitted
  · simp only [Channel.eval_pulledIf, Channel.pulledIfValue, CircuitType.eval_expr, active]
  · simp only [Channel.eval_pulledIf, Channel.pulledIfValue]

end SP1Clean.Soundness.ProtectedLocalCore
