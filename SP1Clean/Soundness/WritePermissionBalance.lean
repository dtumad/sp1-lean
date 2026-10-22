import SP1Clean.Native.Operations.WritePermission
import ToClean.Air.ChannelClosure
import ToClean.Circuit.InteractionRecovery

/-! # Byte permission authentication from a structural ledger

A permission row proves writability from its assertions and authenticated fixed-interval membership. Count-bounded balance
then authenticates every unit pull, provided the public verifier and every other component emit only
zero or unit-negative permission interactions. This separates the generic matching argument from the concrete assembly's
exhaustive source classification and from the store's byte-footprint proof.
-/

namespace SP1Clean.Soundness.WritePermission

open Circuit Air.Flat SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Consumers cannot forge a positive permission source, including on padding rows. -/
def Pulls (component : Component (ZMod p)) : Prop :=
  ∀ data physical, component.operations.ConstraintsHold (Environment.fromArray physical data) →
    ∀ interaction ∈ component.operations.interactionValuesWith WritePermissionProvider.channel.toRaw
      (Environment.fromArray physical data), interaction.mult = 0 ∨ interaction.mult = -1

omit [Fact (2 ^ 17 < p)] in
theorem pulls_of_silent (component : Component (ZMod p))
    (silent : WritePermissionProvider.channel.toRaw ∉ component.circuit.channels) : Pulls component := by
  intro data physical _ interaction member
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((component.circuit.main (varFromOffset component.Input 0)).operations
    (size component.Input)).interactionsWith WritePermissionProvider.channel.toRaw).map _ at member
  rw [InteractionRecovery.interactionsWith_main_eq_nil component.circuit.base _ _ _ silent] at member
  contradiction

theorem provider_constraints (image : ProgramImage) (env : Environment (ZMod p))
    (constraints : (WritePermissionProvider.component image : Component (ZMod p)).operations.ConstraintsHold env)
    (membership : (WritePermissionProvider.component image : Component (ZMod p)).operations.ChannelGuarantees
      image.writePermissionTable.channel.toRaw env) :
    IsBool ((WritePermissionProvider.component image : Component (ZMod p)).rowInput env).2 ∧
      (((WritePermissionProvider.component image : Component (ZMod p)).rowInput env).2 = 1 → WritePermissionProvider.Permitted image
        ((WritePermissionProvider.component image : Component (ZMod p)).rowInput env).1.address) :=
    by
  let component : Component (ZMod p) :=
    WritePermissionProvider.component image
  apply (component.weakSoundness (by intro _; trivial) constraints ?_).1
  apply (Operations.guarantees_iff component.operations
    [image.writePermissionTable.channel.toRaw] env (component.inChannelsOrGuarantees env)).mpr
  simpa only [List.mem_singleton, forall_eq] using membership

theorem active_provider_emission (image : ProgramImage) (input : Var WritePermissionProvider.Inputs (ZMod p))
    (offset : ℕ) :
    ((WritePermissionProvider.activeCircuit image).main input |>.operations offset).interactionsWith
      WritePermissionProvider.channel.toRaw = [(WritePermissionProvider.channel.pushed input.address).toRaw] := by
  have range (offset : ℕ) (value : Expression (ZMod p)) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil
      (Gadgets.ToBits.rangeCheck 16 (by have := Fact.out (p := 2 ^ 17 < p); omega))
      WritePermissionProvider.channel.toRaw (n := offset) value
      (by change _ ∉ []; simp) (by change _ ∉ []; simp)
  have order (offset : ℕ) (value : Var AddressOrder.Inputs (ZMod p)) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil AddressOrder.circuit
      WritePermissionProvider.channel.toRaw (n := offset) value
      (by change _ ∉ []; simp) (by change _ ∉ []; simp)
  simp only [WritePermissionProvider.activeCircuit, WritePermissionProvider.activeMain, circuit_norm]
  simp only [range, order, List.nil_append]
  simp [StaticTable.channel, ProgramImage.writePermissionTable, StaticTable.ofRows,
    WritePermissionProvider.channel, Channel.toRaw]

/-- Permission padding retains the physical occurrence with its activity multiplier. -/
theorem provider_emission (image : ProgramImage) (input : Var WritePermissionProvider.RowInput (ZMod p))
    (offset : ℕ) :
    ((WritePermissionProvider.circuit image).main input |>.operations offset).interactionsWith
      WritePermissionProvider.channel.toRaw =
        [AbstractInteraction.guard input.2 (WritePermissionProvider.channel.pushed input.1.address).toRaw] := by
  change ((Guarded.main (WritePermissionProvider.activeCircuit image)
    (WritePermissionProvider.guard_supported image) input).operations offset).interactionsWith _ = _
  rw [Guarded.main_interactionsWith, active_provider_emission]
  rfl

/-- A permission occurrence carries the actual row activity and semantic address. -/
theorem provider_payload (image : ProgramImage) (env : Environment (ZMod p))
    (interaction : Interaction (ZMod p))
    (member : interaction ∈ (WritePermissionProvider.component image : Component (ZMod p)).operations.interactionValuesWith
      WritePermissionProvider.channel.toRaw env) :
    interaction.mult = ((WritePermissionProvider.component image : Component (ZMod p)).rowInput env).2 ∧
      interaction.msg = (toElements ((WritePermissionProvider.component image : Component (ZMod p)).rowInput env).1.address).toArray := by
  change interaction.mult = (valueFromOffset WritePermissionProvider.RowInput 0 env).2 ∧
    interaction.msg = (toElements (valueFromOffset WritePermissionProvider.RowInput 0 env).1.address).toArray
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((WritePermissionProvider.circuit image).main
    (varFromOffset WritePermissionProvider.RowInput 0)).operations (size WritePermissionProvider.RowInput)
    |>.interactionsWith WritePermissionProvider.channel.toRaw).map _ at member
  rw [provider_emission] at member
  obtain rfl := List.mem_singleton.mp member
  simp only [AbstractInteraction.eval_guard, Channel.eval_pushed]
  constructor
  · change env.get 3 * 1 = env.get 3
    exact mul_one _
  · apply congrArg Vector.toArray
    ext i hi
    change i < 3 at hi
    interval_cases i <;>
      simp [valueFromOffset, circuit_norm, explicit_provable_type]

/-- A matched provider proves the requested byte writable in the fixed image. -/
theorem pull_permitted_of_sources {Public : TypeMap} [ProvableType Public]
    {assembly : Ensemble (ZMod p) Public} (image : ProgramImage)
    (witness : EnsembleWitness assembly) (constraints : witness.Constraints)
    (balance : BalancedInteractions (witness.interactionsWith WritePermissionProvider.channel.toRaw))
    (verifier : ∀ (input : Public (ZMod p)) (data : ProverData (ZMod p)),
      ∀ interaction ∈ assembly.verifierOperations.interactionValuesWith
      WritePermissionProvider.channel.toRaw (Environment.fromInput input data),
      interaction.mult = 0 ∨ interaction.mult = -1)
    (sources : ∀ component ∈ assembly.tables,
      component = (WritePermissionProvider.component image : Component (ZMod p)) ∨ Pulls component)
    (membership : ∀ table ∈ witness.tables,
      table.ChannelGuarantees image.writePermissionTable.channel.toRaw)
    (address : fields 3 (ZMod p)) (interaction : Interaction (ZMod p))
    (member : interaction ∈ witness.interactionsWith WritePermissionProvider.channel.toRaw)
    (active : interaction.mult = -1) (payload : interaction.msg = (toElements address).toArray) :
    WritePermissionProvider.Permitted image address := by
  obtain ⟨provider, providerMem, samePayload, nonzero, notPull⟩ :=
    exists_push_of_pull _ balance interaction member active
  rcases EnsembleWitness.mem_interactionsWith.mp providerMem with verifierMem | ⟨table, tableMem, providerMem⟩
  · exact ((verifier witness.publicInput witness.data provider verifierMem).elim nonzero notPull).elim
  · obtain ⟨physical, physicalMem, emitted⟩ := List.mem_flatMap.mp providerMem
    have checked := constraints table tableMem physical physicalMem
    simp only [Table.environment, witness.same_data table tableMem] at emitted checked
    rcases sources table.component
      (EnsembleWitness.component_mem_tables_of_mem tableMem) with fixed | pulls
    · rw [fixed] at emitted checked
      have authenticated := membership table tableMem physical physicalMem
      simp only [Table.environment, witness.same_data table tableMem] at authenticated
      rw [fixed] at authenticated
      have valid := provider_constraints image (Environment.fromArray physical witness.data)
        checked authenticated
      obtain ⟨multiplicity, message⟩ := provider_payload image _ provider emitted
      have enabled := valid.1.resolve_left (fun disabled => nonzero (multiplicity.trans disabled))
      have permitted := valid.2 enabled
      have same := message.symm.trans (samePayload.trans payload)
      have addressEq := congrArg (fromElements (M := fields 3)) (Vector.toArray_inj.mp same)
      simp only [ProvableType.fromElements_toElements] at addressEq
      exact Eq.mp (congrArg (WritePermissionProvider.Permitted image) addressEq) permitted
    · exact ((pulls witness.data physical checked provider emitted).elim nonzero notPull).elim

end SP1Clean.Soundness.WritePermission
