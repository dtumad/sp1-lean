import SP1Clean.Native.Operations.CommitmentStatement
import SP1Clean.Native.Operations.CommitmentBoundary
import SP1Clean.Proofs.Operations.CommitmentStatement
import SP1Clean.Model.Core.BankReplay
import ToClean.Air.Authentication
import ToClean.Air.EnsembleProjection
import ToClean.Air.TableBuild

/-! # Installing the immutable commitment statement

The fixed declaration provider and public assertions share one verifier-owned statement.
Existing physical positions are preserved. The new table uses Clean's ordinary preprocessed
payload provider; neither the prover's mutable bank nor per-call PublicValues echoes select it.
Forgetting the provider and the statement checks returns the original assembly's rows. Canonical
data changes only at the provider's name, so lookup-free original components keep their
constraints, and every original channel other than the declarations keeps its balance.

`Declared` records that each actual COMMIT/COMMIT_DEFERRED call carries the slot and word of a
declaration requested in a witness ledger. When the original components only pull declarations
and its verifier is silent on them, the balanced provider authenticates every request, so a
declared execution agrees with the immutable statement (`Declared.agrees`).
-/

namespace SP1Clean.Soundness.CommitmentEnsemble

open Circuit Air.Flat Model.Core

variable {p : ℕ} [Fact p.Prime]

/-- Every actual commitment call names the slot and word of a declaration requested in the
witness ledger. It does not assert that any declaration occurs. -/
def Declared {PublicIO : TypeMap} [ProvableType PublicIO] {ens : Ensemble (ZMod p) PublicIO}
    (witness : EnsembleWitness ens) (events : List Machine.ExecutionEvent) : Prop :=
  ∀ (deferred : Bool) (call : Machine.CoreSyscallEvent), .syscall call ∈ events →
    call.rawCode = (bankKind deferred).code →
      ∃ (slot : Fin 8) (value : Word (ZMod p)),
        CommitmentDeclaration.channel.pulledValue
            (⟨if deferred then 1 else 0, slot.val, value, 1⟩ : CommitmentDeclaration.Row (ZMod p)) ∈
          witness.interactionsWith CommitmentDeclaration.channel.toRaw ∧
        call.arg1 = BitVec.ofNat 64 slot.val ∧ call.arg2 = Word.toBitVec64 value

namespace Declared

variable {PublicIO PublicIO' : TypeMap} [ProvableType PublicIO] [ProvableType PublicIO']
  {ens : Ensemble (ZMod p) PublicIO} {ens' : Ensemble (ZMod p) PublicIO'}
  {witness : EnsembleWitness ens} {events events' : List Machine.ExecutionEvent}

/-- Agreement concerns occurrences only, so reordering the events preserves it. -/
theorem of_perm (declared : Declared witness events') (perm : events.Perm events') :
    Declared witness events :=
  fun deferred call member code => declared deferred call (perm.mem_iff.mp member) code

/-- A larger ledger on the declaration channel retains every request. -/
theorem transfer (declared : Declared witness events) {other : EnsembleWitness ens'}
    (ledger : ∀ interaction ∈ witness.interactionsWith CommitmentDeclaration.channel.toRaw,
      interaction ∈ other.interactionsWith CommitmentDeclaration.channel.toRaw) :
    Declared other events := by
  intro deferred call member code
  obtain ⟨slot, value, pulled, arg1, arg2⟩ := declared deferred call member code
  exact ⟨slot, value, ledger _ pulled, arg1, arg2⟩

/-- Authenticated requests make every actual declaration agree with the statement. -/
theorem agrees [Fact (2 ^ 17 < p)] (declared : Declared witness events) (statement : CommitmentStatement)
    (authenticated : ∀ record, CommitmentDeclaration.channel.pulledValue record ∈
      witness.interactionsWith CommitmentDeclaration.channel.toRaw → record ∈ CommitmentDeclaration.rows statement) :
    statement.Matches events := by
  intro event member
  cases event with
  | ordinary => trivial
  | syscall call =>
      have agrees (deferred : Bool) : statement.MatchesDeclaration deferred call := by
        intro code
        obtain ⟨slot, value, pulled, arg1, arg2⟩ := declared deferred call member (by cases deferred <;> exact code)
        exact CommitmentDeclaration.matches_declaration_of_member statement deferred slot value call
          (authenticated _ pulled) arg1 arg2 code
      exact ⟨agrees false, agrees true⟩

end Declared

/-- Append the provider, retaining every original row, channel occurrence and table position. -/
def withSource (statement : CommitmentStatement) (base : Ensemble (ZMod p) SP1PublicIO)
    (fresh : (CommitmentDeclaration.source (p := p) statement).circuit.name ∉ base.tables.map (·.circuit.name)) :
    Ensemble (ZMod p) SP1PublicIO where
  tables := base.tables ++ [CommitmentDeclaration.source statement]
  unique_names := by
    simpa only [List.map_append, List.map_cons, List.map_nil, List.concat_eq_append] using base.unique_names.concat fresh
  channels := base.channels ++ [CommitmentDeclaration.channel.toRaw]
  verifier := base.verifier

/-- Public bytes, deferred elements and flags are bound to the same fixed provider. -/
def install (statement : CommitmentStatement) (base : Ensemble (ZMod p) SP1PublicIO)
    (fresh : (CommitmentDeclaration.source (p := p) statement).circuit.name ∉ base.tables.map (·.circuit.name)) :
    Ensemble (ZMod p) SP1PublicIO :=
  (CommitmentBoundary.checker statement).install (withSource statement base fresh)

/-- Forget the statement checks and the appended provider, retaining every original physical row. -/
def project {statement : CommitmentStatement} {base : Ensemble (ZMod p) SP1PublicIO}
    {fresh : (CommitmentDeclaration.source (p := p) statement).circuit.name ∉ base.tables.map (·.circuit.name)}
    (witness : EnsembleWitness (install statement base fresh)) : EnsembleWitness base :=
  ((CommitmentBoundary.checker statement).project witness).projectPrefix base
    (by simp [withSource])
    (fun index => by simp [withSource, List.getElem_append_left index.isLt])
    (fun index => by simp [withSource, List.getElem_append_left index.isLt])

variable {statement : CommitmentStatement} {base : Ensemble (ZMod p) SP1PublicIO}
  {fresh : (CommitmentDeclaration.source (p := p) statement).circuit.name ∉ base.tables.map (·.circuit.name)}

@[simp] theorem project_publicInput (witness : EnsembleWitness (install statement base fresh)) :
    (project witness).publicInput = witness.publicInput := rfl

/-- Lookup-free original components keep their constraints across the changed canonical data. -/
theorem project_constraints (witness : EnsembleWitness (install statement base fresh))
    (lookupFree : ∀ component ∈ base.tables, component.operations.lookups = [])
    (checked : witness.Constraints) : (project witness).Constraints := by
  apply EnsembleWitness.projectPrefix_constraints_of _ _ _ _ ?_
    (((CommitmentBoundary.checker statement).project_constraints witness).mp checked)
  intro index row width valid
  have same : (withSource statement base fresh).tables[index.val]'(by simp [withSource]) =
      base.tables[index.val] := List.getElem_append_left index.isLt
  rw [same] at valid width
  rw [← width, Array.extract_size]
  exact Component.constraintsHold_setData _ (lookupFree _ (List.getElem_mem _)) valid

/-- Every original channel except the declarations keeps its complete ledger and balance. -/
theorem project_balancedChannel (witness : EnsembleWitness (install statement base fresh))
    (balanced : witness.BalancedChannels) (channel : RawChannel (ZMod p))
    (registered : channel ∈ base.channels) (different : channel ≠ CommitmentDeclaration.channel.toRaw) :
    (project witness).BalancedChannel channel := by
  have source := (((CommitmentBoundary.checker statement).project_balanced_iff witness).mp balanced).1
  let retained := (CommitmentBoundary.checker statement).project witness
  have preserves : ∀ index : Fin base.tables.length, ∀ row,
      row.size = ((withSource statement base fresh).tables[index.val]'(by simp [withSource])).width →
      base.tables[index.val].operations.interactionValuesWith channel
          (Environment.fromArray (row.extract 0 base.tables[index.val].width) (project witness).data) =
        ((withSource statement base fresh).tables[index.val]'(by simp [withSource])).operations.interactionValuesWith
          channel (Environment.fromArray row retained.data) := by
    intro index row width
    have same : (withSource statement base fresh).tables[index.val]'(by simp [withSource]) =
        base.tables[index.val] := List.getElem_append_left index.isLt
    rw [same] at width ⊢
    rw [← width, Array.extract_size]
    exact Component.interactionValuesWith_setData _ channel
  have silent : (retained.tables.drop base.tables.length).flatMap (·.interactionsWith channel) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    apply table.interactionsWith_nil_of_channel_not_mem
    have components := congrArg (List.drop base.tables.length) retained.tables_map_component
    rw [← List.map_drop] at components
    change _ = (base.tables ++ [CommitmentDeclaration.source statement]).drop base.tables.length at components
    rw [List.drop_left] at components
    have provider : table.component = CommitmentDeclaration.source statement := by
      have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
      rw [components] at mapped
      exact List.mem_singleton.mp mapped
    rw [provider]
    simp only [CommitmentDeclaration.source, StaticTable.payloadComponent, StaticTable.payloadProvider]
    simp only [circuit_norm, List.mem_append, List.mem_singleton, not_or]
    exact ⟨List.not_mem_nil, different⟩
  have ledger : (project witness).interactionsWith channel = retained.interactionsWith channel :=
    retained.projectPrefix_interactions (target := base) _ _ _ rfl channel preserves silent
  change BalancedInteractions ((project witness).interactionsWith channel)
  rw [ledger]
  exact source channel (List.mem_append_left _ registered)

/-- The statement checks establish its public encoding, including well-formedness. -/
theorem statement_spec (witness : EnsembleWitness (install statement base fresh))
    (balanced : witness.BalancedChannels) : CommitmentBoundary.Spec statement witness.publicInput :=
  CommitmentBoundary.spec_of_checks statement
    (((CommitmentBoundary.checker statement).project_balanced_iff witness).mp balanced).2.2

/-- The installed verifier adds nothing on the declaration channel to the original one. -/
private theorem verifier_declarations (witness : EnsembleWitness (install statement base fresh))
    (silent : ∀ env, base.verifierOperations.interactionValuesWith CommitmentDeclaration.channel.toRaw env = []) :
    witness.verifierInteractionsWith CommitmentDeclaration.channel.toRaw = [] := by
  change ((CommitmentBoundary.checker statement).install (withSource statement base fresh)).verifierOperations.interactionValuesWith
    CommitmentDeclaration.channel.toRaw (Environment.fromInput witness.publicInput witness.data) = []
  rw [PublicVerifier.install_verifier_interactions_of_mem _ _ _ _
    (List.mem_append_right _ (List.mem_singleton_self _))]
  exact silent _

/-- Requests of the original components survive forgetting the provider and the checks. -/
theorem project_declaration_mem (witness : EnsembleWitness (install statement base fresh))
    (silent : ∀ env, base.verifierOperations.interactionValuesWith CommitmentDeclaration.channel.toRaw env = [])
    {interaction : Interaction (ZMod p)}
    (member : interaction ∈ (project witness).interactionsWith CommitmentDeclaration.channel.toRaw) :
    interaction ∈ witness.interactionsWith CommitmentDeclaration.channel.toRaw := by
  let retained := (CommitmentBoundary.checker statement).project witness
  have preserves : ∀ index : Fin base.tables.length, ∀ row,
      row.size = ((withSource statement base fresh).tables[index.val]'(by simp [withSource])).width →
      base.tables[index.val].operations.interactionValuesWith CommitmentDeclaration.channel.toRaw
          (Environment.fromArray (row.extract 0 base.tables[index.val].width) (project witness).data) =
        ((withSource statement base fresh).tables[index.val]'(by simp [withSource])).operations.interactionValuesWith
          CommitmentDeclaration.channel.toRaw (Environment.fromArray row retained.data) := by
    intro index row width
    have same : (withSource statement base fresh).tables[index.val]'(by simp [withSource]) =
        base.tables[index.val] := List.getElem_append_left index.isLt
    rw [same] at width ⊢
    rw [← width, Array.extract_size]
    exact Component.interactionValuesWith_setData _ _
  have tables : (project witness).tables.flatMap (·.interactionsWith CommitmentDeclaration.channel.toRaw) =
      (retained.tables.take base.tables.length).flatMap (·.interactionsWith CommitmentDeclaration.channel.toRaw) :=
    retained.projectPrefix_tables_interactions (target := base) _ _ _ CommitmentDeclaration.channel.toRaw preserves
  have projectedSilent : (project witness).verifierInteractionsWith CommitmentDeclaration.channel.toRaw = [] :=
    silent _
  rcases EnsembleWitness.mem_interactionsWith.mp member with emitted | ⟨table, tableMem, emitted⟩
  · rw [projectedSilent] at emitted
    contradiction
  · have inPrefix : interaction ∈ (retained.tables.take base.tables.length).flatMap
        (·.interactionsWith CommitmentDeclaration.channel.toRaw) := by
      rw [← tables]
      exact List.mem_flatMap.mpr ⟨table, tableMem, emitted⟩
    obtain ⟨original, originalMem, originalEmitted⟩ := List.mem_flatMap.mp inPrefix
    exact EnsembleWitness.mem_interactionsWith.mpr
      (Or.inr ⟨original, List.mem_of_mem_take originalMem, originalEmitted⟩)

/-- When the original components only pull declarations and its verifier is silent on them, the
fixed provider authenticates every request in the balanced ledger. -/
theorem declared_member (witness : EnsembleWitness (install statement base fresh))
    (sources : ∀ component ∈ base.tables,
      component.Authenticates CommitmentDeclaration.channel (· ∈ CommitmentDeclaration.rows statement))
    (silent : ∀ env, base.verifierOperations.interactionValuesWith CommitmentDeclaration.channel.toRaw env = [])
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (record : CommitmentDeclaration.Row (ZMod p))
    (pulled : CommitmentDeclaration.channel.pulledValue record ∈
      witness.interactionsWith CommitmentDeclaration.channel.toRaw) :
    record ∈ CommitmentDeclaration.rows statement := by
  have ledger : witness.interactionsWith CommitmentDeclaration.channel.toRaw =
      witness.tables.flatMap (·.interactionsWith CommitmentDeclaration.channel.toRaw) := by
    simp only [EnsembleWitness.interactionsWith, verifier_declarations witness silent, List.nil_append,
      EnsembleWitness.toTables, Tables.interactionsWith]
  have registered : CommitmentDeclaration.channel.toRaw ∈ (install statement base fresh).channels :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
  have bal := balanced _ registered
  change BalancedInteractions (witness.interactionsWith CommitmentDeclaration.channel.toRaw) at bal
  rw [ledger] at bal pulled
  apply authenticated_pull_of_tables witness.tables CommitmentDeclaration.channel _ ?_ bal record pulled
  intro table tableMem
  have component := EnsembleWitness.component_mem_tables_of_mem tableMem
  change table.component ∈ base.tables ++ [CommitmentDeclaration.source statement] at component
  rcases List.mem_append.mp component with original | provider
  · exact Table.Authenticates.of_component table _ _ (sources _ original) (constraints table tableMem)
  · exact CommitmentDeclaration.source_authenticates statement table (List.mem_singleton.mp provider)
      (witness.dataConsistency_of_mem table tableMem) (constraints table tableMem)

end SP1Clean.Soundness.CommitmentEnsemble
