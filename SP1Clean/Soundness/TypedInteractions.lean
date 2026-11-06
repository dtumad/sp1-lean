import SP1Clean.Model.Channels
import SP1Clean.Model.InteractionProjection
import Clean.Air.FlatEnsemble
import ToClean.Air.TableBuild

/-! # Typed views of evaluated Clean interactions

Clean evaluates every channel interaction into the heterogeneous `Interaction` type.  This module
adds a proof-carrying typed view which retains that exact evaluated interaction while recovering the
message type from the channel.  It is deliberately an adapter over Clean's value, not a second bus
representation: erasing the wrapper gives `Operations.interactionValuesWith` definitionally up to
the list's membership proofs.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {F : Type} [FiniteField F]
variable {Message : TypeMap} [ProvableType Message]

/-- Full nested constraint satisfaction distributes over operation concatenation. This is the
`Operations.ConstraintsHold` counterpart of Clean's flat-list `constraintsHold_append`. -/
theorem operationsConstraintsHold_append (env : Environment F)
    (left right : Operations F) :
    (left ++ right).ConstraintsHold env ↔
      left.ConstraintsHold env ∧ right.ConstraintsHold env := by
  simp only [Operations.ConstraintsHold, Operations.constraints_append,
    Operations.lookups_append, List.forall_mem_append]
  tauto

/-- Extract the field equality represented by one retained Clean equality subcircuit. -/
theorem equality_of_singleton_constraintsHold
    (env : Environment F) (left right : Expression F) (offset : ℕ) :
    Operations.ConstraintsHold env
        [.subcircuit (@FormalAssertion.toSubcircuit F _ (ProvablePair field field)
          ProvablePair.instance (Gadgets.Equality.circuit field) offset (left, right))] →
      env left = env right := by
  intro constraints
  have difference :
      env (toElements (M := field) left)[0] - env (toElements (M := field) right)[0] = 0 := by
    simpa [Operations.ConstraintsHold, FormalAssertion.toSubcircuit,
      Gadgets.Equality.main, Gadgets.allZero, Circuit.forEach.operations_eq,
      FlatOperation.constraints, FlatOperation.lookups, eval_sub, circuit_norm] using constraints
  have leftEq : env (toElements (M := field) left)[0] = env left := rfl
  have rightEq : env (toElements (M := field) right)[0] = env right := rfl
  rwa [leftEq, rightEq, sub_eq_zero] at difference

/-- An evaluated Clean interaction together with evidence that it belongs to `channel`. -/
structure TypedInteraction (channel : Channel F Message) where
  raw : Interaction F
  channel_eq : raw.channel = channel.toRaw

namespace TypedInteraction

/-- A typed wrapper for Clean's evaluated gated pull. -/
def pulledIfValue (channel : Channel F Message) (enabled : F) (msg : Message F) :
    TypedInteraction channel where
  raw := channel.pulledIfValue enabled msg
  channel_eq := rfl

/-- A typed wrapper for Clean's evaluated gated push. -/
def pushedIfValue (channel : Channel F Message) (enabled : F) (msg : Message F) :
    TypedInteraction channel where
  raw := channel.pushedIfValue enabled msg
  channel_eq := rfl

/-- The proof carried beside an interaction is irrelevant; the original Clean value determines the
typed wrapper. -/
theorem raw_injective {channel : Channel F Message} :
    Function.Injective (@raw F _ Message _ channel) := by
  rintro ⟨-, -⟩ ⟨-, -⟩ rfl
  rfl

@[simp] theorem pulledIfValue_raw (channel : Channel F Message) (enabled : F) (msg : Message F) :
    (pulledIfValue channel enabled msg).raw = channel.pulledIfValue enabled msg := rfl

@[simp] theorem pushedIfValue_raw (channel : Channel F Message) (enabled : F) (msg : Message F) :
    (pushedIfValue channel enabled msg).raw = channel.pushedIfValue enabled msg := rfl

/-- The original Clean multiplicity. -/
def mult {channel : Channel F Message} (interaction : TypedInteraction channel) : F :=
  interaction.raw.mult

/-- Recover the channel's typed message from the original evaluated array. -/
noncomputable def message {channel : Channel F Message}
    (interaction : TypedInteraction channel) : Message F :=
  fromElements ⟨interaction.raw.msg, by
    simpa only [interaction.channel_eq, Channel.toRaw_arity] using interaction.raw.same_size⟩

@[simp] theorem message_toElements {channel : Channel F Message}
    (interaction : TypedInteraction channel) :
    (toElements interaction.message).toArray = interaction.raw.msg := by
  unfold message
  rw [ProvableType.toElements_fromElements]

theorem message_eq_iff {channel : Channel F Message}
    (interaction : TypedInteraction channel) (msg : Message F) :
    interaction.message = msg ↔
      interaction.raw.msg = (toElements msg).toArray := by
  unfold message
  rw [ProvableType.fromElements_eq_iff]
  exact ⟨congrArg Vector.toArray, fun h => Vector.toArray_inj.mp h⟩

@[simp] theorem pulledIfValue_mult (channel : Channel F Message) (enabled : F) (msg : Message F) :
    (pulledIfValue channel enabled msg).mult = enabled := rfl

@[simp] theorem pushedIfValue_mult (channel : Channel F Message) (enabled : F) (msg : Message F) :
    (pushedIfValue channel enabled msg).mult = enabled := rfl

@[simp] theorem pulledIfValue_message (channel : Channel F Message) (enabled : F)
    (msg : Message F) : (pulledIfValue channel enabled msg).message = msg := by
  rw [message_eq_iff]
  rfl

@[simp] theorem pushedIfValue_message (channel : Channel F Message) (enabled : F)
    (msg : Message F) : (pushedIfValue channel enabled msg).message = msg := by
  rw [message_eq_iff]
  rfl

/-- Attach the channel equality to an evaluated abstract interaction. -/
def eval (channel : Channel F Message) (env : Environment F) (interaction : AbstractInteraction F)
    (channel_eq : interaction.channel = channel.toRaw) : TypedInteraction channel where
  raw := interaction.eval env
  channel_eq := by simpa only [AbstractInteraction.eval_channel] using channel_eq

@[simp] theorem eval_raw (channel : Channel F Message) (env : Environment F)
    (interaction : AbstractInteraction F) (channel_eq : interaction.channel = channel.toRaw) :
    (eval channel env interaction channel_eq).raw = interaction.eval env := rfl

/-- Evaluating an exact syntactic channel pull produces its canonical typed value.  Factoring this
generically avoids re-normalizing large concrete message structures in every chip proof. -/
theorem eval_pulledIf (channel : Channel F Message) (env : Environment F)
    (enabled : Expression F) (msg : Message (Expression F)) :
    eval channel env (channel.pulledIf enabled msg).toRaw rfl =
      pulledIfValue channel (Expression.eval env enabled) (Eval.eval env msg) := by
  apply raw_injective
  change (channel.pulledIf enabled msg).toRaw.eval env =
    channel.pulledIfValue (Expression.eval env enabled) (Eval.eval env msg)
  simpa only [CircuitType.eval_expr] using
    (Channel.eval_pulledIf (channel := channel) (enabled := enabled) (msg := msg) (env := env))

/-- An active push satisfying Clean's requirement proves its typed channel predicate. -/
theorem guarantee_of_requirements {channel : Channel F Message}
    (interaction : TypedInteraction channel) (data : ProverData F)
    (requirements : interaction.raw.Requirements data)
    (push : interaction.raw.direction = .push) (active : interaction.mult ≠ 0) :
    channel.Guarantees interaction.message data := by
  obtain ⟨⟨rawChannel, direction, mult, message, sameSize⟩, channelEq⟩ := interaction
  dsimp only at channelEq
  subst rawChannel
  change direction = .push at push
  subst direction
  exact requirements active

end TypedInteraction

/-- The exact interactions emitted by `ops` on `channel`, with their message type recovered. -/
noncomputable def typedInteractionValuesWith (ops : Operations F)
    (channel : Channel F Message) (env : Environment F) : List (TypedInteraction channel) :=
  (ops.interactionsWith channel.toRaw).attach.map fun interaction =>
    TypedInteraction.eval channel env interaction.1
      (Operations.channel_eq_of_mem_interactionsWith interaction.2)

/-- Every syntactic interaction retained by `interactionsWith` has its canonical evaluated typed
wrapper in `typedInteractionValuesWith`.  This is the pointwise introduction rule for the adapter. -/
theorem mem_typedInteractionValuesWith (ops : Operations F)
    (channel : Channel F Message) (env : Environment F)
    {interaction : AbstractInteraction F}
    (member : interaction ∈ ops.interactionsWith channel.toRaw) :
    TypedInteraction.eval channel env interaction
        (Operations.channel_eq_of_mem_interactionsWith member) ∈
      typedInteractionValuesWith ops channel env := by
  unfold typedInteractionValuesWith
  exact List.mem_map.mpr ⟨⟨interaction, member⟩, by simp, rfl⟩

/-- A typed view of a channel with no syntactic interactions is empty. -/
theorem typedInteractionValuesWith_eq_nil_of_interactionsWith_eq_nil
    (ops : Operations F) (channel : Channel F Message) (env : Environment F)
    (empty : ops.interactionsWith channel.toRaw = []) :
    typedInteractionValuesWith ops channel env = [] := by
  simp [typedInteractionValuesWith, empty]

/-- The typed adapter neither invents nor drops evaluated interactions. -/
@[simp] theorem typedInteractionValuesWith_raw (ops : Operations F)
    (channel : Channel F Message) (env : Environment F) :
    (typedInteractionValuesWith ops channel env).map TypedInteraction.raw =
      ops.interactionValuesWith channel.toRaw env := by
  unfold typedInteractionValuesWith Operations.interactionValuesWith
  rw [List.map_map]
  change ((ops.interactionsWith channel.toRaw).attach.map
      (fun interaction => AbstractInteraction.eval env interaction.1)) = _
  exact List.attach_map_val

/-- Typed interaction values read only committed row cells; the channel predicates may still
read prover data. -/
theorem typedInteractionValuesWith_congr (ops : Operations F)
    (channel : Channel F Message) {env env' : Environment F} (cells : env.get = env'.get) :
    typedInteractionValuesWith ops channel env = typedInteractionValuesWith ops channel env' := by
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  simp only [typedInteractionValuesWith_raw]
  exact Operations.interactionValuesWith_congr cells

/-- Typed channel interactions emitted by every physical row of a Clean table. -/
noncomputable def typedTableInteractionsWith (table : Table F) (channel : Channel F Message) :
    List (TypedInteraction channel) :=
  table.table.flatMap fun row =>
    typedInteractionValuesWith table.component.operations channel (table.environment row)

/-- A table's literal ledger can be evaluated at any data view because interactions read only
row cells. This does not transport the channel's guarantee or requirement predicates. -/
theorem typedTableInteractionsWith_eq_flatMap (table : Table F) (data : ProverData F)
    (channel : Channel F Message) :
    typedTableInteractionsWith table channel = table.table.flatMap fun row =>
      typedInteractionValuesWith table.component.operations channel (Environment.fromArray row data) := by
  unfold typedTableInteractionsWith
  exact List.flatMap_congr fun _ _ => typedInteractionValuesWith_congr _ _ rfl

/-- Replacing stored evaluation data preserves the literal typed interaction list. -/
@[simp] theorem typedTableInteractionsWith_setData (table : Table F) (data : ProverData F)
    (consistent : data.tables table.component.circuit.name (size table.component.Input) =
      table.rowPrefixes (size table.component.Input)) (channel : Channel F Message) :
    typedTableInteractionsWith { table with data, data_consistent := consistent } channel =
      typedTableInteractionsWith table channel := by
  rw [typedTableInteractionsWith_eq_flatMap _ data,
    typedTableInteractionsWith_eq_flatMap table data]

/-- Erasing the typed table view recovers Clean's actual interaction list. -/
@[simp] theorem typedTableInteractionsWith_raw (table : Table F) (channel : Channel F Message) :
    (typedTableInteractionsWith table channel).map TypedInteraction.raw =
      table.interactionsWith channel.toRaw := by
  simp only [typedTableInteractionsWith, Table.interactionsWith, List.map_flatMap,
    typedInteractionValuesWith_raw]

/-- Typed interactions on one channel across the verifier and every witness table. -/
noncomputable def typedEnsembleInteractionsWith {PublicIO : TypeMap} [ProvableType PublicIO]
    {ensemble : Ensemble F PublicIO} (witness : EnsembleWitness ensemble)
    (channel : Channel F Message) : List (TypedInteraction channel) :=
  typedInteractionValuesWith ensemble.verifierOperations channel
      witness.data.publicEnvironment ++
    witness.tables.flatMap (typedTableInteractionsWith · channel)

/-- Erasure agrees exactly with Clean's ensemble-level channel interaction list. -/
@[simp] theorem typedEnsembleInteractionsWith_raw {PublicIO : TypeMap} [ProvableType PublicIO]
    {ensemble : Ensemble F PublicIO} (witness : EnsembleWitness ensemble)
    (channel : Channel F Message) :
    (typedEnsembleInteractionsWith witness channel).map TypedInteraction.raw =
      witness.interactionsWith channel.toRaw := by
  simp only [typedEnsembleInteractionsWith, Air.Flat.EnsembleWitness.interactionsWith,
    List.map_append, List.map_flatMap, typedTableInteractionsWith_raw,
    typedInteractionValuesWith_raw, EnsembleWitness.verifierInteractionsWith,
    Tables.interactionsWith, EnsembleWitness.toTables]

/-! ## Balance without an untyped lookup-key shadow -/

section TypedBalance

variable {p : ℕ} [Fact p.Prime]

/-- Use Clean's finite-field equality for the literal typed and untyped balance ledgers. -/
local instance cleanBalanceDecidableEq : DecidableEq (ZMod p) := FiniteField.instDecidableEq

variable {Message : TypeMap} [ProvableType Message]
variable {channel : Channel (ZMod p) Message}

/-- Active unit pushes, retaining typed messages and every repeated occurrence. -/
noncomputable def producedMessages (interactions : List (TypedInteraction channel)) :
    List (Message (ZMod p)) :=
  (interactions.filter fun interaction =>
    interaction.raw.direction = .push ∧ interaction.mult = 1).map TypedInteraction.message

/-- Active unit pulls, using Clean's direction and multiplicity directly. -/
noncomputable def consumedMessages (interactions : List (TypedInteraction channel)) :
    List (Message (ZMod p)) :=
  (interactions.filter fun interaction =>
    interaction.raw.direction = .pull ∧ interaction.mult = 1).map TypedInteraction.message

/-- A unit pull contributes its exact message to the consumed occurrence list. -/
theorem TypedInteraction.message_mem_consumedMessages
    (interaction : TypedInteraction channel) (interactions : List (TypedInteraction channel))
    (member : interaction ∈ interactions) (pull : interaction.raw.Pull) :
    interaction.message ∈ consumedMessages interactions := by
  unfold consumedMessages
  exact List.mem_map.mpr ⟨interaction, List.mem_filter.mpr ⟨member, by exact decide_eq_true pull⟩, rfl⟩

/-- An active syntactic `pulledIf` retained by an operation list contributes its evaluated message
to that exact list's consumed typed messages.  This packages the proof-irrelevant typed wrapper and
the centered-multiplicity calculation once, leaving chip contracts to prove only structural list
membership and semantic field bindings. -/
theorem eval_pulledIf_message_mem_consumedMessages (ops : Operations (ZMod p))
    (channel : Channel (ZMod p) Message) (env : Environment (ZMod p))
    (enabled : Expression (ZMod p)) (msg : Message (Expression (ZMod p)))
    (member : (channel.pulledIf enabled msg).toRaw ∈
      ops.interactionsWith channel.toRaw)
    (active : Expression.eval env enabled = 1) :
    Eval.eval env msg ∈ consumedMessages (typedInteractionValuesWith ops channel env) := by
  let abstract := (channel.pulledIf enabled msg).toRaw
  let typed := TypedInteraction.eval channel env abstract
    (Operations.channel_eq_of_mem_interactionsWith member)
  have typedMem : typed ∈ typedInteractionValuesWith ops channel env :=
    mem_typedInteractionValuesWith ops channel env member
  have typedEq : typed = TypedInteraction.pulledIfValue channel
      (Expression.eval env enabled) (Eval.eval env msg) := by
    simpa only [typed, abstract] using TypedInteraction.eval_pulledIf channel env enabled msg
  have pull : typed.raw.Pull := by
    simp only [typedEq, TypedInteraction.pulledIfValue_raw, Interaction.Pull,
      Channel.pulledIfValue, active, and_self]
  have messageMem :=
    TypedInteraction.message_mem_consumedMessages typed _ typedMem pull
  simpa only [typedEq, TypedInteraction.pulledIfValue_message] using messageMem

/-- A finished channel guarantee may be specialized to any exact active syntactic pull in the
operation list.  This is the pull-side counterpart of `guarantee_of_mem_producedTableMessages`:
chip contracts prove only interaction membership and the active gate, while this lemma performs
the generic descent through Clean's raw-channel representation. -/
theorem guarantee_of_eval_pulledIf_mem (ops : Operations (ZMod p))
    (channel : Channel (ZMod p) Message) (env : Environment (ZMod p))
    (enabled : Expression (ZMod p)) (msg : Message (Expression (ZMod p)))
    (member : (channel.pulledIf enabled msg).toRaw ∈
      ops.interactionsWith channel.toRaw)
    (guarantees : ops.ChannelGuarantees channel.toRaw env)
    (active : Expression.eval env enabled = 1) :
    channel.Guarantees (Eval.eval env msg) env.data := by
  rw [Operations.ChannelGuarantees, ← Operations.forall_interactionsWith_iff] at guarantees
  have pulled := guarantees _ member
  rw [ChannelInteraction.toRaw_guarantees] at pulled
  apply pulled
  · rfl
  · simp only [Channel.pulledIf, pulledIf_mult, active]

/-- Erase the dependent raw-channel representation after a typed wrapper has fixed its channel.
Pattern-matching the wrapper is important here: rewriting `raw.channel` directly gives Lean an
ill-typed dependent motive because the raw message vector is indexed by that channel's arity. -/
theorem TypedInteraction.guarantee_of_rawGuarantees
    (channel : Channel (ZMod p) Message) (interaction : TypedInteraction channel)
    (data : ProverData (ZMod p)) (rawGuarantees : interaction.raw.Guarantees data)
    (pull : interaction.raw.Pull) :
    channel.Guarantees interaction.message data := by
  obtain ⟨⟨rawChannel, direction, mult, message, sameSize⟩, channelEq⟩ := interaction
  dsimp only at channelEq
  subst rawChannel
  exact rawGuarantees pull.1 pull.2

/-- A typed evaluated interaction inherits its channel predicate from Clean's finished
`ChannelGuarantees` whenever it is an assumption-carrying active pull.  Unlike
`guarantee_of_eval_pulledIf_mem`, this form starts from the exact typed interaction list and is
therefore convenient after a chip's interaction-shape theorem has already hidden the syntax. -/
theorem TypedInteraction.guarantee_of_channelGuarantees
    (ops : Operations (ZMod p)) (channel : Channel (ZMod p) Message)
    (env : Environment (ZMod p)) (interaction : TypedInteraction channel)
    (member : interaction ∈ typedInteractionValuesWith ops channel env)
    (guarantees : ops.ChannelGuarantees channel.toRaw env)
    (pull : interaction.raw.Pull) :
    channel.Guarantees interaction.message env.data := by
  unfold typedInteractionValuesWith at member
  obtain ⟨⟨abstract, abstractMem⟩, -, rfl⟩ := List.mem_map.mp member
  rw [Operations.ChannelGuarantees, ← Operations.forall_interactionsWith_iff] at guarantees
  have evaluated : (abstract.eval env).Guarantees env.data :=
    AbstractInteraction.eval_guarantees.mpr (guarantees abstract abstractMem)
  exact TypedInteraction.guarantee_of_rawGuarantees channel _ env.data evaluated pull

/-- Full parent constraints restrict to the flattened constraints of any retained subcircuit.
This is the constraint analogue of `channelGuarantees_subcircuit_of_mem`; it is useful when a
chip-owned routing assertion deliberately lives inside a semantic proof-boundary subcircuit. -/
theorem constraintsHoldFlat_subcircuit_of_mem (env : Environment (ZMod p))
    (ops : Operations (ZMod p)) {n : ℕ} (sub : Subcircuit (ZMod p) n)
    (subMem : ⟨n, sub⟩ ∈ ops.subcircuits) (constraints : ops.ConstraintsHold env) :
    FlatOperation.ConstraintsHoldFlat env sub.ops.toFlat := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  have allConstraints := Operations.forall_constraints_iff.mp constraints.1
  have allLookups := Operations.forall_lookups_iff.mp constraints.2
  exact ⟨allConstraints.2 _ subMem, allLookups.2 _ subMem⟩

/-- Parent constraints restrict to the `main` operation list of any retained
`GeneralFormalCircuit` boundary.  This is the folded constraint analogue of
`channelGuarantees_subcircuit_of_mem`; callers need not unfold the completed subcircuit record. -/
theorem constraintsHold_generalSubcircuit_of_mem {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (env : Environment (ZMod p)) (ops : Operations (ZMod p))
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (input : Var Input (ZMod p)) (offset : ℕ)
    (subMem : ⟨offset, circuit.toSubcircuit offset input⟩ ∈ ops.subcircuits)
    (constraints : ops.ConstraintsHold env) :
    ((circuit.main input).operations offset).ConstraintsHold env := by
  have nested := constraintsHoldFlat_subcircuit_of_mem env ops
    (circuit.toSubcircuit offset input) subMem constraints
  rwa [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat,
    Circuit.constraintsHold_toFlat_iff] at nested

/-- Parent constraints restrict to the `main` operation list of any retained `FormalCircuit`
boundary. This is the witnessed-output companion to
`constraintsHold_generalSubcircuit_of_mem`. -/
theorem constraintsHold_formalSubcircuit_of_mem {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (env : Environment (ZMod p)) (ops : Operations (ZMod p))
    (circuit : FormalCircuit (ZMod p) Input Output)
    (input : Var Input (ZMod p)) (offset : ℕ)
    (subMem : ⟨offset, circuit.toSubcircuit offset input⟩ ∈ ops.subcircuits)
    (constraints : ops.ConstraintsHold env) :
    ((circuit.main input).operations offset).ConstraintsHold env := by
  have nested := constraintsHoldFlat_subcircuit_of_mem env ops
    (circuit.toSubcircuit offset input) subMem constraints
  rwa [FormalCircuit.toSubcircuit, Operations.toNested_toFlat,
    Circuit.constraintsHold_toFlat_iff] at nested

/-- Parent constraints restrict to the `main` operation list of any retained
`FormalAssertion` boundary. This is the assertion-only companion to
`constraintsHold_generalSubcircuit_of_mem`. -/
theorem constraintsHold_assertionSubcircuit_of_mem {Input : TypeMap}
    [ProvableType Input]
    (env : Environment (ZMod p)) (ops : Operations (ZMod p))
    (circuit : FormalAssertion (ZMod p) Input)
    (input : Var Input (ZMod p)) (offset : ℕ)
    (subMem : ⟨offset, circuit.toSubcircuit offset input⟩ ∈ ops.subcircuits)
    (constraints : ops.ConstraintsHold env) :
    ((circuit.main input).operations offset).ConstraintsHold env := by
  have nested := constraintsHoldFlat_subcircuit_of_mem env ops
    (circuit.toSubcircuit offset input) subMem constraints
  rwa [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Circuit.constraintsHold_toFlat_iff] at nested

/-- Clean requirements on a physical table prove the typed predicate of each exact active push. -/
theorem guarantee_of_mem_producedTableMessages (table : Table (ZMod p))
    (channel : Channel (ZMod p) Message)
    (requirements : table.ChannelRequirements channel.toRaw) (msg : Message (ZMod p))
    (member : msg ∈ producedMessages (typedTableInteractionsWith table channel)) :
    channel.Guarantees msg table.data := by
  unfold producedMessages at member
  obtain ⟨interaction, interactionMem, messageEq⟩ := List.mem_map.mp member
  obtain ⟨typedMem, positive⟩ := List.mem_filter.mp interactionMem
  simp only [decide_eq_true_eq] at positive
  have rawMem : interaction.raw ∈ table.interactionsWith channel.toRaw := by
    rw [← typedTableInteractionsWith_raw]
    exact List.mem_map_of_mem typedMem
  have rawRequirements : interaction.raw.Requirements table.data :=
    (Table.channelRequirements_iff_forall table channel.toRaw).mp requirements
      interaction.raw rawMem
  rw [← messageEq]
  exact interaction.guarantee_of_requirements table.data rawRequirements positive.1 (by rw [positive.2]; exact one_ne_zero)

/-- If every active typed pull message satisfies the typed channel predicate, then the original
operation list has Clean's exact `ChannelGuarantees`.  This transports semantic grounding back to
the circuit theorem without replacing or reinterpreting its interaction list. -/
theorem channelGuarantees_of_consumedMessages (ops : Operations (ZMod p))
    (channel : Channel (ZMod p) Message) (env : Environment (ZMod p))
    (guarantees : ∀ msg ∈ consumedMessages (typedInteractionValuesWith ops channel env),
      channel.Guarantees msg env.data) :
    ops.ChannelGuarantees channel.toRaw env := by
  rw [Operations.ChannelGuarantees, ← Operations.forall_interactionsWith_iff]
  intro interaction interactionMem
  have channelEq := Operations.channel_eq_of_mem_interactionsWith interactionMem
  obtain ⟨rawChannel, direction, mult, message⟩ := interaction
  dsimp only at channelEq
  subst rawChannel
  simp only [AbstractInteraction.Guarantees, Channel.toRaw]
  intro pullDirection pullMult
  let interaction : AbstractInteraction (ZMod p) :=
    ⟨channel.toRaw, direction, mult, message⟩
  have currentMem : interaction ∈ ops.interactionsWith channel.toRaw := by
    simpa only [interaction] using interactionMem
  let typed := TypedInteraction.eval channel env interaction
    (Operations.channel_eq_of_mem_interactionsWith currentMem)
  have typedMem : typed ∈ typedInteractionValuesWith ops channel env :=
    mem_typedInteractionValuesWith ops channel env currentMem
  have pull : typed.raw.Pull := ⟨pullDirection, pullMult⟩
  have messageMem :=
    TypedInteraction.message_mem_consumedMessages typed _ typedMem pull
  have grounded := guarantees typed.message messageMem
  have messageEq : typed.message =
      fromElements (message.map (Expression.eval env)) := by
    apply (TypedInteraction.message_eq_iff typed _).2
    simp only [typed, interaction, TypedInteraction.eval_raw, AbstractInteraction.eval,
      ProvableType.toElements_fromElements]
  rwa [messageEq] at grounded

@[simp] theorem producedMessages_append (left right : List (TypedInteraction channel)) :
    producedMessages (left ++ right) = producedMessages left ++ producedMessages right := by
  simp [producedMessages, List.filter_append]

@[simp] theorem consumedMessages_append (left right : List (TypedInteraction channel)) :
    consumedMessages (left ++ right) = consumedMessages left ++ consumedMessages right := by
  simp [consumedMessages, List.filter_append]

/-- A pull-only consumer prefix cannot contain the provider matching an active pull.
The provider may count repeated demand in a single physical row. -/
theorem provider_matches_active_pull
    (consumers providers : List (TypedInteraction channel))
    (balanced : BalancedInteractions ((consumers ++ providers).map TypedInteraction.raw))
    (consumerShape : ∀ interaction ∈ consumers,
      interaction.mult = 0 ∨ interaction.raw.Pull)
    (target : TypedInteraction channel) (targetMem : target ∈ consumers)
    (targetPull : target.raw.Pull) :
    ∃ provider ∈ providers,
      provider.message = target.message ∧ provider.mult ≠ 0 := by
  have targetRawMem : target.raw ∈ (consumers ++ providers).map TypedInteraction.raw :=
    List.mem_map.mpr ⟨target, List.mem_append_left providers targetMem, rfl⟩
  obtain ⟨rawProvider, rawProviderMem, sameMessage, providerPush⟩ :=
    balanced.exists_push_of_pull target.raw targetRawMem targetPull
  obtain ⟨provider, providerMem, rfl⟩ := List.mem_map.mp rawProviderMem
  rcases List.mem_append.mp providerMem with consumerMem | providerMem
  · rcases consumerShape provider consumerMem with zero | pull
    · exact (providerPush.1 zero).elim
    · exact (providerPush.2 pull.1 pull.2).elim
  · refine ⟨provider, providerMem, ?_, providerPush.1⟩
    rw [TypedInteraction.message_eq_iff]
    exact sameMessage.trans (TypedInteraction.message_toElements target).symm

/-- Encoding the selected typed occurrences recovers Clean's active message inventory. -/
private theorem activeMessages_eq_typed (interactions : List (TypedInteraction channel))
    (binary : ∀ interaction ∈ interactions, IsBool interaction.mult)
    (direction : Channel.Direction) :
    activeMessages (interactions.map TypedInteraction.raw) direction =
      ((if direction = .push then producedMessages interactions else consumedMessages interactions).map
        fun message => (toElements message).toArray) := by
  simp only [activeMessages, List.filter_map, List.map_map, Function.comp_def]
  cases direction <;> simp only [↓reduceIte, Channel.Direction.pull_eq_push_iff,
    producedMessages, consumedMessages, List.map_map, Function.comp_def,
    TypedInteraction.message_toElements]
  all_goals
    apply congrArg (List.map (fun interaction : TypedInteraction channel => interaction.raw.msg))
    apply List.filter_congr
    intro interaction member
    have countBool : interaction.raw.mult = 0 ∨ interaction.raw.mult = 1 := binary interaction member
    rcases countBool with h | h <;> simp [TypedInteraction.mult, h]

/-- Abstract Clean balance gives an exact permutation when every physical count is Boolean.
Count bounds stay with the verifier's chosen balance check; this transport needs no modular
integer reconstruction or extra capacity premise. -/
theorem producedMessages_perm_consumedMessages
    (interactions : List (TypedInteraction channel))
    (balanced : BalancedInteractions (interactions.map TypedInteraction.raw))
    (binary : ∀ interaction ∈ interactions, IsBool interaction.mult) :
    (producedMessages interactions).Perm (consumedMessages interactions) := by
  have encoding : Function.Injective (fun message : Message (ZMod p) => (toElements message).toArray) := by
    intro a b same
    have same := Vector.toArray_inj.mp same
    simpa only [ProvableType.fromElements_toElements] using congrArg fromElements same
  apply (List.map_perm_map_iff encoding).mp
  rw [List.perm_iff_count]
  intro message
  have counts := balanced.activeCount_push_eq_activeCount_pull_of_isBool message (by
    intro interaction member _
    obtain ⟨typed, typedMem, rfl⟩ := List.mem_map.mp member
    exact binary typed typedMem)
  simpa only [← count_activeMessages, activeMessages_eq_typed interactions binary,
    ↓reduceIte, Channel.Direction.pull_eq_push_iff] using counts

end TypedBalance

end SP1Clean.Soundness
