module

public import Clean.Air.Verifier
public import ToClean.Air.UnitBalance

/-! # Public assertions through verifier interactions

Clean's interaction-only verifier has no assertion adapter. Ordinary pulls of the checked values
and pushes of zero supply one: balance requires every value to be zero, with exactly two
occurrences per check. This uses Clean's existing operations, lowering and Rust emitter.

The check channel must have no other users. Adding these checks to an existing ensemble must
prove that separation and account for the new occurrences; the generic ledger equivalence below
does not establish those installation obligations. Delete this extension if Clean gains an
upstream public-assertion interface with the same semantics.
-/

@[expose] public section

namespace Verifier

variable {F : Type} [FiniteField F]

/-- Verifier composition appends the two literal operation lists. -/
@[circuit_norm] theorem operations_bind {α β : Type} (program : VerifierM F α)
    (next : α → VerifierM F β) :
    (program >>= next).operations = program.operations ++ (next program.1).operations := by
  rcases program with ⟨value, operations⟩
  simp only [VerifierM.bind_def, VerifierM.operations]
  rcases next value with ⟨result, more⟩
  rfl

/-- A dedicated channel certifying zero field values. Keep it disjoint from other channel users. -/
def zeroChannel (name : String) : Channel F field where
  name := name
  Guarantees value _ := value = 0

/-- Pull the checked value and supply zero using ordinary verifier primitives. -/
def checkZero (name : String) (value : Expression F) : VerifierM F Unit := do
  pull (zeroChannel name) value
  push (zeroChannel name) 0

/-- Abstract balance forces every checked value to zero. The verifier counts both occurrences. -/
theorem zero_ledger_iff (name : String) (values : List F) :
    BalancedInteractions (values.flatMap fun value =>
      [(zeroChannel name).pulledValue value, (zeroChannel name).pushedValue 0]) ↔
      ∀ value ∈ values, value = 0 := by
  rw [Channel.pairedLedger_balanced_iff (zeroChannel name) values (fun value => (value, 0))]
  constructor
  · intro permutation value member
    have present := permutation.mem_iff.mpr (List.mem_map.mpr ⟨value, member, rfl⟩)
    obtain ⟨_, _, same⟩ := List.mem_map.mp present
    exact same.symm
  · intro zero
    have same : values.map (fun _ => (0 : F)) = values.map (fun value => value) := by
      apply List.map_congr_left
      intro value member
      exact (zero value member).symm
    rw [same]

/-- One check emits one pull and one zero push, including when its input is zero. -/
theorem checkZero_values (name : String) (value : Expression F)
    (env : Environment F) :
    (checkZero name value).circuitOperations.interactionValuesWith (zeroChannel name).toRaw env =
      [(zeroChannel name).pulledValue (Expression.eval env value),
        (zeroChannel name).pushedValue 0] := by
  simp [checkZero, circuit_norm, _root_.Operations.interactionValuesWith,
    _root_.Operations.interactionsWith, Channel.pulledValue, Channel.pushedValue,
    AbstractInteraction.eval, ChannelInteraction.toRaw, Channel.pulled,
    Expression.eval, explicit_provable_type]

/-- Check each expression separately; equal expressions retain separate occurrences. -/
def checkZeros (name : String) (values : List (Expression F)) : VerifierM F Unit :=
  values.forM (checkZero name)

/-- Traversal preserves the operation order and every repeated check. -/
theorem checkZeros_operations (name : String) (values : List (Expression F)) :
    (checkZeros name values).operations = values.flatMap (fun value => (checkZero name value).operations) := by
  induction values with
  | nil => simp [checkZeros, circuit_norm]
  | cons value values ih =>
    change ((checkZero name value) >>= fun _ => checkZeros name values).operations = _
    rw [operations_bind, ih]
    rfl

/-- The literal evaluated ledger of all checks, without deduplication. -/
theorem checkZeros_values (name : String) (values : List (Expression F))
    (env : Environment F) :
    (checkZeros name values).circuitOperations.interactionValuesWith (zeroChannel name).toRaw env =
      values.flatMap (fun value =>
        [(zeroChannel name).pulledValue (Expression.eval env value),
          (zeroChannel name).pushedValue 0]) := by
  simp only [VerifierM.circuitOperations, checkZeros_operations, Operations.circuitOperations,
    Operations.interactions, List.map_flatMap]
  induction values with
  | nil => simp [circuit_norm, _root_.Operations.interactionValuesWith,
      _root_.Operations.interactionsWith]
  | cons value values ih =>
    simp only [List.flatMap_cons]
    simp only [_root_.Operations.interactionValuesWith, _root_.Operations.interactionsWith,
      _root_.Operations.interactions_append, List.filter_append, List.map_append] at ih ⊢
    rw [ih]
    exact congrArg (· ++ _) (checkZero_values name value env)

/-- Public assertions contribute no occurrence to any other channel. -/
theorem checkZeros_other_values (name : String) (values : List (Expression F))
    (env : Environment F) (channel : RawChannel F)
    (different : (zeroChannel (F := F) name).toRaw ≠ channel) :
    (checkZeros name values).circuitOperations.interactionValuesWith channel env = [] := by
  simp only [VerifierM.circuitOperations, checkZeros_operations, Operations.circuitOperations,
    Operations.interactions, List.map_flatMap]
  induction values with
  | nil => simp [circuit_norm, _root_.Operations.interactionValuesWith,
      _root_.Operations.interactionsWith]
  | cons value values ih =>
    simp only [List.flatMap_cons]
    simp only [_root_.Operations.interactionValuesWith, _root_.Operations.interactionsWith,
      _root_.Operations.interactions_append, List.filter_append, List.map_append] at ih ⊢
    rw [ih, List.append_nil]
    simp [checkZero, circuit_norm, ChannelInteraction.toRaw, Channel.pulled,
      different]

/-- Abstract balance of check interactions is equivalent to all assertions. -/
theorem checkZeros_balanced_iff (name : String) (values : List (Expression F))
    (env : Environment F) :
    BalancedInteractions
      ((checkZeros name values).circuitOperations.interactionValuesWith (zeroChannel name).toRaw env) ↔
      ∀ value ∈ values, Expression.eval env value = 0 := by
  rw [checkZeros_values]
  simpa only [List.flatMap_map, Function.comp_def, List.forall_mem_map] using
    zero_ledger_iff name (values.map (Expression.eval env))

/-- Zero-check ledgers have Boolean multiplicities and preserve every repeated occurrence. -/
theorem checkZeros_isBool (name : String) (values : List (Expression F)) (env : Environment F) :
    ∀ i ∈ (checkZeros name values).circuitOperations.interactionValuesWith (zeroChannel name).toRaw env,
      IsBool i.mult := by
  rw [checkZeros_values]
  intro i hi
  obtain ⟨value, _, hi⟩ := List.mem_flatMap.mp hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact .inr rfl

/-- Checked zero assertions imply the concrete LogUp equation, without a capacity premise. -/
theorem checkZeros_logUp_of_checks (name : String) (values : List (Expression F))
    (env : Environment F) (checked : ∀ value ∈ values, Expression.eval env value = 0) :
    LogUpBalanced ((checkZeros name values).circuitOperations.interactionValuesWith
      (zeroChannel name).toRaw env) :=
  ((checkZeros_balanced_iff name values env).mpr checked).logUp_of_isBool
    (checkZeros_isBool name values env)

/-- Local channel guarantees supply exactly the requested zero checks. -/
theorem checkZeros_guarantees (name : String) (values : List (Expression F))
    (env : Environment F) :
    (checkZeros name values).circuitOperations.FullGuarantees env ↔
      ∀ value ∈ values, Expression.eval env value = 0 := by
  simp only [VerifierM.circuitOperations, checkZeros_operations, Operations.circuitOperations,
    Operations.interactions, List.map_flatMap]
  induction values with
  | nil => simp [circuit_norm]
  | cons value values ih =>
    simp only [List.flatMap_cons, _root_.Operations.FullGuarantees,
      _root_.Operations.interactions_append, List.forall_mem_append] at ih ⊢
    rw [ih]
    simp [checkZero, circuit_norm, zeroChannel]

/-- Every zero check supplies its own outgoing requirement, independently of the checked value. -/
theorem checkZeros_requirements (name : String) (values : List (Expression F))
    (env : Environment F) : (checkZeros name values).circuitOperations.FullRequirements env := by
  simp only [VerifierM.circuitOperations, checkZeros_operations, Operations.circuitOperations,
    Operations.interactions, List.map_flatMap]
  induction values with
  | nil => simp [circuit_norm]
  | cons value values ih =>
    simp only [List.flatMap_cons, _root_.Operations.FullRequirements,
      _root_.Operations.interactions_append, List.forall_mem_append] at ih ⊢
    exact ⟨by simp [checkZero, circuit_norm, zeroChannel], ih⟩

/-- A bundled verifier for a public vector whose semantic meaning is that every value is zero. -/
def zerosProgram (name : String) (n : ℕ) : Program F (fields n) where
  main input := checkZeros name input.toList
  Spec values _ := ∀ value ∈ values.toList, value = 0
  soundness := by
    intro env guarantees
    rw [checkZeros_guarantees] at guarantees
    simpa [circuit_norm, explicit_provable_type] using guarantees

/-- Compose bundled verifier programs and retain both semantic specifications. -/
def Program.andThen {PublicIO : TypeMap} [ProvableType PublicIO]
    (first second : Program F PublicIO) : Program F PublicIO where
  main input := do first.main input; second.main input
  Spec input data := first.Spec input data ∧ second.Spec input data
  soundness := by
    intro env guarantees
    simp only [operations_bind, Operations.circuitOperations,
      Operations.interactions, List.map_append, _root_.Operations.FullGuarantees,
      _root_.Operations.interactions_append, List.forall_mem_append] at guarantees
    exact ⟨first.soundness env guarantees.1, second.soundness env guarantees.2⟩

/-- Composition retains both programs' full outgoing requirements. -/
theorem Program.andThen_requirements {PublicIO : TypeMap} [ProvableType PublicIO]
    (first second : Program F PublicIO) (env : Environment F) :
    (first.andThen second).circuitOperations.FullRequirements env ↔
      first.circuitOperations.FullRequirements env ∧ second.circuitOperations.FullRequirements env := by
  simp only [andThen, Program.circuitOperations, Program.operations, operations_bind,
    Operations.circuitOperations, Operations.interactions, List.map_append,
    _root_.Operations.FullRequirements, _root_.Operations.interactions_append, List.forall_mem_append]

/-- A channel guarantee for a composition holds for both of its constituent programs. -/
theorem Program.andThen_channelGuarantees {PublicIO : TypeMap} [ProvableType PublicIO]
    (first second : Program F PublicIO) (channel : RawChannel F) (env : Environment F) :
    (first.andThen second).circuitOperations.ChannelGuarantees channel env ↔
      first.circuitOperations.ChannelGuarantees channel env ∧
        second.circuitOperations.ChannelGuarantees channel env := by
  simp only [andThen, Program.circuitOperations, Program.operations, operations_bind,
    Operations.circuitOperations, Operations.interactions, List.map_append,
    _root_.Operations.ChannelGuarantees, _root_.Operations.interactions_append, List.forall_mem_append]

/-- Composition appends each channel's literal evaluated ledger. -/
theorem Program.andThen_values {PublicIO : TypeMap} [ProvableType PublicIO]
    (first second : Program F PublicIO) (channel : RawChannel F) (env : Environment F) :
    (first.andThen second).circuitOperations.interactionValuesWith channel env =
      first.circuitOperations.interactionValuesWith channel env ++
        second.circuitOperations.interactionValuesWith channel env := by
  change ((first.main (varFromOffset PublicIO 0) >>= fun _ =>
    second.main (varFromOffset PublicIO 0)).operations.circuitOperations).interactionValuesWith
      channel env = _
  simp only [operations_bind, Operations.circuitOperations, Operations.interactions,
    _root_.Operations.interactionValuesWith, _root_.Operations.interactionsWith,
    _root_.Operations.interactions_append, List.filter_append, List.map_append]

/-- Verifier composition covers exactly the channels of its two programs. -/
theorem Program.mem_andThen_channels {PublicIO : TypeMap} [ProvableType PublicIO]
    (first second : Program F PublicIO) (channel : RawChannel F) :
    channel ∈ (first.andThen second).channels ↔
      channel ∈ first.channels ∨ channel ∈ second.channels := by
  simp only [Program.channels, Program.channelsWithGuarantees, Program.channelsWithRequirements,
    Program.operations, andThen, operations_bind, Operations.channelsWithGuarantees,
    Operations.channelsWithRequirements, List.filterMap_append, List.mem_append]
  tauto

/-- Every occurrence of a zero-check program uses its dedicated channel. -/
theorem checkZeros_channels (name : String) (values : List (Expression F)) :
    (checkZeros name values).operations.channelsWithGuarantees ++
      (checkZeros name values).operations.channelsWithRequirements ⊆ [(zeroChannel name).toRaw] := by
  intro channel member
  simp only [checkZeros_operations, Operations.channelsWithGuarantees,
    Operations.channelsWithRequirements, List.filterMap_flatMap, List.mem_append,
    List.mem_flatMap] at member
  rcases member with ⟨value, _, member⟩ | ⟨value, _, member⟩ <;>
    simpa [checkZero, circuit_norm, Operations.channelsWithGuarantees,
      Operations.channelsWithRequirements] using member

/-- The bundled verifier enforces its entire specification through channel balance. -/
theorem zerosProgram_balanced_iff (name : String) (n : ℕ) (env : Environment F) :
    BalancedInteractions ((zerosProgram (F := F) name n).circuitOperations.interactionValuesWith
      (zeroChannel name).toRaw env) ↔
        (zerosProgram name n).Spec (eval env (varFromOffset (F := F) (fields n) 0)) env.data := by
  simpa [zerosProgram, circuit_norm, explicit_provable_type] using
    checkZeros_balanced_iff name (varFromOffset (fields n) 0).toList env

end Verifier
