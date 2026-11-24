import SP1Clean.Native.Operations.HintQueueSeal
import ToClean.Circuit.SubcircuitProjection
import ToClean.Air.MessageFilter

/-! # Physical identities of the outgoing queue-word table

Every row gets its scheduled word and indices from the fixed prefix. Its surviving cursor,
node and word interactions retain their original multiplicities, including all padding rows.
-/

namespace SP1Clean.HostHintSnapshot
open Circuit Air.Flat Semantics HostHintQueue

variable {p : ℕ} [Fact p.Prime]

/-- The declared schedule fixes the actual padded height independently of prover hints. -/
theorem physical_height (hints : List Bytes) (t : Table (ZMod p)) (same : t.component = component hints) :
    t.table.length = (inventory (p := p) hints).height := by
  have fixed := t.fixed_rows_match
  rw [same] at fixed
  exact fixed.1.trans (UInt64.toNat_ofNatLT ..)

/-- The shape recovered from the canonical data of every physical row is its public word or padding. -/
theorem physical_shape (hints : List Bytes) (t : Table (ZMod p)) (same : t.component = component hints)
    (i : Fin t.table.length) :
    (valueFromOffset Inputs 0 (t.environment t.table[i.val])).1 =
      (fixedShapes (p := p) hints)[i.val]'((physical_height hints t same) ▸ i.isLt) := by
  have fixed := t.fixed_rows_match
  rw [same] at fixed
  rw [Table.environment, valueFromOffset_fromArray]
  exact fixed_at hints ⟨i.val, (physical_height hints t same) ▸ i.isLt⟩ _ (fixed.2 i.val i.isLt)

/-- The complete row ledger follows its public shape and private pointers. -/
theorem ledger (hints : List Bytes) (r : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main hints r).operations offset).interactions =
      [(channel.pulledIf r.2.2 (r.1.before r.2.1)).toRaw,
       (nodeChannel.pulledIf r.1.first (r.1.node r.2.1)).toRaw,
       (wordChannel.pulledIf r.1.active (r.1.word r.2.1)).toRaw,
       (channel.pushedIf r.1.active (r.1.after r.2.1)).toRaw] := by
  simp [main, Operations.interactions, circuit_norm, FormalAssertion.toSubcircuit_interactions]

/-- Both signed cursor occurrences of one physical word row, including inactive padding. -/
def walkValues (r : Inputs (ZMod p)) : List (Interaction (ZMod p)) :=
  [channel.pulledIfValue r.2.2 (r.1.before r.2.1), channel.pushedIfValue r.1.active (r.1.after r.2.1)]

/-- Select and evaluate the two physical walk occurrences at arbitrary row data. -/
theorem walk_values (hints : List Bytes) (r : Var Inputs (ZMod p)) (env : Environment (ZMod p)) (offset : ℕ) :
    ((main hints r).operations offset).interactionValuesWith channel.toRaw env = walkValues (eval env r) := by
  have occurrences : ((main hints r).operations offset).interactionsWith channel.toRaw =
      [(channel.pulledIf r.2.2 (r.1.before r.2.1)).toRaw, (channel.pushedIf r.1.active (r.1.after r.2.1)).toRaw] := by
    rw [Operations.interactionsWith, ledger]
    simp [channel, nodeChannel, wordChannel, Channel.toRaw, circuit_norm]
  rw [Operations.interactionValuesWith, occurrences]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulledIf, Channel.eval_pushedIf, walkValues]
  rcases r with ⟨⟨_, _, _, _, _, _, _, _⟩, ⟨_, _⟩, _⟩
  simp only [Shape.before, Shape.after, circuit_norm]
  simp only [ProvableType.eval_fields, Vector.map_map, Function.comp_def]

/-- Under the row's actual environment, the two immutable reads have precisely the public
first-word and active-word multiplicities, including at padded rows. -/
theorem lookup_occurrences (hints : List Bytes) (env : Environment (ZMod p)) :
    let r := valueFromOffset Inputs 0 env
    let interactions := (component hints).operations.interactionValues env
    nodeChannel.pulledIfValue r.1.first (r.1.node r.2.1) ∈ interactions ∧
      wordChannel.pulledIfValue r.1.active (r.1.word r.2.1) ∈ interactions := by
  let x : Var Inputs (ZMod p) := varFromOffset Inputs 0
  rw [Operations.interactionValues, Component.interactions_eq]
  change _ ∈ (((main hints x).operations (size Inputs)).interactions).map (·.eval env) ∧
    _ ∈ (((main hints x).operations (size Inputs)).interactions).map (·.eval env)
  rw [ledger]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulledIf, Channel.eval_pushedIf]
  have cells : eval env x = valueFromOffset Inputs 0 env := eval_varFromOffset_valueFromOffset ..
  rw [← cells]
  have node : ProvableStruct.eval env (x.1.node x.2.1) = (eval env x).1.node (eval env x).2.1 := by
    simp [Shape.node, circuit_norm]
  have word : ProvableStruct.eval env (x.1.word x.2.1) = (eval env x).1.word (eval env x).2.1 := by
    simp [Shape.word, circuit_norm]
  simp only [node, word, circuit_norm]

/-- An active immutable demand belongs to its original physical table and channel. -/
theorem physical_lookups (hints : List Bytes) (t : Table (ZMod p)) (same : t.component = component hints) (i : Fin t.table.length) :
    let r := valueFromOffset Inputs 0 (t.environment t.table[i.val])
    (r.1.first = 1 → nodeChannel.pulledValue (r.1.node r.2.1) ∈ t.interactionsWith nodeChannel.toRaw) ∧
      (r.1.active = 1 → wordChannel.pulledValue (r.1.word r.2.1) ∈ t.interactionsWith wordChannel.toRaw) := by
  let row := t.table[i.val]
  have found := lookup_occurrences (p := p) hints (t.environment row)
  rw [← same] at found
  constructor
  · intro one
    rw [Table.interactionsWith_eq_filter]
    exact List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨row, List.getElem_mem _, by simpa only [row, one, Channel.pulledIfValue, Channel.pulledValue] using found.1⟩, by simp [Channel.pulledValue]⟩
  · intro one
    rw [Table.interactionsWith_eq_filter]
    exact List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨row, List.getElem_mem _, by simpa only [row, one, Channel.pulledIfValue, Channel.pulledValue] using found.2⟩, by simp [Channel.pulledValue]⟩

/-- Recover the fixed admission check and the physical cursor multiplicity from constraints alone. -/
theorem count_of_constraints (hints : List Bytes) (env : Environment (ZMod p))
    (checked : (component hints).operations.ConstraintsHold env) :
    fits hints = true ∧ (valueFromOffset Inputs 0 env).2.2 = (valueFromOffset Inputs 0 env).1.active := by
  have raw := (Component.constraintsHold_iff env).mp checked
  let r : Var Inputs (ZMod p) := varFromOffset Inputs 0
  change ((main hints r).operations (size Inputs)).ConstraintsHold env at raw
  have cells : eval env r = valueFromOffset Inputs 0 env := eval_varFromOffset_valueFromOffset ..
  rw [← cells]
  simp only [main, circuit_norm] at raw
  have gate := raw _ (Or.inl rfl)
  have count := raw _ (Or.inr (Or.inl rfl))
  rw [eval_sub, sub_eq_zero] at count
  change (if fits hints then (0 : ZMod p) else 1) = 0 at gate
  by_cases pass : fits hints = true
  · exact ⟨pass, by simpa only [circuit_norm] using count⟩
  · simp [pass] at gate

namespace Seal

/-- Fixed registration gives exactly one physical seal row. -/
theorem physical_height (hints : List Bytes) (t : Table (ZMod p)) (same : t.component = component hints) :
    t.table.length = 1 := by
  have fixed := t.fixed_rows_match
  rw [same] at fixed
  exact fixed.1

/-- The private clock, head and allocation frontier read from the one physical seal row. -/
def physicalState (hints : List Bytes) (t : Table (ZMod p)) (same : t.component = component hints) : State (ZMod p) :=
  let row := t.table[0]'(by rw [physical_height hints t same]; decide)
  (valueFromOffset Inputs 0 (t.environment row)).2.1

/-- Every seal row carries the actual initial and terminal word-walk occurrences, for arbitrary
private cells. Its ticket only affects the separate queue-state publication. -/
theorem walk_ledger (hints : List Bytes) (env : Environment (ZMod p)) :
    (component hints).operations.interactionValuesWith channel.toRaw env =
      [channel.pushedValue (endpoint 0 (valueFromOffset Inputs 0 env).2.1.head),
       channel.pulledValue (endpoint (wordRows hints) 0)] := by
  let r : Var Inputs (ZMod p) := varFromOffset Inputs 0
  have occurrences : ((main hints r).operations (size Inputs)).interactionsWith channel.toRaw =
      [(channel.pushed ⟨const (Address.ofNat 0), r.2.1.head, const (Address.ofNat 0)⟩).toRaw,
       (channel.pulled (const (endpoint (wordRows hints) 0))).toRaw] := by
    rw [Operations.interactionsWith, ledger]
    simp [channel, stateChannel, Channel.toRaw, circuit_norm]
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change (((main hints r).operations (size Inputs)).interactionsWith channel.toRaw).map (·.eval env) = _
  rw [occurrences]
  have cells : eval env r = valueFromOffset Inputs 0 env := eval_varFromOffset_valueFromOffset ..
  have head := congrArg (fun x : Inputs (ZMod p) => x.2.1.head) cells
  simp only [circuit_norm] at head
  simp only [List.map_cons, List.map_nil, Channel.eval_pushed, Channel.eval_pulled, ProvableType.eval_const]
  simp [endpoint, circuit_norm, head, Address.ofNat_zero]

/-- Recover both endpoints of the word walk directly from the complete physical seal table. -/
theorem physical_walk_ledger (hints : List Bytes) (t : Table (ZMod p)) (same : t.component = component hints) :
    t.interactionsWith channel.toRaw =
      [channel.pushedValue (endpoint 0 (physicalState hints t same).head), channel.pulledValue (endpoint (wordRows hints) 0)] := by
  obtain ⟨row, one⟩ := List.length_eq_one_iff.mp (physical_height hints t same)
  simp only [Table.interactionsWith, physicalState, one, List.flatMap_singleton, same, walk_ledger, List.getElem_cons_zero]

end Seal
end SP1Clean.HostHintSnapshot
