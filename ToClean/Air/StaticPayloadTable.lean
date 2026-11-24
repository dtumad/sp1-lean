module

public import ToClean.Air.StaticProvider
public import ToClean.Air.TableBuild
public import ToClean.Circuit.EmittedInteraction

/-! # Constructing a counted preallocated payload provider

Clean supplies the fixed scheduler and the table verifier. This constructor uses the exact
preallocated row at every physical index, including duplicate and padding rows, together
with its assigned multiplicity. It exposes the full ledger of the resulting table.
-/

@[expose] public section

namespace StaticTable
open Circuit Air.Flat Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F] {Row : TypeMap} [ProvableType Row]

/-- All preallocated payload inputs in physical order. -/
def payloadInputs (t : StaticTable F Row) (counts : Fin t.height → F) :
    List (ProvablePair (Entry Row) field F) :=
  List.ofFn fun i => (t.fixedEntry i.val,counts i)

/-- Preallocation preserves the full verifier-chosen height. -/
theorem payloadInputs_length (t : StaticTable F Row) (counts : Fin t.height → F) :
    (t.payloadInputs counts).length = t.height := List.length_ofFn

/-- Both static-provider modes use the same committed multiplicity and verifier-fixed prefix. -/
theorem countedInput_fixedAt (t : StaticTable F Row) (bounded : t.height < UInt64.size)
    (counts : Fin t.height → F) (i : Fin t.height) :
    (t.generation bounded).FixedAt (UInt64.ofNat i.val) (t.fixedEntry i.val, counts i) := by
  rw [← t.fixedRow_evalRow bounded i]
  apply PreallocatedMode.fixedAt_of_typed_prefix (row := t.fixedRow .idx) (suffix := (.multiplicity : Cell F)) _ rfl
  intro cell mem
  change cell ∈ [.multiplicity] at mem
  exact List.mem_singleton.mp mem ▸ rfl

/-- The generated prefix matches every verifier-fixed cell at its original position. -/
theorem payloadInputs_fixed (t : StaticTable F Row) (target : Channel F Row) (valid : ∀ row, t.Spec row → ∀ data, target.Guarantees row data) (bounded : t.height < UInt64.size)
    (counts : Fin t.height → F) (data : ProverData F) (hint : ProverHint F) :
    let c := t.payloadComponent target valid bounded
    c.FixedRowsMatch ((t.payloadInputs counts).map (c.buildRow · data hint)) := by
  apply ((t.payloadComponent target valid bounded).fixedRowsMatch_buildRows _ _ _ (mode := t.payloadGeneration target bounded) rfl).mpr
  refine ⟨(t.payloadInputs_length counts).trans (UInt64.toNat_ofNatLT ..).symm,?_⟩
  intro i inside
  have ok := inside.trans_eq (t.payloadInputs_length counts)
  have indexed : (t.payloadInputs counts)[i] = (t.fixedEntry i,counts ⟨i,ok⟩) := List.getElem_ofFn ..
  change (t.payloadGeneration target bounded).FixedAt (UInt64.ofNat i) ((t.payloadInputs counts)[i].1,(t.payloadInputs counts)[i].2)
  rw [indexed]
  exact t.countedInput_fixedAt bounded counts ⟨i,ok⟩

/-- Fill every physical row using the verifier's typed prefix and the assigned reader count. -/
def buildPayload (t : StaticTable F Row) (target : Channel F Row) (valid : ∀ row, t.Spec row → ∀ data, target.Guarantees row data) (bounded : t.height < UInt64.size)
    (counts : Fin t.height → F) (data : ProverData F) : Table F :=
  let c := t.payloadComponent target valid bounded
  let inputs := t.payloadInputs counts
  Table.build c inputs (c.inputData inputs data) (.empty _)
    ((t.payloadInputs_length counts).trans_le bounded.le)
    (payloadInputs_fixed t target valid bounded counts _ _) (c.inputData_consistent inputs data)

/-- The provider permits positive multiplicity only on the first original copy of a row. -/
theorem buildPayload_valid (t : StaticTable F Row) (target : Channel F Row) (valid : ∀ row, t.Spec row → ∀ data, target.Guarantees row data) (bounded : t.height < UInt64.size)
    (counts : Fin t.height → F) (data : ProverData F)
    (assigned : ∀ i, counts i = 0 ∨ (t.fixedEntry i.val).eligible = 1) :
    (t.buildPayload target valid bounded counts data).Constraints ∧
      (t.buildPayload target valid bounded counts data).Guarantees := by
  have all r (mem : r ∈ t.payloadInputs counts) : r.2 = 0 ∨ r.1.eligible = 1 := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
    exact assigned i
  unfold buildPayload
  constructor
  · apply Table.build_constraints
    exact all
  · apply Table.build_guarantees
    exact all

private theorem payload_emits (t : StaticTable F Row) (target : Channel F Row) (valid : ∀ row, t.Spec row → ∀ data, target.Guarantees row data) (bounded : t.height < UInt64.size) (env : Environment F) :
    let c := t.payloadComponent target valid bounded
    c.operations.interactionValuesWith target.toRaw env =
      [target.emittedValue (c.rowInput env).2 (c.rowInput env).1.payload] := by
  let c := t.payloadComponent target valid bounded
  let I := ProvablePair (Entry Row) field
  let input := varFromOffset I (F := F) 0
  have transfers (x : Var (ProvablePair (Entry Row) field) F) (n : Nat) :
      (((t.payloadProvider target valid).main x).operations n).interactionsWith target.toRaw =
        [(target.pushedIf x.2 x.1.payload).toRaw] := by
    simp [payloadProvider,circuit_norm]
    rfl
  change c.operations.interactionValuesWith target.toRaw env = _
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((((t.payloadProvider target valid).main input).operations (size I)).interactionsWith target.toRaw).map _ = _
  rw [transfers,List.map_singleton,Channel.eval_pushedIf]
  have value := eval_varFromOffset_valueFromOffset (F := F) (ProvablePair (Entry Row) field) 0 env
  simp only [CircuitType.eval_provablePair_dispatch] at value
  have first := congrArg (fun r : ProvablePair (Entry Row) field F => r.1.payload) value
  have last := congrArg Prod.snd value
  simp only [ProvableStruct.eval_eq_eval,Entry.eval_payload] at first
  change [target.pushedIfValue (eval env input.2) (eval env input.1.payload)] =
    [target.emittedValue (valueFromOffset (ProvablePair (Entry Row) field) 0 env).2
      (valueFromOffset (ProvablePair (Entry Row) field) 0 env).1.payload]
  rw [← first,← last]
  rfl

/-- Every row retains its one physical occurrence on the original payload channel. -/
theorem buildPayload_interactions (t : StaticTable F Row) (target : Channel F Row) (valid : ∀ row, t.Spec row → ∀ data, target.Guarantees row data) (bounded : t.height < UInt64.size)
    (counts : Fin t.height → F) (data : ProverData F) :
    (t.buildPayload target valid bounded counts data).interactionsWith target.toRaw =
      List.ofFn (fun i : Fin t.height => target.emittedValue (counts i) (t.fixedEntry i.val).payload) := by
  unfold buildPayload
  refine (Table.build_interactions _ _ _ _ _ _ _ target.toRaw).trans ?_
  simp only [payload_emits,Component.rowInput_buildRow]
  let emit (r : ProvablePair (Entry Row) field F) := target.emittedValue r.2 r.1.payload
  change (t.payloadInputs counts).flatMap (fun r => [emit r]) = _
  rw [← List.map_eq_flatMap]
  unfold payloadInputs
  rw [List.map_ofFn]
  rfl

end StaticTable
