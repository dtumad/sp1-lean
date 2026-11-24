module

public import ToClean.Air.StaticPayloadTable
public import ToClean.Air.ReaderCounts

/-! # Building the verifier-fixed static membership table from assigned reader counts

Clean's membership provider emits the entire tagged fixed entry. This constructor proves its
fixed prefix, local constraints and counted ledger, including all ineligible duplicate and padding
rows. Assigned request indices can only name eligible copies.
-/

@[expose] public section

namespace StaticTable
open Circuit Air.Flat Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F] {Row : TypeMap} [ProvableType Row]

/-- Build the original tagged membership provider at its exact fixed height. -/
def buildMembership (t : StaticTable F Row) (bounded : t.height < UInt64.size)
    (counts : Fin t.height → F) (data : ProverData F) : Table F :=
  let c := t.component bounded
  let inputs := t.payloadInputs counts
  let localData := c.inputData inputs data
  Table.build c inputs localData (.empty _) ((t.payloadInputs_length counts).trans_le bounded.le) (by
    apply (c.fixedRowsMatch_buildRows _ _ _ (mode := t.generation bounded) rfl).mpr
    refine ⟨(t.payloadInputs_length counts).trans (UInt64.toNat_ofNatLT ..).symm, ?_⟩
    intro i inside
    have ok := inside.trans_eq (t.payloadInputs_length counts)
    have indexed : (t.payloadInputs counts)[i] = (t.fixedEntry i,counts ⟨i,ok⟩) := List.getElem_ofFn ..
    change (t.generation bounded).FixedAt (UInt64.ofNat i) ((t.payloadInputs counts)[i].1,(t.payloadInputs counts)[i].2)
    rw [indexed]
    exact t.countedInput_fixedAt bounded counts ⟨i,ok⟩)
    (c.inputData_consistent inputs data)

/-- Positive counts are allowed precisely at eligible physical membership rows. -/
theorem buildMembership_valid (t : StaticTable F Row) (bounded : t.height < UInt64.size)
    (counts : Fin t.height → F) (data : ProverData F)
    (assigned : ∀ i, counts i = 0 ∨ (t.fixedEntry i.val).eligible = 1) :
    (t.buildMembership bounded counts data).Constraints ∧ (t.buildMembership bounded counts data).Guarantees := by
  have all (r) (mem : r ∈ t.payloadInputs counts) : r.2 = 0 ∨ r.1.eligible = 1 := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
    exact assigned i
  unfold buildMembership
  exact ⟨Table.build_constraints _ _ _ _ _ _ _ all, Table.build_guarantees _ _ _ _ _ _ _ all⟩

private theorem membership_emits (t : StaticTable F Row) (bounded : t.height < UInt64.size) (env : Environment F) :
    let c := t.component bounded
    c.operations.interactionValuesWith t.channel.toRaw env = [t.channel.emittedValue (c.rowInput env).2 (c.rowInput env).1] := by
  let c := t.component bounded
  let I := ProvablePair (Entry Row) field
  let input := varFromOffset I (F := F) 0
  have transfer (x : Var I F) (offset : Nat) :
      ((t.provider.main x).operations offset).interactionsWith t.channel.toRaw = [(t.channel.pushedIf x.2 x.1).toRaw] := by
    simp [provider,circuit_norm]
    rfl
  change c.operations.interactionValuesWith t.channel.toRaw env = _
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change (((t.provider.main input).operations (size I)).interactionsWith t.channel.toRaw).map _ = _
  rw [transfer, List.map_singleton, Channel.eval_pushedIf]
  have value := eval_varFromOffset_valueFromOffset (F := F) (ProvablePair (Entry Row) field) 0 env
  simp only [CircuitType.eval_provablePair_dispatch] at value
  exact congrArg (fun r : I F => [t.channel.emittedValue r.2 r.1]) value

/-- Keep every verifier-fixed entry and every actual prover-owned count in physical order. -/
theorem buildMembership_interactions (t : StaticTable F Row) (bounded : t.height < UInt64.size)
    (counts : Fin t.height → F) (data : ProverData F) :
    (t.buildMembership bounded counts data).interactionsWith t.channel.toRaw =
      List.ofFn (fun i : Fin t.height => t.channel.emittedValue (counts i) (t.fixedEntry i.val)) := by
  unfold buildMembership
  refine (Table.build_interactions _ _ _ _ _ _ _ t.channel.toRaw).trans ?_
  simp only [membership_emits,Component.rowInput_buildRow]
  let emit (r : ProvablePair (Entry Row) field F) := t.channel.emittedValue r.2 r.1
  change (t.payloadInputs counts).flatMap (fun r => [emit r]) = _
  rw [← List.map_eq_flatMap]
  unfold payloadInputs
  rw [List.map_ofFn]
  rfl

/-- Count every occurrence of an eligible tagged request at its actual physical provider index.
The original padded table and the chronological request sequence balance on each message. -/
theorem assignedMembership (t : StaticTable F Row) (bounded : t.height < UInt64.size)
    (indices : List (Fin t.height)) (eligible : ∀ i ∈ indices, (t.fixedEntry i.val).eligible = 1)
    (data : ProverData F) :
    let counts := ReaderCounts.counts indices
    let table := t.buildMembership bounded (fun i => (counts[i] : F)) data
    table.Constraints ∧ table.Guarantees ∧ table.length = t.height ∧
      LogUpBalanced (table.interactionsWith t.channel.toRaw ++ indices.map (fun i => t.channel.pulledValue (t.fixedEntry i.val))) := by
  intro counts table
  have valid := t.buildMembership_valid bounded (fun i => (counts[i] : F)) data (by
    intro i
    by_cases present : i ∈ indices
    · exact Or.inr (eligible i present)
    · left
      have zero := (ReaderCounts.counts_at indices i).trans (List.count_eq_zero.mpr present)
      exact (congrArg (fun n : ℕ => (n : F)) zero).trans Nat.cast_zero)
  refine ⟨valid.1,valid.2,(List.length_map ..).trans (t.payloadInputs_length _),?_⟩
  rw [show table.interactionsWith t.channel.toRaw = _ from t.buildMembership_interactions bounded _ data]
  exact ReaderCounts.balanced t.channel (fun i : Fin t.height => t.fixedEntry i.val) indices

end StaticTable
