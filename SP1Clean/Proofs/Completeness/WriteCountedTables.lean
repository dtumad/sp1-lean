import SP1Clean.Soundness.WriteSourceActivity
import SP1Clean.Proofs.Completeness.WriteProbeTables
import SP1Clean.Proofs.Completeness.FieldClosure
import ToClean.Air.MessageFilter
import Mathlib.Algebra.BigOperators.Fin

/-! # Constructing the counted native WRITE supply and both physical ledgers

Every live predecessor has its own physical supply row. A request identifies the selected
source occurrence, so equal messages can be counted repeatedly without overfunding another
row. Both supply and read tables use their registered power-of-two demand padding.
-/

namespace SP1Clean.WriteProbe.Counted

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Select live original receipts in physical order. -/
def live (rows : List (ZMod p × Readback (ZMod p))) := (rows.filter (fun r => r.1 = 1)).map Prod.snd

/-- An assigned probe retains its exact occurrence and its full incoming clock. -/
abbrev Request (n : ℕ) (F : Type) := Fin n × fields 3 F

/-- Each original occurrence receives the precise number of probes that chose it. -/
def count {n : ℕ} (requests : List (Request n (ZMod p))) (i : Fin n) : ℕ := requests.countP (fun r => r.1 = i)

/-- Count every selected position in a single traversal of the original request sequence. -/
def counts {n : ℕ} (requests : List (Request n (ZMod p))) : Vector ℕ n :=
  requests.foldl (fun totals r => totals.set r.1.val (totals[r.1] + 1)) (Vector.replicate n 0)

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem counts_from {n : ℕ} (requests : List (Request n (ZMod p))) (start : Vector ℕ n) (i : Fin n) :
    (requests.foldl (fun (totals : Vector ℕ n) r => totals.set r.1.val (totals[r.1] + 1)) start)[i] =
      start[i] + count requests i := by
  induction requests generalizing start with
  | nil => simp [count]
  | cons r rest ih =>
    rw [List.foldl_cons, ih]
    by_cases same : r.1 = i
    · simp [count, same, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · have different : r.1.val ≠ i.val := fun eq => same (Fin.ext eq)
      simp [count, same, Vector.getElem_set_ne _ _ different]

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
theorem counts_at {n : ℕ} (requests : List (Request n (ZMod p))) (i : Fin n) : (counts requests)[i] = count requests i := by
  have zero : (Vector.replicate n (0 : ℕ))[i] = 0 := Vector.getElem_replicate i.isLt
  simpa only [counts, zero, Nat.zero_add] using counts_from requests (Vector.replicate n 0) i

/-- All live supply rows, with no deduplication by address or encoded version. -/
def allocated (records : List (Readback (ZMod p))) (requests : List (Request records.length (ZMod p))) :=
  let sourceArray := records.toArray
  let totals := counts requests
  List.ofFn fun i : Fin records.length => ReadbackSupply.populate (sourceArray[i.val]'(by simp [sourceArray])) totals[i]

omit [Fact (2 ^ 25 < p)] in
private theorem allocated_eq (records : List (Readback (ZMod p))) (requests : List (Request records.length (ZMod p))) :
    allocated records requests = List.ofFn (fun i : Fin records.length => ReadbackSupply.populate records[i] (count requests i)) := by
  simp only [allocated, List.getElem_toArray, counts_at]
  rfl

/-- Restore the probes in original WRITE header and packet-word order, regardless of source order. -/
def probes (records : List (Readback (ZMod p))) (requests : List (Request records.length (ZMod p))) :=
  let sourceArray := records.toArray
  requests.map fun r => populate (ReadbackSupply.populate (sourceArray[r.1.val]'(by simp [sourceArray])) 0).version r.2

omit [Fact (2 ^ 25 < p)] in
theorem probes_eq (records : List (Readback (ZMod p))) (requests : List (Request records.length (ZMod p))) :
    probes records requests = requests.map (fun r => populate (ReadbackSupply.populate records[r.1] 0).version r.2) := by
  simp only [probes, List.getElem_toArray]
  rfl

/-- The installed supply demand scheduler pads with all-zero inputs. -/
def padding : ReadbackSupply.Inputs (ZMod p) :=
  ⟨#v[0, 0, 0], ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, #v[0, 0, 0, 0], 0, 0⟩

/-- The complete fixed cells for the local supply table. -/
def physical (rows : List (ReadbackSupply.Inputs (ZMod p))) :=
  rows ++ List.replicate (WitnessGeneration.demandPadding rows.length) padding

/-- The local table uses Clean's generated rows and its own actual input prefix. -/
def table (rows : List (ReadbackSupply.Inputs (ZMod p))) (data : ProverData (ZMod p))
    (fits : WitnessGeneration.demandHeight rows.length ≤ UInt64.size) : Table (ZMod p) :=
  let actual : List (ReadbackSupply.Inputs (ZMod p)) := physical rows
  Table.build ReadbackSupply.component actual (ReadbackSupply.component.inputData actual data) (.empty _)
    (by change (rows ++ List.replicate _ padding).length ≤ _; simpa only [List.length_append, List.length_replicate, WitnessGeneration.add_demandPadding] using fits)
    (by trivial) (ReadbackSupply.component.inputData_consistent actual data)

/-- Constraints and channel guarantees for the actual table, including its disabled suffix. -/
theorem table_complete (rows : List (ReadbackSupply.Inputs (ZMod p)))
    (valid : ∀ row ∈ rows, ReadbackSupply.Valid row) (data : ProverData (ZMod p)) (fits) :
    (table rows data fits).Constraints ∧ (table rows data fits).Guarantees := by
  have all row (member : row ∈ physical rows) : ReadbackSupply.Valid row := by
    rcases List.mem_append.mp member with used | pad
    · exact valid row used
    · obtain rfl := List.eq_of_mem_replicate pad
      simp [ReadbackSupply.Valid, padding, ClockParts.Bounded]
  unfold table
  constructor
  · apply Table.build_constraints; exact all
  · apply Table.build_guarantees; exact all

private theorem receipts (rows : List (ReadbackSupply.Inputs (ZMod p))) (data : ProverData (ZMod p)) (fits) :
    (table rows data fits).interactionsWith readbackChannel.toRaw =
      (physical rows).map (fun r => readbackChannel.pulledIfValue r.active r.receipt) := by
  unfold table
  refine (Table.build_interactions _ _ _ _ _ _ _ _).trans ?_
  simp only [ReadbackSupply.receipt_values, Component.rowInput_buildRow]
  exact List.map_eq_flatMap.symm

private theorem versions (rows : List (ReadbackSupply.Inputs (ZMod p))) (data : ProverData (ZMod p)) (fits) :
    (table rows data fits).interactionsWith versionChannel.toRaw =
      (physical rows).map (fun r => versionChannel.emittedValue r.count r.version) := by
  unfold table
  refine (Table.build_interactions _ _ _ _ _ _ _ _).trans ?_
  simp only [ReadbackSupply.version_values, Component.rowInput_buildRow]
  exact List.map_eq_flatMap.symm

omit [Fact (2 ^ 25 < p)] in
private theorem balance_map {α : Type} (rows : List α) (make : α → Interaction (ZMod p)) (msg : Array (ZMod p)) :
    balanceOf (rows.map make) msg = (rows.map fun r => if (make r).msg = msg then (make r).signedMult else 0).sum := by
  induction rows with
  | nil => simp [balanceOf]
  | cons a rest ih =>
    by_cases same : (make a).msg = msg <;> simp [balanceOf_cons, ih, same]

omit [Fact (2 ^ 25 < p)] in
private theorem counted {n : ℕ} (requests : List (Request n (ZMod p))) (encode : Fin n → Array (ZMod p)) (msg : Array (ZMod p)) :
    (∑ i, if encode i = msg then (count requests i : ZMod p) else 0) =
      ((requests.countP fun r => encode r.1 = msg : ℕ) : ZMod p) := by
  induction requests with
  | nil => simp [count]
  | cons r rest ih =>
    calc
      _ = (∑ i, if encode i = msg then (count rest i : ZMod p) else 0) +
          ∑ i, if i = r.1 then (if encode r.1 = msg then 1 else 0) else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        by_cases same : i = r.1
        · subst i
          by_cases hit : encode r.1 = msg <;> simp [count, hit]
        · by_cases hit : encode i = msg <;> simp [count, hit, same, Ne.symm same]
      _ = _ := by
        rw [ih]
        by_cases hit : encode r.1 = msg <;> simp [hit]

omit [Fact (2 ^ 25 < p)] in
private theorem balance_disabled (n : ℕ) (row : Interaction (ZMod p)) (zero : row.signedMult = 0) (msg : Array (ZMod p)) :
    balanceOf (List.replicate n row) msg = 0 := by
  induction n with
  | zero => simp [balanceOf]
  | succ n ih => simp [List.replicate_succ, balanceOf_cons, zero, ih]

/-- Exact field balance for every version payload, including duplicate read demands, zero
query counts on genuine sources, and both independently padded tables. -/
theorem version_balanced (records : List (Readback (ZMod p))) (requests : List (Request records.length (ZMod p)))
    (data probeData : ProverData (ZMod p)) (supplyFits probeFits) :
    LogUpBalanced ((table (allocated records requests) data supplyFits).interactionsWith versionChannel.toRaw ++
      (WriteProbe.table (probes records requests) probeData probeFits).interactionsWith versionChannel.toRaw) := by
  let version (i : Fin records.length) := (ReadbackSupply.populate records[i] 0).version
  let encode (i : Fin records.length) := (toElements (version i)).toArray
  intro msg
  rw [balanceOf_append, versions, table_versions]
  simp only [physical, physicalInputs, List.map_append, List.flatMap_append, ← List.map_eq_flatMap, List.map_replicate,
    List.map_map, Function.comp_def, balanceOf_append]
  rw [balance_disabled _ _ (by rfl), balance_disabled _ _ (by simp [Channel.pulledIfValue, Interaction.signedMult]), add_zero, add_zero]
  have pushed : balanceOf ((allocated records requests).map (fun r => versionChannel.emittedValue r.count r.version)) msg =
      ((requests.countP fun r => encode r.1 = msg : ℕ) : ZMod p) := by
    rw [balance_map, allocated_eq, List.map_ofFn, List.sum_ofFn]
    exact counted requests encode msg
  rw [pushed]
  have pulled := FieldClosure.balanceOf_unitPulls (fun r : Request records.length (ZMod p) => encode r.1)
    (fun r => versionChannel.pulledIfValue 1 (version r.1)) (fun _ => rfl) (fun _ => rfl) requests msg
  simp only [probes_eq, List.map_map, Function.comp_def]
  change _ + balanceOf (requests.map (fun r => versionChannel.pulledIfValue 1 (version r.1))) msg = _
  rw [show balanceOf (requests.map (fun r => versionChannel.pulledIfValue 1 (version r.1))) msg = _ from pulled]
  exact add_neg_cancel _

/-- Original clocks fit the 24-bit limbs used by the registered supply component. -/
def Bounded (r : Readback (ZMod p)) : Prop :=
  r.previousHigh.val < 2 ^ 24 ∧ r.previousLow.val < 2 ^ 24 ∧ r.currentHigh.val < 2 ^ 24 ∧ r.currentLow.val < 2 ^ 24

private theorem allocated_inputs (records : List (Readback (ZMod p))) (requests : List (Request records.length (ZMod p)))
    (bounded : ∀ r ∈ records, Bounded r) :
    (∀ input ∈ allocated records requests, ReadbackSupply.Valid input) ∧
      (allocated records requests).map (fun input => readbackChannel.pulledIfValue input.active input.receipt) =
        records.map (fun r => readbackChannel.pulledIfValue 1 r) := by
  have full (i : Fin records.length) := by
    obtain ⟨ph, pl, ch, cl⟩ := bounded records[i] (List.getElem_mem ..)
    exact ReadbackSupply.populate_valid records[i] (count requests i) ph pl ch cl
  constructor
  · intro input member
    rw [allocated_eq] at member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    exact (full i).1
  · rw [allocated_eq, List.map_ofFn, ← List.ofFn_getElem (xs := records.map _)]
    apply List.ext_getElem
    · simp
    · intro i h h'
      simp only [List.getElem_ofFn, List.getElem_map]
      exact congrArg (readbackChannel.pulledIfValue 1) (full ⟨i, by simpa using h⟩).2

private theorem receipt_tally (rows : List (ZMod p × Readback (ZMod p)))
    (binary : ∀ r ∈ rows, r.1 = 0 ∨ r.1 = 1) (msg : Array (ZMod p)) :
    balanceOf ((live rows).map (fun r => readbackChannel.pulledIfValue 1 r)) msg +
      balanceOf (rows.map (fun r => readbackChannel.pushedIfValue r.1 r.2)) msg = 0 := by
  induction rows with
  | nil => simp [live, balanceOf]
  | cons r rest ih =>
    have tail := ih (fun x hx => binary x (List.mem_cons_of_mem _ hx))
    rcases binary r List.mem_cons_self with off | on
    · simpa [live, off, balanceOf_cons, Channel.pushedIfValue, Interaction.signedMult] using tail
    · simp only [live, List.filter_cons, on, decide_true, ↓reduceIte, List.map_cons, balanceOf_cons,
        Channel.pushedIfValue, Channel.pulledIfValue, Interaction.signedMult] at tail ⊢
      split <;> linear_combination tail

/-- The installed source ledger balances on the first bus. Every original occurrence stays
in the physical count, while only live rows cause the scheduler to allocate a supply row. -/
theorem readback_balanced (raw : AccessInventory.Source → Table (ZMod p))
    (registered : ∀ id, (raw id).component = AccessInventory.original id)
    (requests : List (Request (live (AccessInventory.records raw)).length (ZMod p)))
    (sourceChecked : ∀ id, (raw id).Constraints)
    (bounded : ∀ r ∈ live (AccessInventory.records raw), Bounded r)
    (data : ProverData (ZMod p)) (fits) :
    let supply := table (allocated (live (AccessInventory.records raw)) requests) data fits
    supply.Constraints ∧ supply.Guarantees ∧ LogUpBalanced (AccessInventory.ledger raw registered supply) := by
  obtain ⟨valid, preserved⟩ := allocated_inputs _ requests bounded
  exact ⟨(table_complete _ valid data fits).1, (table_complete _ valid data fits).2, by
    intro msg
    rw [AccessInventory.ledger_records, balanceOf_append, receipts]
    simp only [physical, List.map_append, List.map_replicate, balanceOf_append, preserved]
    rw [balance_disabled _ _ (by simp [padding, Channel.pulledIfValue, Interaction.signedMult]), add_zero]
    exact receipt_tally _ (AccessInventory.records_binary raw registered sourceChecked) msg⟩

end SP1Clean.WriteProbe.Counted
