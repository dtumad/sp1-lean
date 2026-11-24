import SP1Clean.Proofs.Completeness.WriteSparseFinalizers

/-! # Snapshot tables for the complete ordered Memory address inventory

The actual register and RAM snapshot components receive every touched key and every
additional valid WRITE query. Both use the same predecessor sequence and exact per-family
active count as the two finalizers. The only snapshot input carried by a RAM row is its
address; bytes are read by the original bundled circuit.
-/

namespace SP1Clean.WriteProbe.SparseBoundary

open Circuit Air.Flat Semantics TraceGen Channels Soundness

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
private theorem register_key {r : Terminal (ZMod p)} (valid : r.Valid) (tag : r.ram = false) : r.key < 32 := by
  have d := valid.2.2.2
  rw [tag] at d
  change FinalRegisterProvider.Domain r.record at d
  rw [← valid.1]
  simpa [MemoryBoundary.address, Word.toNat, d.2.1, d.2.2] using d.1

omit [Fact (2 ^ 25 < p)] in
private theorem ram_key {r : Terminal (ZMod p)} (valid : r.Valid) (tag : r.ram = true) :
    2 ^ 16 ≤ r.key ∧ r.key < 2 ^ 48 ∧ r.key % 8 = 0 := by
  have d := valid.2.2.2
  rw [tag] at d
  change FinalRamProvider.Domain r.record at d
  exact valid.1 ▸ d.2

/-- Payload queried by the original snapshot provider in each address space. -/
def InitialPayload (ram : Bool) : TypeMap := if ram then Word else RegisterSnapshotRow

instance (ram : Bool) : ProvableType (InitialPayload ram) := by cases ram <;> dsimp [InitialPayload] <;> infer_instance

/-- Select the snapshot register word or encode the exact RAM byte address at a given ordered
cursor. Both branches feed the ordinary snapshot circuit. -/
def initialInput (snapshot : MemorySnapshot) (ram : Bool) (previous : ℕ) (r : Terminal (ZMod p)) :
    OrderedMemoryProvider.Inputs (InitialPayload ram) (ZMod p) :=
  match ram with
  | false => (OrderedMemoryProvider.populate (SnapshotRegisterProvider.populate (p := p) snapshot (BitVec.ofNat 5 r.key)) previous r.key).1
  | true => (OrderedMemoryProvider.populate (Target.bitVecToWord (BitVec.ofNat 64 r.key)) previous r.key).1

theorem initialInput_valid (snapshot : MemorySnapshot) (ram : Bool) (previous : ℕ) (r : Terminal (ZMod p))
    (valid : r.Valid) (tag : r.ram = ram) (ordered : previous < r.key + 1)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    match ram with
    | false => (source snapshot false).circuit.ProverAssumptions (initialInput snapshot false previous r, 1) data hint
    | true => (source snapshot true).circuit.ProverAssumptions (initialInput snapshot true previous r, 1) data hint := by
  cases ram
  · have small := register_key valid tag
    have key : (BitVec.ofNat 5 r.key).toNat = r.key := Nat.mod_eq_of_lt small
    have ready := OrderedSnapshotProvider.populateRegister_assumptions (p := p) SnapshotMemoryEnsemble.channelName snapshot
      (BitVec.ofNat 5 r.key) previous (by rw [key]; exact ordered) data hint
    rw [key] at ready
    exact ready
  · have ⟨lower, upper, aligned⟩ := ram_key valid tag
    apply OrderedSnapshotProvider.populateRam?_sound SnapshotMemoryEnsemble.channelName snapshot previous r.key _ _ data hint
    simp [OrderedSnapshotProvider.populateRam?, ordered, SnapshotRamProvider.populate?, aligned,
      InitialMemoryRead.populate?, initialInput, OrderedMemoryProvider.populate]
    omega

/-- Generate the two original snapshot tables at their actual guarded demand heights. -/
def initialTable (snapshot : MemorySnapshot) (ram : Bool) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p))
    (fit : WitnessGeneration.demandHeight (rows.filter (fun r => r.ram == ram)).length ≤ UInt64.size) : Table (ZMod p) :=
  match ram with
  | false =>
    let inputs := orderedInputs false (initialInput snapshot false) 0 rows
    Table.ofInputs (source snapshot false) (WitnessGeneration.guardedRows inputs) data
      ((WitnessGeneration.guardedRows_length inputs).trans_le ((orderedInputs_length false _ rows 0) ▸ fit)) (fun _ => trivial)
  | true =>
    let inputs := orderedInputs true (initialInput snapshot true) 0 rows
    Table.ofInputs (source snapshot true) (WitnessGeneration.guardedRows inputs) data
      ((WitnessGeneration.guardedRows_length inputs).trans_le ((orderedInputs_length true _ rows 0) ▸ fit)) (fun _ => trivial)

/-- All generated rows satisfy the original snapshot-provider constraints and channel
guarantees, at their canonical private input data. -/
theorem initialTable_valid (snapshot : MemorySnapshot) (ram : Bool) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p)) (fit)
    (ordered : rows.Pairwise (fun a b => a.key < b.key)) (valid : ∀ r ∈ rows, r.Valid) :
    (initialTable snapshot ram rows data fit).Constraints ∧ (initialTable snapshot ram rows data fit).Guarantees := by
  cases ram <;> unfold initialTable <;> apply Table.ofInputs_valid <;> intro row member
  all_goals
    rcases List.mem_append.mp member with active | pad
    · obtain ⟨input, inside, rfl⟩ := List.mem_map.mp active
      first
      | refine orderedInputs_all false _ rows 0 (fun i => (source (p := p) snapshot false).circuit.ProverAssumptions (i, 1) _ _)
          ordered (fun _ _ => Nat.zero_lt_succ _) ?_ input inside
      | refine orderedInputs_all true _ rows 0 (fun i => (source (p := p) snapshot true).circuit.ProverAssumptions (i, 1) _ _)
          ordered (fun _ _ => Nat.zero_lt_succ _) ?_ input inside
      intro r hr tag previous before
      exact initialInput_valid snapshot _ previous r (valid r hr) tag before _ _
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp pad
      exact ⟨Or.inl rfl, fun h => (zero_ne_one h).elim⟩

/-- Each incoming table has the same genuine active count and demand height as its finalizer. -/
theorem initialTable_length (snapshot : MemorySnapshot) (ram : Bool) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p)) (fit) :
    (initialTable snapshot ram rows data fit).table.length = WitnessGeneration.demandHeight (rows.filter (fun r => r.ram == ram)).length := by
  cases ram
  · refine (Table.ofInputs_length (source snapshot false) _ data _ (fun _ => trivial)).trans ?_
    exact (WitnessGeneration.guardedRows_length (F := ZMod p) (orderedInputs false (initialInput snapshot false) 0 rows)).trans
      (congrArg WitnessGeneration.demandHeight (orderedInputs_length false _ rows 0))
  · refine (Table.ofInputs_length (source snapshot true) _ data _ (fun _ => trivial)).trans ?_
    exact (WitnessGeneration.guardedRows_length (F := ZMod p) (orderedInputs true (initialInput snapshot true) 0 rows)).trans
      (congrArg WitnessGeneration.demandHeight (orderedInputs_length true _ rows 0))

/-- Compile the source and final register/RAM tables from their common genuine address
inventory. Heights are fixed by physical counts, including on the empty Memory history. -/
theorem compiled_boundaries_valid (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess) (requested : List ℕ)
    (guest : ∀ a ∈ stream, ∀ cell, a.loc = .ram cell → NativeLayout.guestMemory.Contains (MemLoc.ram cell).busAddress)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (ram : Bool) :
    let rows := terminals snapshot stream requested data hint
    let initial := initialTable snapshot ram rows data (terminal_count_fit ram snapshot stream requested (canonical_addresses guest) data hint)
    let final := finalTable ram rows data (terminals_fit ram snapshot stream requested (canonical_addresses guest) data hint)
    initial.Constraints ∧ initial.Guarantees ∧ final.Constraints ∧ final.Guarantees ∧ initial.table.length = final.table.length := by
  have ordered := terminals_ordered snapshot stream requested (canonical_addresses guest) data hint
  have valid := terminals_valid snapshot stream requested guest data hint
  have start := initialTable_valid snapshot ram _ data (terminal_count_fit ram snapshot stream requested (canonical_addresses guest) data hint) ordered valid
  have endRows := finalTable_valid ram _ data (terminals_fit ram snapshot stream requested (canonical_addresses guest) data hint) ordered valid
  exact ⟨start.1, start.2, endRows.1, endRows.2, (initialTable_length ..).trans (finalTable_length ..).symm⟩

end SP1Clean.WriteProbe.SparseBoundary
