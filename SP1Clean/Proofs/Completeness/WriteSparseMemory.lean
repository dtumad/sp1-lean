import SP1Clean.Proofs.Completeness.WriteSparseInitializers
import ToClean.Air.GuardedLedger

/-! # Raw Memory receipts for generated sparse snapshot and finalizer rows

A positive source row is decoded at its actual physical table data. The snapshot and
canonical address uniquely determine its full zero-time Memory message. Thus the
incoming and outgoing occurrences for every extra key agree in every field.
-/

namespace SP1Clean.WriteProbe.SparseBoundary

open Circuit Air.Flat Semantics Channels TraceGen Soundness

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
private theorem same_snapshot {snapshot : MemorySnapshot} {key : ℕ} {l r : MemoryMsg (ZMod p)}
    (left : MemoryBoundary.SnapshotAtSpec snapshot key l) (right : MemoryBoundary.SnapshotAtSpec snapshot key r) : l = r := by
  have loc := MemLoc.busAddress_injective_of_canonical left.1.canonical.1 right.1.canonical.1
    (left.1.canonical.2.2.symm.trans (left.2.trans (right.2.symm.trans right.1.canonical.2.2)))
  have word := Word.eq_of_toBitVec64_eq left.1.1 right.1.1
    (left.1.2.2.2.2.1.symm.trans ((congrArg snapshot.read loc).trans right.1.2.2.2.2.1))
  have keyEq := Word.eq_of_toBitVec64_eq left.1.canonical.2.1 right.1.canonical.2.1
    (congrArg (BitVec.ofNat 64) (left.2.trans right.2.symm))
  have hl := left.1.2.2.1
  have hr := right.1.2.2.1
  change l.clk_high.val * 2 ^ 24 + l.clk_low.val = 0 at hl
  change r.clk_high.val * 2 ^ 24 + r.clk_low.val = 0 at hr
  have hi : l.clk_high = r.clk_high := ZMod.val_injective _ (by omega)
  have lo : l.clk_low = r.clk_low := ZMod.val_injective _ (by omega)
  cases l
  cases r
  exact MemoryMsg.mk.injEq .. |>.mpr ⟨hi, lo, congrArg (fun w : Word (ZMod p) => w[0]) keyEq,
    congrArg (fun w : Word (ZMod p) => w[1]) keyEq, congrArg (fun w : Word (ZMod p) => w[2]) keyEq, word⟩

/-- The initial record at a finalizer's key uses zero local time and the authentic source
snapshot value. The original three address limbs are preserved exactly. -/
def genesis (snapshot : MemorySnapshot) (r : Terminal (ZMod p)) : MemoryMsg (ZMod p) :=
  { r.record with clk_high := 0, clk_low := 0, value := Target.bitVecToWord (snapshot.read (MemoryMsg.locOf r.record)) }

private theorem genesis_spec (snapshot : MemorySnapshot) (r : Terminal (ZMod p)) (valid : r.Valid) :
    MemoryBoundary.SnapshotAtSpec snapshot r.key (genesis snapshot r) := by
  have canonical : MemoryBoundary.CanonicalSpec r.record := by
    have d := valid.2.2.2
    cases tag : r.ram <;> rw [tag] at d
    · change FinalRegisterProvider.Domain r.record at d
      exact FinalRegisterProvider.canonical _ d.1 d.2.1 d.2.2
    · change FinalRamProvider.Domain r.record at d
      have loc := MemoryBoundary.ram_location_of_key r.record _ d.2.1 d.2.2.1 d.2.2.2
        (by simp [MemoryBoundary.address, Word.toNat])
      exact ⟨loc.1, d.1, loc.2.1⟩
  exact ⟨⟨Target.isU64_bitVecToWord _, by simp [MemoryMsg.ClkBound, genesis], by simp [MemoryMsg.timeNat, clkNat, genesis],
    canonical.1, (Target.toBitVec64_bitVecToWord _).symm, canonical.2⟩, valid.1⟩

private def activeInput (snapshot : MemorySnapshot) (ram : Bool) (previous : ℕ) (r : Terminal (ZMod p)) :
    (source (p := p) snapshot ram).Input (ZMod p) :=
  match ram with
  | false => (initialInput snapshot false previous r, 1)
  | true => (initialInput snapshot true previous r, 1)

private theorem active_source (snapshot : MemorySnapshot) (ram : Bool) (previous : ℕ) (r : Terminal (ZMod p))
    (valid : r.Valid) (tag : r.ram = ram) (order : previous < r.key + 1)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    let c := source snapshot ram
    let input := activeInput snapshot ram previous r
    let env := Environment.fromArray (c.buildRow input data hint) data
    c.operations.interactionValuesWith memoryChannel.toRaw env = [memoryChannel.pushedValue (sourceRecord snapshot ram env)] ∧
      MemoryBoundary.SnapshotAtSpec snapshot r.key (sourceRecord snapshot ram env) := by
  let c := source (p := p) snapshot ram
  let input := activeInput snapshot ram previous r
  let env := Environment.fromArray (c.buildRow input data hint) data
  have honest : c.circuit.ProverAssumptions input data hint := by
    cases ram <;> exact initialInput_valid snapshot _ previous r valid tag order data hint
  have hd := c.rowInput_buildRow input data data hint
  have spec := (c.buildRow_spec_requirements input data hint honest (by cases ram <;> intro _ <;> trivial)).1
  change c.circuit.Spec (c.rowInput env) (c.rowOutput env) data at spec
  rw [hd] at spec
  have bound := valid.key_lt
  have decoded : Word.toNat (Target.bitVecToWord (p := p) (BitVec.ofNat 64 (r.key + 1))) = r.key + 1 := by
    rw [← Word.toBitVec64_toNat (Target.isU64_bitVecToWord _), Target.toBitVec64_bitVecToWord,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  cases ram
  case false =>
    have active : _ := congrArg (fun x : OrderedMemoryProvider.RowInput RegisterSnapshotRow (ZMod p) => x.2) hd
    have facts := spec.2 rfl
    refine ⟨source_live snapshot false env ((eval_gate env).trans active), facts.1, ?_⟩
    exact facts.1.canonical.2.2.trans (Nat.add_right_cancel (decoded.symm.trans facts.2.2)).symm
  case true =>
    have active : _ := congrArg (fun x : OrderedMemoryProvider.RowInput Word (ZMod p) => x.2) hd
    have facts := spec.2 rfl
    refine ⟨source_live snapshot true env ((eval_gate env).trans active), facts.1, ?_⟩
    exact facts.1.canonical.2.2.trans (Nat.add_right_cancel (decoded.symm.trans facts.2.2)).symm

private theorem active_publication (snapshot : MemorySnapshot) (ram : Bool) (previous : ℕ) (r : Terminal (ZMod p))
    (valid : r.Valid) (tag : r.ram = ram) (order : previous < r.key + 1)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    let c := source snapshot ram
    let input := activeInput snapshot ram previous r
    c.operations.interactionValuesWith memoryChannel.toRaw (Environment.fromArray (c.buildRow input data hint) data) =
      [memoryChannel.pushedValue (genesis snapshot r)] := by
  obtain ⟨actual, auth⟩ := active_source snapshot ram previous r valid tag order data hint
  rw [same_snapshot auth (genesis_spec snapshot r valid)] at actual
  exact actual

/-- Raw Memory interactions of an actual built incoming row at its physical private data. -/
noncomputable def initialValues (snapshot : MemorySnapshot) (ram : Bool) (data : ProverData (ZMod p))
    (row : OrderedMemoryProvider.RowInput (InitialPayload ram) (ZMod p)) : List (Interaction (ZMod p)) :=
  match ram with
  | false =>
    let c := source (p := p) snapshot false
    c.operations.interactionValuesWith memoryChannel.toRaw (Environment.fromArray (c.buildRow row data (.empty _)) data)
  | true =>
    let c := source (p := p) snapshot true
    c.operations.interactionValuesWith memoryChannel.toRaw (Environment.fromArray (c.buildRow row data (.empty _)) data)

private theorem initial_values_inactive (snapshot : MemorySnapshot) (ram : Bool) (data : ProverData (ZMod p)) (msg : Array (ZMod p)) :
    balanceOf (initialValues snapshot ram data 0) msg = 0 := by
  cases ram
  case false =>
    let c := source (p := p) snapshot false
    let z : OrderedMemoryProvider.RowInput (InitialPayload false) (ZMod p) := 0
    let env := Environment.fromArray (c.buildRow z data (.empty _)) data
    have gate := (eval_gate (Payload := RegisterSnapshotRow) env).trans
      (congrArg (fun row : OrderedMemoryProvider.RowInput RegisterSnapshotRow (ZMod p) => row.2) (c.rowInput_buildRow z data data (.empty _)))
    have ledger := source_with_weight snapshot false env 0 gate
    change balanceOf (c.operations.interactionValuesWith memoryChannel.toRaw env) msg = 0
    rw [ledger, balanceOf_cons]
    simp [balanceOf, Interaction.signedMult, Channel.pushedIfValue]
    exact ite_self 0
  case true =>
    let c := source (p := p) snapshot true
    let z : OrderedMemoryProvider.RowInput (InitialPayload true) (ZMod p) := 0
    let env := Environment.fromArray (c.buildRow z data (.empty _)) data
    have gate := (eval_gate (Payload := Word) env).trans
      (congrArg (fun row : OrderedMemoryProvider.RowInput Word (ZMod p) => row.2) (c.rowInput_buildRow z data data (.empty _)))
    have ledger := source_with_weight snapshot true env 0 gate
    change balanceOf (c.operations.interactionValuesWith memoryChannel.toRaw env) msg = 0
    rw [ledger, balanceOf_cons]
    simp [balanceOf, Interaction.signedMult, Channel.pushedIfValue]
    exact ite_self 0

/-- The exact raw signed Memory ledger of an incoming table includes the original zero-weight
padding and uses its genuine built row environments. -/
theorem initialTable_memory (snapshot : MemorySnapshot) (ram : Bool) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p)) (fit) :
    let table := initialTable snapshot ram rows data fit
    table.interactionsWith memoryChannel.toRaw =
      (WitnessGeneration.guardedRows (F := ZMod p) (orderedInputs ram (initialInput snapshot ram) 0 rows)).flatMap
        (initialValues snapshot ram table.data) := by
  cases ram
  · let c := source (p := p) snapshot false
    let inputs := orderedInputs false (initialInput snapshot false) 0 rows
    let padded := WitnessGeneration.guardedRows (F := ZMod p) inputs
    exact Table.build_interactions c padded (c.inputData padded data) (.empty _)
      ((WitnessGeneration.guardedRows_length inputs).trans_le ((orderedInputs_length false _ rows 0) ▸ fit)) trivial
      (c.inputData_consistent padded data) _
  · let c := source (p := p) snapshot true
    let inputs := orderedInputs true (initialInput snapshot true) 0 rows
    let padded := WitnessGeneration.guardedRows (F := ZMod p) inputs
    exact Table.build_interactions c padded (c.inputData padded data) (.empty _)
      ((WitnessGeneration.guardedRows_length inputs).trans_le ((orderedInputs_length true _ rows 0) ▸ fit)) trivial
      (c.inputData_consistent padded data) _

private theorem active_values (snapshot : MemorySnapshot) (ram : Bool) (rows : List (Terminal (ZMod p))) (previous : ℕ)
    (data : ProverData (ZMod p)) (ordered : rows.Pairwise (fun a b => a.key < b.key))
    (start : ∀ r ∈ rows, previous < r.key + 1) (valid : ∀ r ∈ rows, r.Valid) :
    (orderedInputs ram (initialInput snapshot ram) previous rows).flatMap (fun i => initialValues snapshot ram data (i, 1)) =
      (rows.filter (fun r => r.ram == ram)).map (fun r => memoryChannel.pushedValue (genesis snapshot r)) := by
  induction rows generalizing previous with
  | nil => rfl
  | cons first rest ih =>
    have order := List.pairwise_cons.mp ordered
    have tail := ih (first.key + 1) order.2 (fun r hr => Nat.succ_lt_succ (order.1 r hr)) (fun r hr => valid r (List.mem_cons_of_mem _ hr))
    by_cases tag : first.ram = ram
    · have emitted := active_publication snapshot ram previous first (valid first (List.mem_cons_self ..)) tag (start first (List.mem_cons_self ..)) data (.empty _)
      have atRow : initialValues snapshot ram data (initialInput snapshot ram previous first, 1) = [memoryChannel.pushedValue (genesis snapshot first)] := by
        cases ram <;> exact emitted
      simp [orderedInputs, tag, atRow, tail]
    · simp [orderedInputs, tag, tail, beq_iff_eq]

/-- Every distinct physical address owned by the incoming provider publishes its full canonical
zero-clock message exactly once, with disabled rows contributing zero to every field sum. -/
theorem initialTable_sum (snapshot : MemorySnapshot) (ram : Bool) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p)) (fit)
    (ordered : rows.Pairwise (fun a b => a.key < b.key)) (valid : ∀ r ∈ rows, r.Valid) (msg : Array (ZMod p)) :
    balanceOf ((initialTable snapshot ram rows data fit).interactionsWith memoryChannel.toRaw) msg =
      balanceOf ((rows.filter (fun r => r.ram == ram)).map (fun r => memoryChannel.pushedValue (genesis snapshot r))) msg := by
  rw [initialTable_memory]
  refine (WitnessGeneration.guardedRows_balanceOf _ _ msg (initial_values_inactive snapshot ram _ msg)).trans ?_
  rw [active_values snapshot ram rows 0 _ ordered (fun _ _ => Nat.zero_lt_succ _) valid]

/-- Exact raw Memory pulls of the original generated finalizer, including disabled physical
rows and their actual zero field multiplicities. -/
theorem finalTable_memory (ram : Bool) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p)) (fit) :
    (finalTable ram rows data fit).interactionsWith memoryChannel.toRaw =
      (WitnessGeneration.guardedRows (F := ZMod p) (finalInputs ram 0 rows)).map (fun row => memoryChannel.pulledIfValue row.2 row.1.payload) := by
  let c := originalFinal (p := p) ram
  let inputs := finalInputs ram 0 rows
  let padded := WitnessGeneration.guardedRows (F := ZMod p) inputs
  let emit := fun row : OrderedMemoryProvider.RowInput MemoryMsg (ZMod p) => memoryChannel.pulledIfValue row.2 row.1.payload
  have ledger := Table.ofInputs_ledger c padded data ((WitnessGeneration.guardedRows_length inputs).trans_le fit) (fun _ => trivial)
    memoryChannel.toRaw (fun row => [emit row]) (fun env => by
      rw [original_final_memory_values, finalRecordAt_eq]
      rfl)
  exact ledger.trans (List.map_eq_flatMap ..).symm

omit [Fact (2 ^ 25 < p)] in
private theorem final_payloads (ram : Bool) (previous : ℕ) (rows : List (Terminal (ZMod p))) :
    (finalInputs ram previous rows).map (·.payload) = (rows.filter (fun r => r.ram == ram)).map Terminal.record := by
  induction rows generalizing previous with
  | nil => rfl
  | cons first rest ih =>
    by_cases tag : first.ram = ram <;> simpa only [finalInputs, orderedInputs, List.filter_cons, beq_iff_eq, tag, ↓reduceIte,
      List.map_cons, List.cons.injEq, OrderedMemoryProvider.populate, true_and] using ih (first.key + 1)

/-- Each distinct final payload is consumed at unit field weight, with all padding preserved
by the raw table and contributing zero to the signed sum. -/
theorem finalTable_sum (ram : Bool) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p)) (fit) (msg : Array (ZMod p)) :
    balanceOf ((finalTable ram rows data fit).interactionsWith memoryChannel.toRaw) msg =
      balanceOf ((rows.filter (fun r => r.ram == ram)).map (fun r => memoryChannel.pulledValue r.record)) msg := by
  rw [finalTable_memory, WitnessGeneration.guarded_pull_sum, final_payloads]
  simp only [List.map_map, Function.comp_def]

private theorem extra_genesis (snapshot : MemorySnapshot) (touched requested : List ℕ) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (extra : Rows (ZMod p)) (member : extra ∈ buildAll snapshot touched requested data hint)
    (valid : (terminalOfRows snapshot data extra).Valid) : genesis snapshot (terminalOfRows snapshot data extra) = (terminalOfRows snapshot data extra).record := by
  obtain ⟨i, fresh, built⟩ := (mem_buildAll_iff ..).mp member
  obtain ⟨same, made, _, checked⟩ := build?_checked snapshot touched requested i fresh data hint
  obtain rfl := Option.some.inj (made.symm.trans built)
  exact same_snapshot (genesis_spec snapshot _ valid) checked.2.2.1

/-- The new sparse keys leave precisely the original touched-key contribution on Memory.
This is a per-message identity between the two actual tables, including every row and both
directions. It holds for every list of requests, including repeated and absent keys. -/
theorem sparse_memory_residual (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess) (requested : List ℕ)
    (guest : ∀ a ∈ stream, ∀ cell, a.loc = .ram cell → NativeLayout.guestMemory.Contains (MemLoc.ram cell).busAddress)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (ram : Bool) (msg : Array (ZMod p)) :
    let original := ((memoryFinalEntries stream).map (terminalOfEntry (p := p))).filter (fun r => r.ram == ram)
    let rows := terminals snapshot stream requested data hint
    let sourceTable := initialTable snapshot ram rows data (terminal_count_fit ram snapshot stream requested (canonical_addresses guest) data hint)
    let endTable := finalTable ram rows data (terminals_fit ram snapshot stream requested (canonical_addresses guest) data hint)
    balanceOf (sourceTable.interactionsWith memoryChannel.toRaw ++ endTable.interactionsWith memoryChannel.toRaw) msg =
      balanceOf (original.map (fun r => memoryChannel.pushedValue (genesis snapshot r)) ++
        original.map (fun r => memoryChannel.pulledValue r.record)) msg := by
  let touched := (memoryInitialEntries stream).map MemRecordEntry.addr
  let orig := (memoryFinalEntries stream).map (terminalOfEntry (p := p))
  let extras := (buildAll snapshot touched requested data hint).map (terminalOfRows snapshot data)
  let rows := terminals snapshot stream requested data hint
  let selected := fun r : Terminal (ZMod p) => r.ram == ram
  let push := fun r : Terminal (ZMod p) => memoryChannel.pushedValue (genesis snapshot r)
  let pull := fun r : Terminal (ZMod p) => memoryChannel.pulledValue r.record
  have sorted := terminals_ordered snapshot stream requested (canonical_addresses guest) data hint
  have valid := terminals_valid snapshot stream requested guest data hint
  have perm : rows.Perm (orig ++ extras) := List.mergeSort_perm _ _
  have paired : ((extras.filter selected).map (genesis snapshot)).Perm ((extras.filter selected).map Terminal.record) := by
    apply List.Perm.of_eq
    apply List.map_congr_left
    intro r present
    obtain ⟨extra, inside, rfl⟩ := List.mem_map.mp (List.mem_filter.mp present).1
    exact extra_genesis snapshot touched requested data hint extra inside
      (valid _ (perm.mem_iff.mpr (List.mem_append_right _ (List.mem_map_of_mem inside))))
  have closed := (memoryChannel (p := p)).logUp_unit_of_perm paired msg
  rw [balanceOf_append, List.map_map, List.map_map] at closed
  change balanceOf ((extras.filter selected).map push) msg + balanceOf ((extras.filter selected).map pull) msg = 0 at closed
  dsimp only
  rw [balanceOf_append, initialTable_sum snapshot ram _ data _ sorted valid, finalTable_sum, balanceOf_append]
  change balanceOf ((rows.filter selected).map push) msg + balanceOf ((rows.filter selected).map pull) msg =
    balanceOf ((orig.filter selected).map push) msg + balanceOf ((orig.filter selected).map pull) msg
  rw [balanceOf_perm ((perm.filter selected).map push), balanceOf_perm ((perm.filter selected).map pull)]
  simp only [List.filter_append, List.map_append, balanceOf_append]
  calc
    _ = (balanceOf ((orig.filter selected).map push) msg + balanceOf ((orig.filter selected).map pull) msg) +
        (balanceOf ((extras.filter selected).map push) msg + balanceOf ((extras.filter selected).map pull) msg) := by ac_rfl
    _ = _ := by rw [closed, add_zero]

end SP1Clean.WriteProbe.SparseBoundary
