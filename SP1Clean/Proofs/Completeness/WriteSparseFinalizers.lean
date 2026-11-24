import SP1Clean.Proofs.Completeness.WriteSourceCoverage
import SP1Clean.Proofs.Completeness.WriteCountedCost

/-! # Compiling untouched WRITE keys into the original Memory finalizers

Sort the touched terminal records together with the authentic additional zero-time snapshot
records. The register and RAM tables then draw from the same strictly ordered key inventory
and carry its actual predecessor cursors. Every selected physical input is published at unit
multiplicity by the ordinary source registry, before any probe-routing choice is made.
-/

namespace SP1Clean.WriteProbe.SparseBoundary

open Circuit Air.Flat Semantics TraceGen Channels WriteProbe.AccessInventory

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Complete payload and owning original register/RAM finalizer at an ordered key. -/
structure Terminal (F : Type) where
  /-- Byte address used by the two original ordered providers. -/
  key : ℕ
  /-- The shared Memory address space selects the register or RAM finalizer. -/
  ram : Bool
  /-- Complete final Memory message, including its true last update clock. -/
  record : MemoryMsg F

/-- A chronological history supplies its last pushed record. -/
def terminalOfEntry (e : MemRecordEntry) : Terminal (ZMod p) :=
  ⟨e.addr, decide (32 ≤ e.addr), e.toMemoryMsg⟩

/-- A new sparse key contributes the record output by its own original snapshot row. -/
def terminalOfRows (snapshot : MemorySnapshot) (data : ProverData (ZMod p)) (r : Rows (ZMod p)) : Terminal (ZMod p) :=
  ⟨r.key, r.ram, sourceRecord snapshot r.ram (Environment.fromArray r.initial data)⟩

/-- Sort terminal payloads once by physical address. Duplicate WRITE reads at an otherwise
untouched key have already collapsed to one authentic boundary pair in `buildAll`. -/
def terminals (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess) (requested : List ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : List (Terminal (ZMod p)) :=
  let touched := memoryFinalEntries stream
  let extras := buildAll snapshot ((memoryInitialEntries stream).map MemRecordEntry.addr) requested data hint
  (touched.map terminalOfEntry ++ extras.map (terminalOfRows snapshot data)).mergeSort (fun a b => a.key ≤ b.key)

/-- The generated finalizer payloads enumerate exactly the strictly ordered union of the
existing Memory addresses and the supported queried addresses. -/
theorem terminals_keys (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess) (requested : List ℕ)
    (canonical : MemoryAddressesCanonical stream) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (terminals snapshot stream requested data hint).map Terminal.key =
      keys ((memoryInitialEntries stream).map MemRecordEntry.addr) requested := by
  let touched := (memoryInitialEntries stream).map MemRecordEntry.addr
  let ks := keys touched requested
  let extras := buildAll snapshot touched requested data hint
  let unsorted := (memoryFinalEntries stream).map (terminalOfEntry (p := p)) ++ extras.map (terminalOfRows snapshot data)
  let le := fun (a b : Terminal (ZMod p)) => decide (a.key ≤ b.key)
  have same : (memoryFinalEntries stream).map MemRecordEntry.addr = touched := by
    change (memoryFinalEntries stream).map MemRecordEntry.addr = (memoryInitialEntries stream).map MemRecordEntry.addr
    rw [memoryFinalEntries_addresses, memoryInitialEntries_addresses]
  have extraKeys := buildAll_keys snapshot touched requested data hint
  have addresses : unsorted.map Terminal.key = touched ++ ks.filter (fun k => !touched.contains k) := by
    rw [List.map_append, List.map_map, List.map_map]
    change (memoryFinalEntries stream).map MemRecordEntry.addr ++ extras.map Rows.key = _
    rw [same, extraKeys]
  have perm := (List.mergeSort_perm unsorted le).map Terminal.key
  rw [addresses] at perm
  have sorted : ((unsorted.mergeSort le).map Terminal.key).SortedLE := by
    apply List.Pairwise.sortedLE
    apply List.pairwise_map.mpr
    have result := List.pairwise_mergeSort (le := le)
      (by intro a b c ab bc; exact decide_eq_true (le_trans (of_decide_eq_true ab) (of_decide_eq_true bc)))
      (by intro a b; simpa only [le, Bool.or_eq_true, decide_eq_true_eq] using Nat.le_total a.key b.key) unsorted
    simpa only [le, decide_eq_true_eq] using result
  apply List.Perm.eq_of_sortedLE sorted (ordered_keys touched requested).sortedLE
  apply perm.trans
  have unique : (touched ++ ks.filter (fun k => !touched.contains k)).Nodup := by
    refine List.nodup_append.mpr ⟨memoryInitialEntries_addresses_nodup canonical, (ordered_keys touched requested).nodup.filter _, ?_⟩
    intro a ha b hb eq
    subst b
    exact (by simpa using (List.mem_filter.mp hb).2 : a ∉ touched) ha
  apply (List.perm_ext_iff_of_nodup unique (ordered_keys touched requested).nodup).mpr
  intro k
  by_cases used : k ∈ touched
  · simpa [used] using (mem_keys.mpr (Or.inl used) : k ∈ ks)
  · simp [used, ks]

/-- The original finalizer requires a canonical payload in its own address space. -/
def Terminal.Valid (r : Terminal (ZMod p)) : Prop :=
  Word.toNat (MemoryBoundary.address r.record) = r.key ∧ MemoryMsg.isU64 r.record ∧
    MemoryMsg.ClkBound r.record ∧ (if r.ram then FinalRamProvider.Domain r.record else FinalRegisterProvider.Domain r.record)

omit [Fact (2 ^ 25 < p)] in
/-- A valid original register or RAM payload fits the 48-bit native physical address space. -/
theorem Terminal.Valid.key_lt {r : Terminal (ZMod p)} (valid : r.Valid) : r.key < 2 ^ 48 := by
  rw [← valid.1]
  have d := valid.2.2.2
  cases tag : r.ram <;> rw [tag] at d
  · change FinalRegisterProvider.Domain r.record at d
    have canonical := FinalRegisterProvider.canonical _ d.1 d.2.1 d.2.2
    rw [canonical.2.2]
    exact MemLoc.busAddress_lt_two_pow_48 canonical.1
  · change FinalRamProvider.Domain r.record at d
    exact d.2.2.1

omit [Fact (2 ^ 25 < p)] in
private theorem register_of_small {record : MemoryMsg (ZMod p)} (small : Word.toNat (MemoryBoundary.address record) < 32) :
    FinalRegisterProvider.Domain record := by
  simp only [MemoryBoundary.address, Word.toNat, circuit_norm, ZMod.val_zero, zero_mul, add_zero] at small
  refine ⟨by omega, ZMod.val_injective _ ?_, ZMod.val_injective _ ?_⟩ <;> simp only [ZMod.val_zero] <;> omega

private theorem entry_valid (entry : MemRecordEntry)
    (legal : entry.addr < 32 ∨ 2 ^ 16 ≤ entry.addr ∧ entry.addr < 2 ^ 48 ∧ entry.addr % 8 = 0) :
    (terminalOfEntry (p := p) entry).Valid := by
  let msg := entry.toMemoryMsg (p := p)
  have bound : entry.addr < 2 ^ 48 := by rcases legal with h | ⟨_, h, _⟩ <;> omega
  have packed : Word.toNat (MemoryBoundary.address msg) = entry.addr := by
    calc
      _ = Address.toNat (Address.ofNat (p := p) entry.addr) := by
        simp [msg, MemRecordEntry.toMemoryMsg, Address.toNat, Address.ofNat, MemoryBoundary.address, Word.toNat]
      _ = _ := Address.toNat_ofNat _ bound
  have clk : MemoryMsg.ClkBound msg := by
    change ((entry.clk % 2 ^ 24 : ℕ) : ZMod p).val < 2 ^ 24
    exact val_natCast_lt (Nat.mod_lt _ (by decide)) le_rfl
  refine ⟨packed, wordOfNat_isU64 _, clk, ?_⟩
  change if decide (32 ≤ entry.addr) then FinalRamProvider.Domain msg else FinalRegisterProvider.Domain msg
  rcases legal with small | ram
  · simp only [show ¬32 ≤ entry.addr by omega, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact register_of_small (packed ▸ small)
  · simp only [show 32 ≤ entry.addr by omega, decide_true, ↓reduceIte]
    unfold FinalRamProvider.Domain
    rw [packed]
    have bounded := Address.bounded_ofNat (p := p) entry.addr
    exact ⟨Word.isU64_of_cases (bounded 0) (bounded 1) (bounded 2) (by simp [MemoryBoundary.address]), ram⟩

private theorem extra_valid (snapshot : MemorySnapshot) (touched requested : List ℕ) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (rows : Rows (ZMod p)) (member : rows ∈ buildAll snapshot touched requested data hint) :
    (terminalOfRows snapshot data rows).Valid := by
  obtain ⟨i, fresh, made⟩ := (mem_buildAll_iff ..).mp member
  obtain ⟨other, also, key, checked⟩ := build?_checked snapshot touched requested i fresh data hint
  obtain rfl := Option.some.inj (also.symm.trans made)
  have legal := ((mem_keys.mp (List.getElem_mem i.isLt)).resolve_left fresh).2
  rw [← key] at legal
  have tag : other.ram = decide (other.key ≠ 12) := by
    obtain ⟨input, _, rfl⟩ := Option.map_eq_some_iff.mp made
    rfl
  have actual := checked.2.2.1
  refine ⟨actual.2, actual.1.1, actual.1.2.1, ?_⟩
  change if other.ram then FinalRamProvider.Domain _ else FinalRegisterProvider.Domain _
  rw [tag]
  rcases legal with reg | ram
  · simp only [reg, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact register_of_small (lt_of_eq_of_lt actual.2 (reg ▸ (by decide : 12 < 32)))
  · have nonreg : other.key ≠ 12 := by omega
    rw [show decide (other.key ≠ 12) = true from decide_eq_true nonreg]
    exact ⟨actual.1.canonical.2.1, actual.2 ▸ ram⟩

private theorem inputs_valid {r : Terminal (ZMod p)} (valid : r.Valid) (previous : ℕ) (ordered : previous < r.key + 1)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (originalFinal r.ram).circuit.ProverAssumptions (OrderedMemoryProvider.populate r.record previous r.key) data hint := by
  obtain ⟨key, word, clock, domain⟩ := valid
  rw [← key] at ordered ⊢
  cases tag : r.ram
  · rw [tag] at domain
    change FinalRegisterProvider.Domain r.record at domain
    apply OrderedFinalProvider.populateRegister?_sound previous r.record _ _ data hint
    exact ite_eq_left ⟨⟨domain, word, clock⟩, ordered⟩
  · rw [tag] at domain
    change FinalRamProvider.Domain r.record at domain
    apply OrderedFinalProvider.populateRam?_sound previous r.record _ _ data hint
    exact ite_eq_left ⟨⟨domain, word, clock⟩, ordered⟩

/-- Walk the shared ordered key inventory for either pair of register/RAM boundary components.
Every key advances the predecessor even when its row belongs to the other table. -/
def orderedInputs {I F : Type} (ram : Bool) (input : ℕ → Terminal F → I) (previous : ℕ) : List (Terminal F) → List I
  | [] => []
  | row :: rest =>
    let tail := orderedInputs ram input (row.key + 1) rest
    if row.ram = ram then input previous row :: tail else tail

theorem orderedInputs_member {I F : Type} (input : ℕ → Terminal F → I) {row : Terminal F}
    {rows : List (Terminal F)} (member : row ∈ rows) (previous : ℕ) :
    ∃ prev, input prev row ∈ orderedInputs row.ram input previous rows := by
  induction rows generalizing previous with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨previous, by simp [orderedInputs]⟩
    · obtain ⟨prev, inside⟩ := ih later (first.key + 1)
      refine ⟨prev, ?_⟩
      unfold orderedInputs
      split
      · exact List.mem_cons_of_mem _ inside
      · exact inside

theorem orderedInputs_all {I F : Type} (ram : Bool) (input : ℕ → Terminal F → I)
    (rows : List (Terminal F)) (previous : ℕ) (P : I → Prop)
    (ordered : rows.Pairwise (fun a b => a.key < b.key)) (start : ∀ r ∈ rows, previous < r.key + 1)
    (point : ∀ r ∈ rows, r.ram = ram → ∀ prev < r.key + 1, P (input prev r)) :
    ∀ i ∈ orderedInputs ram input previous rows, P i := by
  induction rows generalizing previous with
  | nil => simp [orderedInputs]
  | cons first rest ih =>
    have order := List.pairwise_cons.mp ordered
    have tail := ih (first.key + 1) order.2 (fun r hr => Nat.succ_lt_succ (order.1 r hr))
      (fun r hr => point r (List.mem_cons_of_mem _ hr))
    intro i inside
    unfold orderedInputs at inside
    split at inside
    next same =>
      rcases List.mem_cons.mp inside with rfl | found
      · exact point first (List.mem_cons_self ..) same previous (start first (List.mem_cons_self ..))
      · exact tail i found
    next => exact tail i inside

theorem orderedInputs_length {I F : Type} (ram : Bool) (input : ℕ → Terminal F → I)
    (rows : List (Terminal F)) (previous : ℕ) :
    (orderedInputs ram input previous rows).length = (rows.filter (fun r => r.ram == ram)).length := by
  induction rows generalizing previous with
  | nil => rfl
  | cons first rest ih =>
    by_cases tag : first.ram = ram <;> simp [orderedInputs, tag, ih, beq_iff_eq]

/-- Active inputs for the original finalizer carry the full terminal record at each key. -/
def finalInputs (ram : Bool) (previous : ℕ) (rows : List (Terminal (ZMod p))) :
    List (OrderedMemoryProvider.Inputs MemoryMsg (ZMod p)) :=
  orderedInputs ram (fun prev r => (OrderedMemoryProvider.populate r.record prev r.key).1) previous rows

/-- Build the actual original table, including its genuine physical padding. -/
def finalTable (ram : Bool) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p))
    (fit : WitnessGeneration.demandHeight (finalInputs ram 0 rows).length ≤ UInt64.size) : Table (ZMod p) :=
  let inputs := finalInputs ram 0 rows
  Table.ofInputs (originalFinal ram) (WitnessGeneration.guardedRows inputs) data
    ((WitnessGeneration.guardedRows_length inputs).trans_le fit) (fun _ => trivial)

/-- Both ordinary table constraints and their exported guarantees hold for each generated
register/RAM finalizer. The only input conditions here are the original terminal payload
semantics and their strictly increasing keys. -/
theorem finalTable_valid (ram : Bool) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p)) (fit)
    (ordered : rows.Pairwise (fun a b => a.key < b.key)) (valid : ∀ r ∈ rows, r.Valid) :
    (finalTable ram rows data fit).Constraints ∧ (finalTable ram rows data fit).Guarantees := by
  unfold finalTable
  apply Table.ofInputs_valid
  intro row member
  rcases List.mem_append.mp member with active | padding
  · obtain ⟨input, inside, rfl⟩ := List.mem_map.mp active
    refine orderedInputs_all ram _ rows 0 (fun i => (originalFinal ram).circuit.ProverAssumptions (i, 1) _ _)
      ordered (fun _ _ => Nat.zero_lt_succ _) ?_ input inside
    intro r hr same prev before
    subst ram
    exact inputs_valid (valid r hr) prev before _ _
  · obtain ⟨_, rfl⟩ := List.mem_replicate.mp padding
    cases ram <;> exact ⟨Or.inl rfl, fun h => (zero_ne_one h).elim⟩

/-- The two active counts partition the ordered address union by finalizer, and each actual
table pays exactly Clean's required padding at its own active count. -/
theorem finalTable_length (ram : Bool) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p)) (fit) :
    (finalTable ram rows data fit).table.length = WitnessGeneration.demandHeight (rows.filter (fun r => r.ram == ram)).length := by
  refine (Table.ofInputs_length (originalFinal ram) _ data _ (fun _ => trivial)).trans ?_
  exact (WitnessGeneration.guardedRows_length (F := ZMod p) (finalInputs ram 0 rows)).trans
    (congrArg WitnessGeneration.demandHeight (orderedInputs_length ram _ rows 0))

/-- Every physically representable touched key and every extra key is below the native 48-bit
address limit, which bounds the number of active original finalizer rows. -/
theorem terminal_count_bound (ram : Bool) (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess) (requested : List ℕ)
    (canonical : MemoryAddressesCanonical stream) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ((terminals snapshot stream requested data hint).filter (fun r => r.ram == ram)).length ≤ 2 ^ 48 := by
  let touched := (memoryInitialEntries stream).map MemRecordEntry.addr
  let ks := keys touched requested
  have bound : ks.toFinset ⊆ Finset.range (2 ^ 48) := by
    intro k mem
    apply Finset.mem_range.mpr
    rcases mem_keys.mp (List.mem_toFinset.mp mem) with known | ⟨_, query⟩
    · change k ∈ (memoryInitialEntries stream).map MemRecordEntry.addr at known
      rw [memoryInitialEntries_addresses] at known
      obtain ⟨loc, used, rfl⟩ := List.mem_map.mp known
      exact MemLoc.busAddress_lt_two_pow_48 (canonical_of_mem_touched canonical used)
    · rcases query with reg | ⟨_, below, _⟩
      · omega
      · exact below
  have cap := Finset.card_le_card bound
  rw [List.toFinset_card_of_nodup (ordered_keys touched requested).nodup, Finset.card_range] at cap
  let rows := terminals snapshot stream requested data hint
  have lengthKeys : rows.length = ks.length := by simpa using congrArg List.length (terminals_keys snapshot stream requested canonical data hint)
  have required := (List.length_filter_le (fun r : Terminal (ZMod p) => r.ram == ram) rows).trans (lengthKeys.le.trans cap)
  exact required

/-- Rounding the original finalizer height fits the host row-index type. -/
theorem terminal_count_fit (ram : Bool) (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess) (requested : List ℕ)
    (canonical : MemoryAddressesCanonical stream) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    WitnessGeneration.demandHeight ((terminals snapshot stream requested data hint).filter (fun r => r.ram == ram)).length ≤ UInt64.size :=
  (WitnessGeneration.demandHeight_le_pow (terminal_count_bound ram snapshot stream requested canonical data hint)).trans (by decide)

/-- Every finalizer host-row count fits by its physical address inventory. -/
theorem terminals_fit (ram : Bool) (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess) (requested : List ℕ)
    (canonical : MemoryAddressesCanonical stream) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    WitnessGeneration.demandHeight (finalInputs ram 0 (terminals snapshot stream requested data hint)).length ≤ UInt64.size := by
  unfold finalInputs
  rw [orderedInputs_length]
  exact terminal_count_fit ram snapshot stream requested canonical data hint

/-- The actual terminal payloads appear in strict physical address order. -/
theorem terminals_ordered (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess) (requested : List ℕ)
    (canonical : MemoryAddressesCanonical stream) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (terminals snapshot stream requested data hint).Pairwise (fun a b => a.key < b.key) := by
  apply (List.pairwise_map (R := (· < ·)) (f := Terminal.key)).mp
  rw [terminals_keys snapshot stream requested canonical data hint]
  exact (ordered_keys ..).pairwise

/-- Both touched and untouched payloads belong to their original register/RAM row domains. -/
theorem terminals_valid (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess) (requested : List ℕ)
    (guest : MemoryAddressesInLayout stream)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ row ∈ terminals snapshot stream requested data hint, row.Valid := by
  intro row member
  rcases List.mem_append.mp (List.mem_mergeSort.mp member) with touched | additional
  · obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp touched
    apply entry_valid
    have key := List.mem_map_of_mem (f := MemRecordEntry.addr) inside
    rw [memoryFinalEntries_addresses] at key
    obtain ⟨loc, present, key⟩ := List.mem_map.mp key
    obtain ⟨a, used, locEq⟩ := mem_touchedMemoryLocations.mp present
    cases loc with
    | reg index => exact Or.inl (key ▸ index.isLt)
    | ram cell =>
      have domain := guest a used cell locEq
      exact Or.inr (key ▸ ⟨domain.1, domain.2, Nat.mul_mod_left _ _⟩)
  · obtain ⟨extra, inside, rfl⟩ := List.mem_map.mp additional
    exact extra_valid snapshot _ requested data hint extra inside

/-- If touched guest RAM belongs to the native guest address range, the generated tables
satisfy both original finalizers. Registers are in range by construction. -/
theorem compiled_finalizers_valid (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess) (requested : List ℕ)
    (guest : MemoryAddressesInLayout stream)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (ram : Bool) :
    let rows := terminals snapshot stream requested data hint
    ∃ fit, (finalTable ram rows data fit).Constraints ∧ (finalTable ram rows data fit).Guarantees := by
  have canonical := guest.canonical
  exact ⟨terminals_fit ram snapshot stream requested canonical data hint, finalTable_valid ram _ data _
    (terminals_ordered snapshot stream requested canonical data hint) (terminals_valid snapshot stream requested guest data hint)⟩

/-- Replace the two original finalizer slots in a physical source family with their concrete
generated tables. Every other source is read unchanged. -/
def withFinalTables (raw : Source → Table (ZMod p)) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p))
    (fit : ∀ ram, WitnessGeneration.demandHeight (finalInputs ram 0 rows).length ≤ UInt64.size) (id : Source) : Table (ZMod p) :=
  match id with
  | .finalizer ram => finalTable ram rows data (fit ram)
  | other => raw other

/-- The actual counted supplier reads the complete active terminal receipt from the selected
physical register/RAM row, for any original provider data or multiplicities on other tables. -/
theorem final_mem_live_of_rows (raw : Source → Table (ZMod p)) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p))
    (fit : ∀ ram, WitnessGeneration.demandHeight (finalInputs ram 0 rows).length ≤ UInt64.size)
    (same : ∀ ram, (raw (.finalizer ram)).table = (finalTable ram rows data (fit ram)).table)
    (r : Terminal (ZMod p)) (member : r ∈ rows) :
    finalReadback r.record ∈ Counted.live (records raw) := by
  obtain ⟨previous, found⟩ := orderedInputs_member (fun prev r => (OrderedMemoryProvider.populate r.record prev r.key).1) member 0
  let input := (OrderedMemoryProvider.populate r.record previous r.key).1
  let c := originalFinal (p := p) r.ram
  let inputs := WitnessGeneration.guardedRows (F := ZMod p) (finalInputs r.ram 0 rows)
  let actual : OrderedMemoryProvider.RowInput MemoryMsg (ZMod p) := (input, 1)
  have occurs : actual ∈ inputs := List.mem_append_left _ (List.mem_map_of_mem found)
  let table := raw (.finalizer r.ram)
  let built := c.buildRow actual (c.inputData inputs data) (.empty _)
  have present : built ∈ table.table := (same r.ram) ▸ List.mem_map_of_mem occurs
  let env := table.environment built
  have decoded : valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env = actual :=
    c.rowInput_buildRow actual _ _ _
  have gate : (valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env).2 = 1 := congrArg Prod.snd decoded
  have record : finalRecordAt r.ram env = r.record := (finalRecordAt_eq r.ram env).trans
    (congrArg (fun i : OrderedMemoryProvider.RowInput MemoryMsg (ZMod p) => i.1.payload) decoded)
  have real : (1, finalReadback r.record) ∈ records raw := by
    refine List.mem_flatMap.mpr ⟨.finalizer r.ram, sources_complete _, List.mem_flatMap.mpr ⟨built, present, ?_⟩⟩
    change (1, finalReadback r.record) ∈ [((valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env).2, finalReadback (finalRecordAt r.ram env))]
    rw [gate, record]; exact List.mem_singleton_self _
  exact List.mem_map.mpr ⟨(1, finalReadback r.record), List.mem_filter.mpr ⟨real, by simp⟩, rfl⟩

/-- The actual counted supplier reads the complete active terminal receipt from the selected
physical register/RAM row, for any original provider data or multiplicities on other tables. -/
theorem final_mem_live (raw : Source → Table (ZMod p)) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p))
    (fit : ∀ ram, WitnessGeneration.demandHeight (finalInputs ram 0 rows).length ≤ UInt64.size) (r : Terminal (ZMod p)) (member : r ∈ rows) :
    finalReadback r.record ∈ Counted.live (records (withFinalTables raw rows data fit)) :=
  final_mem_live_of_rows (withFinalTables raw rows data fit) rows data fit (fun _ => rfl) r member

/-- Every otherwise untouched valid requested key is now covered in the actual raw source list
used by the counted router, throughout the full representable clock range. -/
theorem sparse_live_covers_of_rows (raw : Source → Table (ZMod p)) (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess)
    (requested : List ℕ) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (fit : ∀ ram, WitnessGeneration.demandHeight (finalInputs ram 0 (terminals snapshot stream requested data hint)).length ≤ UInt64.size)
    (same : ∀ ram, (raw (.finalizer ram)).table = (finalTable ram (terminals snapshot stream requested data hint) data (fit ram)).table)
    (key : ℕ) (wanted : key ∈ requested) (legal : ValidKey key) (fresh : key ∉ (memoryInitialEntries stream).map MemRecordEntry.addr)
    (time : ℕ) (bound : time < 2 ^ 48) :
    ∃ loc : MemLoc, loc.busAddress = key ∧
      ∃ r ∈ Counted.live (records raw),
        Counted.Covers r ⟨Address.ofNat key, Address.ofNat time, Soundness.Target.bitVecToWord (snapshot.read loc)⟩ := by
  obtain ⟨sparse, present, _, checked, record, emitted, address, covered⟩ :=
    Counted.sparse_covers snapshot stream requested key wanted legal fresh time bound data hint
  let row := terminalOfRows snapshot data sparse
  have included : row ∈ terminals snapshot stream requested data hint :=
    List.mem_mergeSort.mpr (List.mem_append_right _ (List.mem_map_of_mem present))
  have pushed : readbackChannel.pushedValue (finalReadback row.record) = readbackChannel.pushedValue (finalReadback record) :=
    List.singleton_inj.mp (checked.2.2.2.2.2.symm.trans emitted)
  have message : finalReadback row.record = finalReadback record := ProvableType.toElements_inj_iff.mp
    (Vector.toArray_inj.mp (congrArg Interaction.msg pushed))
  exact ⟨MemoryMsg.locOf record, address, finalReadback row.record, final_mem_live_of_rows raw _ data fit same row included, message ▸ covered⟩

/-- Every otherwise untouched valid requested key is now covered in the actual raw source list
used by the counted router, throughout the full representable clock range. -/
theorem sparse_live_covers (raw : Source → Table (ZMod p)) (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess)
    (requested : List ℕ) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (fit : ∀ ram, WitnessGeneration.demandHeight (finalInputs ram 0 (terminals snapshot stream requested data hint)).length ≤ UInt64.size)
    (key : ℕ) (wanted : key ∈ requested) (legal : ValidKey key) (fresh : key ∉ (memoryInitialEntries stream).map MemRecordEntry.addr)
    (time : ℕ) (bound : time < 2 ^ 48) :
    ∃ loc : MemLoc, loc.busAddress = key ∧
      ∃ r ∈ Counted.live (records (withFinalTables raw (terminals snapshot stream requested data hint) data fit)),
        Counted.Covers r ⟨Address.ofNat key, Address.ofNat time, Soundness.Target.bitVecToWord (snapshot.read loc)⟩ :=
  sparse_live_covers_of_rows _ snapshot stream requested data hint fit (fun _ => rfl) key wanted legal fresh time bound

/-- Route a valid untouched WRITE demand through counted sources on the generated two original
finalizers. Both tables fit their physical row type by the address inventory itself. -/
theorem compiled_sparse_covers (raw : Source → Table (ZMod p)) (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess)
    (requested : List ℕ) (canonical : MemoryAddressesCanonical stream) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (key : ℕ) (wanted : key ∈ requested) (legal : ValidKey key) (fresh : key ∉ (memoryInitialEntries stream).map MemRecordEntry.addr)
    (time : ℕ) (bound : time < 2 ^ 48) :
    ∃ loc : MemLoc, loc.busAddress = key ∧
      ∃ r ∈ Counted.live (records (withFinalTables raw (terminals snapshot stream requested data hint) data
        (fun ram => terminals_fit ram snapshot stream requested canonical data hint))),
        Counted.Covers r ⟨Address.ofNat key, Address.ofNat time, Soundness.Target.bitVecToWord (snapshot.read loc)⟩ :=
  sparse_live_covers raw snapshot stream requested data hint _ key wanted legal fresh time bound

end SP1Clean.WriteProbe.SparseBoundary
