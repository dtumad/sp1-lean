import SP1Clean.Soundness.WriteReadbackSources
import SP1Clean.Soundness.SnapshotMemoryEnsemble
import SP1Clean.Proofs.Chips.OrderedSnapshotProvider
import SP1Clean.Proofs.Completeness.MemoryReadbackIntervals
import ToClean.Air.TableBuild
import Mathlib.Data.Finset.Sort
import Std.Data.HashSet.Lemmas

/-! # Queried sparse keys in both authenticated Memory boundaries

Touched keys and valid WRITE queries share one strict ordering. A query missing from the access
stream uses the actual source circuit's zero-time output as the input to the installed finalizer.
Consequently the new initial push and final pull agree, even on an empty access history.
-/

namespace SP1Clean.WriteProbe.SparseBoundary

open Circuit Air.Flat Semantics Soundness TraceGen Channels

/-- Include all prior Memory keys and every representable x12 or aligned RAM request. -/
def keys (touched requested : List ℕ) : List ℕ :=
  let queries := requested.filter fun key => key == 12 ||
    (decide (2 ^ 16 ≤ key ∧ key < 2 ^ 48) && key % 8 == 0)
  (touched.toFinset ∪ queries.toFinset).sort

theorem mem_keys {touched requested : List ℕ} {key : ℕ} :
    key ∈ keys touched requested ↔ key ∈ touched ∨ key ∈ requested ∧ ValidKey key := by
  simp [keys, ValidKey, and_assoc]

theorem ordered_keys (touched requested : List ℕ) : (keys touched requested).SortedLT := Finset.sortedLT_sort _

/-- The preceding ordered cursor, including the zero sentinel before the first physical key. -/
def previousKey (ks : List ℕ) (i : Fin ks.length) : ℕ :=
  if positive : 0 < i.val then ks[i.val - 1]'(by omega) + 1 else 0

theorem previousKey_lt {ks : List ℕ} (ordered : ks.SortedLT) (i : Fin ks.length) :
    previousKey ks i < ks[i.val] + 1 := by
  unfold previousKey
  split
  next pos =>
    exact Nat.succ_lt_succ (ordered.getElem_lt_getElem_of_lt (by omega))
  next => omega

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The original physical source component selected by the queried address space. -/
def source (snapshot : MemorySnapshot) (ram : Bool) : Component (ZMod p) :=
  if ram then (SnapshotMemoryEnsemble.ramView snapshot).component else (SnapshotMemoryEnsemble.registerView snapshot).component

omit [Fact (2 ^ 17 < p)] in
private theorem snapshotKey {record : MemoryMsg (ZMod p)} {snapshot : MemorySnapshot} {key : ℕ}
    (spec : MemoryBoundary.SnapshotSpec snapshot record)
    (indexed : key + 1 = (MemoryMsg.locOf record).busAddress + 1) :
    MemoryBoundary.SnapshotAtSpec snapshot key record :=
  ⟨spec, spec.canonical.2.2.trans (Nat.add_right_cancel indexed).symm⟩

omit [Fact (2 ^ 17 < p)] in
private theorem eval_gate {Payload : TypeMap} [ProvableType Payload] (env : Environment (ZMod p)) :
    env (varFromOffset (OrderedMemoryProvider.RowInput Payload) 0).2 =
      (valueFromOffset (OrderedMemoryProvider.RowInput Payload) 0 env).2 := by
  rw [← eval_varFromOffset_valueFromOffset, eval_pair (α := OrderedMemoryProvider.Inputs Payload) (β := field)]
  simp only [ProvableType.eval_field]

/-- The original physical source word as returned by the two installed source components. -/
def sourceRecord (snapshot : MemorySnapshot) (ram : Bool) (env : Environment (ZMod p)) : MemoryMsg (ZMod p) :=
  if ram then (SnapshotMemoryEnsemble.ramView snapshot).component.rowOutput env
  else (SnapshotMemoryEnsemble.registerView snapshot).component.rowOutput env

private theorem source_ledger (snapshot : MemorySnapshot) (ram : Bool) (env : Environment (ZMod p)) :
    let c := source snapshot ram
    let id := if ram then SnapshotMemoryEnsemble.TableId.ram else .registers
    c.operations.interactionValuesWith memoryChannel.toRaw env =
      [memoryChannel.pushedIfValue (env (SnapshotMemoryEnsemble.viewFor snapshot id).activity) (sourceRecord snapshot ram env)] := by
  cases ram
  case false => exact SnapshotMemoryEnsemble.recordFor_interactions snapshot .registers env
  case true => exact SnapshotMemoryEnsemble.recordFor_interactions snapshot .ram env

private theorem source_live (snapshot : MemorySnapshot) (ram : Bool) (env : Environment (ZMod p))
    (enabled : if ram then env (varFromOffset (OrderedMemoryProvider.RowInput Word) 0).2 = 1
      else env (varFromOffset (OrderedMemoryProvider.RowInput RegisterSnapshotRow) 0).2 = 1) :
    (source snapshot ram).operations.interactionValuesWith memoryChannel.toRaw env =
      [memoryChannel.pushedValue (sourceRecord snapshot ram env)] := by
  have ledger := source_ledger snapshot ram env
  dsimp only at ledger
  have active : Expression.eval env (SnapshotMemoryEnsemble.viewFor snapshot
      (if ram then .ram else .registers)).activity = 1 := by
    cases ram <;> simpa only [Bool.false_eq_true, ↓reduceIte, SnapshotMemoryEnsemble.viewFor,
      SnapshotMemoryEnsemble.registerView, SnapshotMemoryEnsemble.ramView, OrderedMemoryEnsemble.providerView] using enabled
  rw [active] at ledger
  exact ledger

/-- Select the real source circuit's active ordered input for an extra probe key. -/
def sourceInput? (snapshot : MemorySnapshot) (ram : Bool) (previous key : ℕ) :
    Option ((source (p := p) snapshot ram).Input (ZMod p)) :=
  match ram with
  | true => OrderedSnapshotProvider.populateRam? previous key
  | false => if key = 12 ∧ previous < 13 then
      some (OrderedMemoryProvider.populate (SnapshotRegisterProvider.populate (p := p) snapshot 12) previous 12)
    else none

private theorem registerSource (snapshot : MemorySnapshot) (previous : ℕ) (ordered : previous < 12 + 1)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∃ input : (source (p := p) snapshot false).Input (ZMod p),
      sourceInput? snapshot false previous 12 = some input ∧
      let c := source (p := p) snapshot false
      let env := Environment.fromArray (c.buildRow input data hint) data
      c.operations.ConstraintsHold env ∧
        c.operations.interactionValuesWith memoryChannel.toRaw env = [memoryChannel.pushedValue (c.rowOutput env)] ∧
        MemoryBoundary.SnapshotAtSpec snapshot 12 (c.rowOutput env) := by
  let c := source (p := p) snapshot false
  let input := OrderedMemoryProvider.populate (SnapshotRegisterProvider.populate (p := p) snapshot 12) previous 12
  have valid := OrderedSnapshotProvider.populateRegister_assumptions (p := p)
    SnapshotMemoryEnsemble.channelName snapshot 12 previous ordered data hint
  let env := Environment.fromArray (c.buildRow input data hint) data
  refine ⟨input, by simp [sourceInput?, ordered, input], (c.buildRow_constraintsHold input data hint valid).1, ?_, ?_⟩
  · have decoded : valueFromOffset (OrderedMemoryProvider.RowInput RegisterSnapshotRow) 0 env = input :=
      c.rowInput_buildRow input data data hint
    have stored := congrArg (fun r : OrderedMemoryProvider.RowInput RegisterSnapshotRow (ZMod p) => r.2) decoded
    have active : env (varFromOffset (OrderedMemoryProvider.RowInput RegisterSnapshotRow) 0).2 = 1 :=
      (eval_gate (Payload := RegisterSnapshotRow) env).trans stored
    exact source_live snapshot false env active
  have sound := (c.buildRow_spec_requirements input data hint valid (by intro _; trivial)).1
  change c.circuit.Spec (c.rowInput env) (c.rowOutput env) data at sound
  have decoded : c.rowInput env = input := c.rowInput_buildRow input data data hint
  rw [decoded] at sound
  have result := sound.2 rfl
  apply snapshotKey result.1
  have same := result.2.2
  change Word.toNat (Target.bitVecToWord (BitVec.ofNat 64 (12 + 1))) = _ at same
  simpa only [← Word.toBitVec64_toNat (Target.isU64_bitVecToWord _), Target.toBitVec64_bitVecToWord,
    BitVec.toNat_ofNat] using same

private theorem ramSource (snapshot : MemorySnapshot) (previous key : ℕ) (ordered : previous < key + 1)
    (lower : 2 ^ 16 ≤ key) (upper : key < 2 ^ 48) (aligned : key % 8 = 0)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∃ input : (source (p := p) snapshot true).Input (ZMod p),
      sourceInput? snapshot true previous key = some input ∧
      let c := source (p := p) snapshot true
      let env := Environment.fromArray (c.buildRow input data hint) data
      c.operations.ConstraintsHold env ∧
        c.operations.interactionValuesWith memoryChannel.toRaw env = [memoryChannel.pushedValue (c.rowOutput env)] ∧
        MemoryBoundary.SnapshotAtSpec snapshot key (c.rowOutput env) := by
  let c := source (p := p) snapshot true
  obtain ⟨input, found⟩ := Option.isSome_iff_exists.mp
    ((OrderedSnapshotProvider.populateRam?_isSome_iff (p := p) previous key).mpr ⟨ordered, lower, upper, aligned⟩)
  have valid := OrderedSnapshotProvider.populateRam?_sound SnapshotMemoryEnsemble.channelName snapshot previous key input found data hint
  have produced := found
  unfold OrderedSnapshotProvider.populateRam? at found
  rw [ite_eq_left ordered] at found
  obtain ⟨payload, _, rfl⟩ := Option.map_eq_some_iff.mp found
  let input := OrderedMemoryProvider.populate payload previous key
  let env := Environment.fromArray (c.buildRow input data hint) data
  refine ⟨input, produced, (c.buildRow_constraintsHold input data hint valid).1, ?_, ?_⟩
  · have decoded : valueFromOffset (OrderedMemoryProvider.RowInput Word) 0 env = input :=
      c.rowInput_buildRow input data data hint
    have stored := congrArg (fun r : OrderedMemoryProvider.RowInput Word (ZMod p) => r.2) decoded
    have active : env (varFromOffset (OrderedMemoryProvider.RowInput Word) 0).2 = 1 :=
      (eval_gate (Payload := Word) env).trans stored
    exact source_live snapshot true env active
  have sound := (c.buildRow_spec_requirements input data hint valid (by intro _; trivial)).1
  change c.circuit.Spec (c.rowInput env) (c.rowOutput env) data at sound
  have decoded : c.rowInput env = input := c.rowInput_buildRow input data data hint
  rw [decoded] at sound
  have result := sound.2 rfl
  apply snapshotKey result.1
  have bound : key + 1 < 2 ^ 64 := by omega
  have same := result.2.2
  change Word.toNat (Target.bitVecToWord (BitVec.ofNat 64 (key + 1))) = _ at same
  simpa only [← Word.toBitVec64_toNat (Target.isU64_bitVecToWord _), Target.toBitVec64_bitVecToWord,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using same

private theorem final_memory (ram : Bool) (env : Environment (ZMod p)) :
    let gate := (valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env).2
    (finalComponent ram).operations.interactionValuesWith memoryChannel.toRaw env =
      [memoryChannel.pulledIfValue gate (finalRecordAt ram env)] := by
  let id := if ram then FinalMemoryEnsemble.TableId.ram else .registers
  have same : (finalComponent (p := p) ram).operations.interactionsWith memoryChannel.toRaw =
      (FinalMemoryEnsemble.viewFor id).component.operations.interactionsWith memoryChannel.toRaw := by
    refine (final_original_interactions ram memoryChannel.toRaw (by
      intro equal
      exact (by decide : "SP1Memory" ≠ "sp1.native.write_readback") (congrArg RawChannel.name equal))).trans ?_
    cases ram
    · exact FinalMemoryReceipt.interactions false OrderedFinalProvider.registerCircuit _ (by
      intro equal
      exact (by decide : "SP1Memory" ≠ "SP1FinalRegisterValue") (congrArg RawChannel.name equal))
    · exact FinalMemoryReceipt.interactions true OrderedFinalProvider.ramCircuit _ (by
      intro equal
      exact (by decide : "SP1Memory" ≠ "SP1FinalRamValue") (congrArg RawChannel.name equal))
  have ledger := FinalMemoryEnsemble.recordFor_interactions id env
  rw [Operations.interactionValuesWith, same, ← Operations.interactionValuesWith]
  rw [finalRecordAt_eq]
  have gate := eval_gate (Payload := MemoryMsg) env
  have active : env (FinalMemoryEnsemble.viewFor (p := p) id).activity =
      (valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env).2 := by
    cases ram <;> simpa only [id, Bool.false_eq_true, ↓reduceIte, FinalMemoryEnsemble.viewFor,
      FinalMemoryEnsemble.registerView_activity, FinalMemoryEnsemble.ramView_activity,
      FinalMemoryEnsemble.activity, varFromOffset_pair, ProvableType.varFromOffset_field, Nat.zero_add] using gate
  rw [active] at ledger
  cases ram <;> exact ledger

omit [Fact (2 ^ 17 < p)] in
private theorem registerDomain {snapshot : MemorySnapshot} {record : MemoryMsg (ZMod p)}
    (actual : MemoryBoundary.SnapshotAtSpec snapshot 12 record) : FinalRegisterProvider.Domain record := by
  have packed := actual.2
  simp only [MemoryBoundary.address, Word.toNat, circuit_norm, ZMod.val_zero, zero_mul, add_zero] at packed
  refine ⟨by omega, ZMod.val_injective _ ?_, ZMod.val_injective _ ?_⟩ <;> simp only [ZMod.val_zero] <;> omega

/-- A positive source row supplies the exact finalized zero-time record, including every
address and value limb. Both original Memory occurrences cancel and the attached private source
offers a closed interval containing all representable clocks. -/
private theorem finalPair (ram : Bool) (snapshot : MemorySnapshot) (previous key : ℕ)
    (record : MemoryMsg (ZMod p)) (actual : MemoryBoundary.SnapshotAtSpec snapshot key record)
    (domain : if ram then 2 ^ 16 ≤ key ∧ key < 2 ^ 48 ∧ key % 8 = 0 else key = 12)
    (ordered : previous < key + 1) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    let c := finalComponent ram
    let input := OrderedMemoryProvider.populate record previous key
    let env := Environment.fromArray (c.buildRow input data hint) data
    c.operations.ConstraintsHold env ∧
    c.operations.interactionValuesWith memoryChannel.toRaw env = [memoryChannel.pulledValue record] ∧
    c.operations.interactionValuesWith readbackChannel.toRaw env = [readbackChannel.pushedValue (finalReadback record)] := by
  let c := finalComponent (p := p) ram
  let input := OrderedMemoryProvider.populate record previous key
  let env := Environment.fromArray (c.buildRow input data hint) data
  have canonical := actual.1.canonical
  have valid : c.circuit.ProverAssumptions input data hint := by
    cases ram
    case false =>
      change key = 12 at domain
      subst key
      change OrderedFinalProvider.registerCircuit.ProverAssumptions (OrderedMemoryProvider.populate record previous 12) data hint
      have ready := (OrderedFinalProvider.populateRegister?_isSome_iff previous record).mpr
        ⟨⟨registerDomain actual, actual.1.1, actual.1.2.1⟩, actual.2 ▸ ordered⟩
      obtain ⟨built, found⟩ := Option.isSome_iff_exists.mp ready
      have ok := OrderedFinalProvider.populateRegister?_sound previous record built found data hint
      unfold OrderedFinalProvider.populateRegister? at found
      split at found
      · obtain rfl := Option.some.inj found
        simpa only [actual.2] using ok
      · contradiction
    case true =>
      change 2 ^ 16 ≤ key ∧ key < 2 ^ 48 ∧ key % 8 = 0 at domain
      change OrderedFinalProvider.ramCircuit.ProverAssumptions (OrderedMemoryProvider.populate record previous key) data hint
      have ramDomain : FinalRamProvider.Domain record := by
        unfold FinalRamProvider.Domain
        rw [actual.2]
        exact ⟨canonical.2.1, domain⟩
      have ready := (OrderedFinalProvider.populateRam?_isSome_iff previous record).mpr
        ⟨⟨ramDomain, actual.1.1, actual.1.2.1⟩, actual.2 ▸ ordered⟩
      obtain ⟨built, found⟩ := Option.isSome_iff_exists.mp ready
      have ok := OrderedFinalProvider.populateRam?_sound previous record built found data hint
      unfold OrderedFinalProvider.populateRam? at found
      split at found
      · obtain rfl := Option.some.inj found
        simpa only [actual.2] using ok
      · contradiction
  have decoded : valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env = input :=
    c.rowInput_buildRow input data data hint
  have out : finalRecordAt ram env = record := (finalRecordAt_eq ram env).trans
    (congrArg (fun r : OrderedMemoryProvider.RowInput MemoryMsg (ZMod p) => r.1.payload) decoded)
  have active : (valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env).2 = 1 :=
    congrArg (fun r : OrderedMemoryProvider.RowInput MemoryMsg (ZMod p) => r.2) decoded
  refine ⟨(c.buildRow_constraintsHold input data hint valid).1, ?_, ?_⟩
  · have ledger := final_memory ram env
    rw [out, active] at ledger
    exact ledger
  · have ledger := final_row_receipt ram env
    rw [out, active] at ledger
    exact ledger

/-- Both authentic boundary tables use exactly this sorted key inventory. -/
theorem initial_final_keys (stream : List MemoryHistoryAccess) (requested : List ℕ) :
    keys ((memoryInitialEntries stream).map MemRecordEntry.addr) requested =
      keys ((memoryFinalEntries stream).map MemRecordEntry.addr) requested := by
  rw [memoryInitialEntries_addresses, memoryFinalEntries_addresses]

/-- The two physical row arrays built by the source and final circuits for one sparse location. -/
structure Rows (F : Type) where
  /-- Guest RAM uses the RAM components, x12 uses the register components. -/
  ram : Bool
  /-- Ordered Memory address used by both original providers. -/
  key : ℕ
  /-- Source array produced by the actual ordered snapshot component. -/
  initial : Array F
  /-- Final array produced by the protected ordered finalizer. -/
  final : Array F

private def buildFrom (snapshot : MemorySnapshot) (ram : Bool) (previous key : ℕ)
    (input : (source (p := p) snapshot ram).Input (ZMod p)) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : Rows (ZMod p) :=
  let initial := (source snapshot ram).buildRow input data hint
  let record := sourceRecord snapshot ram (Environment.fromArray initial data)
  ⟨ram, key, initial, (finalComponent ram).buildRow (OrderedMemoryProvider.populate record previous key) data hint⟩

/-- Execute the honest ordered source constructor, then finalize its exact authenticated output. -/
def build? (snapshot : MemorySnapshot) (previous key : ℕ) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    Option (Rows (ZMod p)) :=
  let ram := decide (key ≠ 12)
  (sourceInput? snapshot ram previous key).map fun input => buildFrom snapshot ram previous key input data hint

/-- Both raw environments satisfy their constraints, cancel the same original Memory record, and
supply its closed private version. The original source circuit fixes the actual timestamp and word. -/
def Rows.Checked (rows : Rows (ZMod p)) (snapshot : MemorySnapshot) (data : ProverData (ZMod p)) : Prop :=
  let sourceEnv := Environment.fromArray rows.initial data
  let record := sourceRecord snapshot rows.ram sourceEnv
  let finalEnv := Environment.fromArray rows.final data
  (source snapshot rows.ram).operations.ConstraintsHold sourceEnv ∧
    (source snapshot rows.ram).operations.interactionValuesWith memoryChannel.toRaw sourceEnv = [memoryChannel.pushedValue record] ∧
    MemoryBoundary.SnapshotAtSpec snapshot rows.key record ∧
    (finalComponent rows.ram).operations.ConstraintsHold finalEnv ∧
    (finalComponent rows.ram).operations.interactionValuesWith memoryChannel.toRaw finalEnv = [memoryChannel.pulledValue record] ∧
    (finalComponent rows.ram).operations.interactionValuesWith readbackChannel.toRaw finalEnv = [readbackChannel.pushedValue (finalReadback record)]

/-- Two real generated rows at a canonical sparse key. -/
def RowPair (snapshot : MemorySnapshot) (ram : Bool) (previous key : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : Prop :=
  ∃ input, (buildFrom snapshot ram previous key input data hint).Checked snapshot data

private theorem generated (snapshot : MemorySnapshot) (touched requested : List ℕ)
    (i : Fin (keys touched requested).length) (fresh : (keys touched requested)[i.val] ∉ touched)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    let ks := keys touched requested
    let key := ks[i.val]
    let previous := previousKey ks i
    ∃ (ram : Bool) (input : (source (p := p) snapshot ram).Input (ZMod p)),
      ram = decide (key ≠ 12) ∧ sourceInput? snapshot ram previous key = some input ∧
      (buildFrom snapshot ram previous key input data hint).Checked snapshot data := by
  let ks := keys touched requested
  let key := ks[i.val]
  let previous := previousKey ks i
  have valid : ValidKey key := ((mem_keys.mp (List.getElem_mem i.isLt)).resolve_left fresh).2
  have ordered : previous < key + 1 := previousKey_lt (ordered_keys touched requested) i
  rcases valid with reg | ⟨lower, upper, aligned⟩
  · obtain ⟨input, found, holds, ledger, indexed⟩ := registerSource snapshot previous (reg ▸ ordered) data hint
    let c := source (p := p) snapshot false
    let env := Environment.fromArray (c.buildRow input data hint) data
    have atKey : MemoryBoundary.SnapshotAtSpec snapshot key (sourceRecord snapshot false env) := by
      rw [reg]
      exact indexed
    have tag : false = decide (key ≠ 12) := by simp [reg]
    have made : sourceInput? snapshot false previous key = some input := by rw [reg]; exact found
    exact ⟨false, input, tag, made, holds, ledger, atKey,
      finalPair false snapshot previous key _ atKey reg ordered data hint⟩
  · obtain ⟨input, found, holds, ledger, indexed⟩ := ramSource snapshot previous key ordered lower upper aligned data hint
    have tag : true = decide (key ≠ 12) := by simp [show key ≠ 12 by omega]
    exact ⟨true, input, tag, found, holds, ledger, indexed,
      finalPair true snapshot previous key _ indexed ⟨lower, upper, aligned⟩ ordered data hint⟩

/-- Every additional valid request yields actual checked source and final arrays from the executable builder. -/
theorem build?_checked (snapshot : MemorySnapshot) (touched requested : List ℕ)
    (i : Fin (keys touched requested).length) (fresh : (keys touched requested)[i.val] ∉ touched)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∃ rows, build? snapshot (previousKey (keys touched requested) i) (keys touched requested)[i.val] data hint = some rows ∧
      rows.key = (keys touched requested)[i.val] ∧ rows.Checked snapshot data := by
  obtain ⟨ram, input, tag, made, valid⟩ := generated snapshot touched requested i fresh data hint
  subst ram
  exact ⟨_, by simp only [build?, made, Option.map_some], rfl, valid⟩

private def positions (ks : List ℕ) : List (ℕ × ℕ) :=
  ks.zip (0 :: ks.map (· + 1))

private theorem positions_length (ks : List ℕ) : (positions ks).length = ks.length := by
  simp [positions]

private theorem position_eq (ks : List ℕ) (i : Fin ks.length) :
    (positions ks)[i.val]'(by rw [positions_length]; exact i.isLt) = (ks[i.val], previousKey ks i) := by
  rcases i with ⟨_ | n, inside⟩ <;> simp [positions, List.getElem_zip, previousKey]

/-- Build every additional pair in canonical order. The existing Memory stream is indexed
once, and adjacent ordered cursors are obtained in a single traversal of the sorted union. -/
def buildAll (snapshot : MemorySnapshot) (touched requested : List ℕ) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    List (Rows (ZMod p)) :=
  let used := Std.HashSet.ofList touched
  (positions (keys touched requested)).filterMap fun (key, previous) =>
    if used.contains key then none else build? snapshot previous key data hint

/-- The batch's committed pairs are exactly the successful builders at fresh positions of the
combined inventory. No multiple requests at the same key can generate a second boundary pair. -/
theorem mem_buildAll_iff (snapshot : MemorySnapshot) (touched requested : List ℕ) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (rows : Rows (ZMod p)) :
    rows ∈ buildAll snapshot touched requested data hint ↔
      ∃ i : Fin (keys touched requested).length, (keys touched requested)[i.val] ∉ touched ∧
        build? snapshot (previousKey (keys touched requested) i) (keys touched requested)[i.val] data hint = some rows := by
  let ks := keys touched requested
  constructor
  · intro member
    obtain ⟨⟨key, previous⟩, position, built⟩ := List.mem_filterMap.mp member
    obtain ⟨n, inside, same⟩ := List.mem_iff_getElem.mp position
    let i : Fin ks.length := ⟨n, by rw [positions_length] at inside; exact inside⟩
    have agree := (position_eq ks i).symm.trans same
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj agree
    by_cases used : ks[i.val] ∈ touched
    · simp [Std.HashSet.contains_ofList, used] at built
    · exact ⟨i, used, by simpa [Std.HashSet.contains_ofList, used] using built⟩
  · rintro ⟨i, unused, built⟩
    apply List.mem_filterMap.mpr
    refine ⟨(ks[i.val], previousKey ks i), List.mem_iff_getElem.mpr ⟨i.val, ?_, position_eq ks i⟩, ?_⟩
    · rw [positions_length]
      exact i.isLt
    · simpa only [ks, Std.HashSet.contains_ofList, List.contains_iff_mem, unused, ↓reduceIte] using built

/-- Each previously untouched valid request occurs in the actual generated batch with its
authentic word, exact original Memory cancellation and finalizer publication. -/
theorem buildAll_covers (snapshot : MemorySnapshot) (touched requested : List ℕ)
    (i : Fin (keys touched requested).length) (fresh : (keys touched requested)[i.val] ∉ touched)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∃ rows ∈ buildAll snapshot touched requested data hint, rows.key = (keys touched requested)[i.val] ∧ rows.Checked snapshot data := by
  obtain ⟨rows, built, key, checked⟩ := build?_checked snapshot touched requested i fresh data hint
  exact ⟨rows, (mem_buildAll_iff snapshot touched requested data hint rows).mpr ⟨i, fresh, built⟩, key, checked⟩

/-- Any additional admissible request has a real source and final row at its place in the
combined strict ordering. The source fixes all four limbs of the word and timestamp zero. -/
theorem sparse_pair (snapshot : MemorySnapshot) (touched requested : List ℕ)
    (i : Fin (keys touched requested).length) (fresh : (keys touched requested)[i.val] ∉ touched)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∃ ram, RowPair snapshot ram (previousKey (keys touched requested) i) (keys touched requested)[i.val] data hint := by
  obtain ⟨ram, input, _, _, valid⟩ := generated snapshot touched requested i fresh data hint
  exact ⟨ram, input, valid⟩

omit [Fact (2 ^ 17 < p)] in
/-- A zero-time sparse suffix covers every legal probe clock and carries the snapshot's
word at every one of those cuts in the actual untouched history. -/
theorem sparse_interval [Fact (2 ^ 24 < p)] (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess)
    {record : MemoryMsg (ZMod p)} {key : ℕ} (actual : MemoryBoundary.SnapshotAtSpec snapshot key record)
    (fresh : key ∉ (memoryInitialEntries stream).map MemRecordEntry.addr) :
    clkNat (finalReadback record).previousHigh (finalReadback record).previousLow = 0 ∧
      clkNat (finalReadback record).currentHigh (finalReadback record).currentLow = 2 ^ 48 - 1 ∧
      ∀ time, MemoryHistoryAccess.heldAt (snapshot.read (MemoryMsg.locOf record)) time
        (memoryHistoryAt stream (MemoryMsg.locOf record)) = Word.toBitVec64 (finalReadback record).value := by
  obtain ⟨lower, upper⟩ := finalReadback_clocks record
  refine ⟨lower.trans actual.1.2.2.1, upper, ?_⟩
  have addr := actual.1.canonical.2.2.symm.trans actual.2
  rw [memoryInitialEntries_addresses] at fresh
  have unused : MemoryMsg.locOf record ∉ touchedMemoryLocations stream := by
    intro used
    exact fresh (List.mem_map.mpr ⟨_, used, addr⟩)
  have empty : memoryHistoryAt stream (MemoryMsg.locOf record) = [] := by
    apply List.filter_eq_nil_iff.mpr
    exact fun a member same => unused (mem_touchedMemoryLocations.mpr ⟨a, member, of_decide_eq_true same⟩)
  intro time
  simpa only [empty, MemoryHistoryAccess.heldAt, finalReadback] using actual.1.2.2.2.2.1

end SP1Clean.WriteProbe.SparseBoundary
