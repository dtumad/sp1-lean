import SP1Clean.Proofs.Completeness.WriteSparseInitializers
import ToClean.Air.GuardedLedger

/-! # Fixed cursor endpoints of generated sparse Memory inventories

Both original providers use the same register/RAM key walk. One actual terminal component
closes the final occupied key to the verifier's fixed endpoint, including for an empty walk.
-/

namespace SP1Clean.WriteProbe.SparseBoundary

open Circuit Air.Flat Semantics TraceGen Channels Soundness

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Encode the ordered verifier cursor in its four little-endian 16-bit limbs. -/
def cursor (n : ℕ) : Word (ZMod p) := Target.bitVecToWord (BitVec.ofNat 64 n)

private theorem cursor_value {n : ℕ} (fits : n < 2 ^ 64) : Word.toNat (cursor (p := p) n) = n := by
  rw [cursor, ← Word.toBitVec64_toNat (Target.isU64_bitVecToWord _), Target.toBitVec64_bitVecToWord,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

omit [Fact (2 ^ 25 < p)] in
private theorem cursor_zero : cursor (p := p) 0 = OrderedMemoryEnsemble.startKey := by
  norm_num [cursor, Target.bitVecToWord, OrderedMemoryEnsemble.startKey]

/-- The actual outgoing cursor after all active register and RAM rows. -/
def lastCursor {F : Type} (previous : ℕ) : List (Terminal F) → ℕ
  | [] => previous
  | first :: rest => lastCursor (first.key + 1) rest

private theorem lastCursor_bound {F : Type} (rows : List (Terminal F)) (previous : ℕ)
    (start : previous ≤ 2 ^ 48) (bounded : ∀ r ∈ rows, r.key < 2 ^ 48) : lastCursor previous rows ≤ 2 ^ 48 := by
  induction rows generalizing previous with
  | nil => exact start
  | cons r rs ih => exact ih _ (bounded r (List.mem_cons_self ..)) (fun s inside => bounded s (List.mem_cons_of_mem _ inside))

/-- Generate one original terminal row between the final occupied address cursor and the
fixed native end marker. Its data and witness input are built by the stock component. -/
def terminalTable (name : String) (distinct : name ≠ "SP1Byte") (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p)) : Table (ZMod p) :=
  let c := (OrderedMemoryEnsemble.terminalView (p := p) name distinct).component
  Table.ofInputs c [OrderedBoundaryEnd.populate (cursor (lastCursor 0 rows)) OrderedMemoryEnsemble.endKey] data (by change 1 ≤ UInt64.size; decide) (fun _ => trivial)

/-- The exact final row is honest for every legal native key inventory, including an empty one. -/
theorem terminalTable_valid (name : String) (distinct : name ≠ "SP1Byte") (rows : List (Terminal (ZMod p)))
    (bounded : ∀ r ∈ rows, r.key < 2 ^ 48) (data : ProverData (ZMod p)) :
    (terminalTable name distinct rows data).Constraints ∧ (terminalTable name distinct rows data).Guarantees := by
  unfold terminalTable
  apply Table.ofInputs_valid
  intro input member
  obtain rfl := List.mem_singleton.mp member
  have last := lastCursor_bound rows 0 (by decide) bounded
  apply OrderedBoundaryEnd.populate_assumptions
  · exact Target.isU64_bitVecToWord _
  · have : Fact (1 < p) := ⟨(Fact.out (p := p.Prime)).one_lt⟩
    apply Word.isU64_of_cases <;> norm_num [OrderedMemoryEnsemble.endKey, ZMod.val_one]
  · rw [cursor_value (by omega), OrderedMemoryEnsemble.endKey_toNat]
    omega

/-- A single terminal row consumes the actual last cursor and publishes the verifier's
fixed end marker at unit weight. -/
theorem terminalTable_ledger (name : String) (distinct : name ≠ "SP1Byte") (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p)) :
    let ch := OrderedBoundary.channel (p := p) name
    (terminalTable name distinct rows data).interactionsWith ch.toRaw =
      [ch.pulledValue (cursor (lastCursor 0 rows)), ch.pushedValue OrderedMemoryEnsemble.endKey] := by
  let view := OrderedMemoryEnsemble.terminalView (p := p) name distinct
  let c := view.component
  let i := OrderedBoundaryEnd.populate (cursor (p := p) (lastCursor 0 rows)) OrderedMemoryEnsemble.endKey
  let ch := OrderedBoundary.channel (p := p) name
  have ledger := Table.ofInputs_ledger c [i] data (by change 1 ≤ UInt64.size; decide) (fun _ => trivial) ch.toRaw
    (fun row => [ch.pulledValue row.previous, ch.pushedValue OrderedMemoryEnsemble.endKey]) view.interactions
  exact ledger

private def edgeValues {Payload : TypeMap} [ProvableType Payload] (name : String)
    (row : OrderedMemoryProvider.RowInput Payload (ZMod p)) : List (Interaction (ZMod p)) :=
  let ch := OrderedBoundary.channel (p := p) name
  [ch.pulledIfValue row.2 row.1.link.previous, ch.pushedIfValue row.2 row.1.link.current]

private theorem sourceOrder (snapshot : MemorySnapshot) (ram : Bool) (env : Environment (ZMod p)) :
    (source snapshot ram).operations.interactionValuesWith (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw env =
      edgeValues SnapshotMemoryEnsemble.channelName (valueFromOffset (OrderedMemoryProvider.RowInput (InitialPayload ram)) 0 env) := by
  cases ram
  case false =>
    exact OrderedMemoryEnsemble.provider_control _ _ _ (SnapshotRegisterProvider.circuit snapshot) _ _ _ env
  case true =>
    exact OrderedMemoryEnsemble.provider_control _ _ _ (SnapshotRamProvider.circuit snapshot) _ _ _ env

private theorem finalOrder (ram : Bool) (env : Environment (ZMod p)) :
    (originalFinal ram).operations.interactionValuesWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw env =
      edgeValues OrderedFinalProvider.channelName (valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env) := by
  let ch := OrderedBoundary.channel (p := p) OrderedFinalProvider.channelName
  let view := FinalMemoryEnsemble.viewFor (p := p) (if ram then .ram else .registers)
  have same : (originalFinal ram).operations.interactionsWith ch.toRaw = view.component.operations.interactionsWith ch.toRaw := by
    cases ram
    · exact FinalMemoryReceipt.interactions false OrderedFinalProvider.registerCircuit ch.toRaw (fun eq => (by decide : "SP1NativeMemoryFinalOrder" ≠ "SP1FinalRegisterValue") (congrArg RawChannel.name eq))
    · exact FinalMemoryReceipt.interactions true OrderedFinalProvider.ramCircuit ch.toRaw (fun eq => (by decide : "SP1NativeMemoryFinalOrder" ≠ "SP1FinalRamValue") (congrArg RawChannel.name eq))
  change (originalFinal ram).operations.interactionValuesWith ch.toRaw env = _
  rw [Operations.interactionValuesWith, same, ← Operations.interactionValuesWith]
  cases ram
  case false =>
    change FinalMemoryEnsemble.registerView.component.operations.interactionValuesWith _ _ = _
    exact OrderedMemoryEnsemble.provider_control _ _ _ FinalRegisterProvider.circuit _ _ _ env
  case true =>
    change FinalMemoryEnsemble.ramView.component.operations.interactionValuesWith _ _ = _
    exact OrderedMemoryEnsemble.provider_control _ _ _ FinalRamProvider.circuit _ _ _ env

private def steps (name : String) (ram : Bool) (previous : ℕ) (rows : List (Terminal (ZMod p))) : List (Interaction (ZMod p)) :=
  let ch := OrderedBoundary.channel (p := p) name
  (orderedInputs ram (fun prev r => (cursor (p := p) prev, cursor (p := p) (r.key + 1))) previous rows).flatMap
    fun pair => [ch.pulledValue pair.1, ch.pushedValue pair.2]

private def delta (word : Word (ZMod p)) (msg : Array (ZMod p)) : ZMod p := if (toElements word).toArray = msg then 1 else 0

omit [Fact (2 ^ 25 < p)] in
private theorem edge_sum (name : String) (a b : Word (ZMod p)) (msg : Array (ZMod p)) :
    let ch := OrderedBoundary.channel (p := p) name
    balanceOf [ch.pulledValue a, ch.pushedValue b] msg = delta b msg - delta a msg := by
  dsimp only
  simp only [balanceOf_cons, Channel.pushedValue, Channel.pulledValue, Interaction.signedMult,
    show balanceOf ([] : List (Interaction (ZMod p))) msg = 0 from rfl, add_zero, delta]
  split <;> split <;> ring

omit [Fact (2 ^ 25 < p)] in
private theorem steps_sum (name : String) (previous : ℕ) (rows : List (Terminal (ZMod p))) (msg : Array (ZMod p)) :
    balanceOf (steps name false previous rows) msg + balanceOf (steps name true previous rows) msg =
      delta (cursor (lastCursor previous rows)) msg - delta (cursor previous) msg := by
  induction rows generalizing previous with
  | nil => simp [steps, orderedInputs, lastCursor, balanceOf]
  | cons r rs ih =>
    have tail := ih (r.key + 1)
    dsimp only [lastCursor]
    cases tag : r.ram
    case false =>
      have reg : steps name false previous (r :: rs) =
          [(OrderedBoundary.channel name).pulledValue (cursor previous), (OrderedBoundary.channel name).pushedValue (cursor (r.key + 1))] ++ steps name false (r.key + 1) rs := by simp [steps, orderedInputs, tag]
      have ram : steps name true previous (r :: rs) = steps name true (r.key + 1) rs := by simp [steps, orderedInputs, tag]
      rw [reg, ram, balanceOf_append, edge_sum]
      linear_combination tail
    case true =>
      have reg : steps name false previous (r :: rs) = steps name false (r.key + 1) rs := by simp [steps, orderedInputs, tag]
      have ram : steps name true previous (r :: rs) =
          [(OrderedBoundary.channel name).pulledValue (cursor previous), (OrderedBoundary.channel name).pushedValue (cursor (r.key + 1))] ++ steps name true (r.key + 1) rs := by simp [steps, orderedInputs, tag]
      rw [reg, ram, balanceOf_append, edge_sum]
      linear_combination tail

omit [Fact (2 ^ 25 < p)] in
private theorem active_steps {Payload : TypeMap} [ProvableType Payload] (name : String) (ram : Bool)
    (make : ℕ → Terminal (ZMod p) → OrderedMemoryProvider.Inputs Payload (ZMod p))
    (link : ∀ previous r, (make previous r).link.previous = cursor previous ∧ (make previous r).link.current = cursor (r.key + 1))
    (previous : ℕ) (rows : List (Terminal (ZMod p))) :
    (orderedInputs ram make previous rows).flatMap (fun i => edgeValues name (i, 1)) = steps name ram previous rows := by
  induction rows generalizing previous with
  | nil => rfl
  | cons r rs ih =>
    have tail := ih (r.key + 1)
    by_cases tag : r.ram = ram
    · simpa only [steps, orderedInputs, tag, ↓reduceIte, List.flatMap_cons, edgeValues, (link previous r).1, (link previous r).2,
        Channel.pushedValue, Channel.pulledValue, Channel.pulledIfValue, Channel.pushedIfValue,
        List.cons_append, List.nil_append, List.cons.injEq, true_and] using tail
    · simpa only [steps, orderedInputs, tag, ↓reduceIte] using tail

omit [Fact (2 ^ 25 < p)] in
private theorem zero_edges {Payload : TypeMap} [ProvableType Payload] (name : String) (msg : Array (ZMod p)) :
    balanceOf (edgeValues (Payload := Payload) name 0) msg = 0 := by
  simp only [edgeValues, balanceOf_cons, Channel.pushedIfValue, Channel.pulledIfValue, Interaction.signedMult,
    show balanceOf ([] : List (Interaction (ZMod p))) msg = 0 from rfl, add_zero, Prod.snd_zero, neg_zero, ite_self]

private theorem initial_order_ledger (snapshot : MemorySnapshot) (ram : Bool) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p)) (fit) :
    (initialTable snapshot ram rows data fit).interactionsWith (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw =
      (WitnessGeneration.guardedRows (F := ZMod p) (orderedInputs ram (initialInput snapshot ram) 0 rows)).flatMap (edgeValues SnapshotMemoryEnsemble.channelName) := by
  cases ram
  case false =>
    let c := source (p := p) snapshot false
    let inputs := orderedInputs false (initialInput snapshot false) 0 rows
    exact Table.ofInputs_ledger c _ data ((WitnessGeneration.guardedRows_length inputs).trans_le ((orderedInputs_length false _ rows 0) ▸ fit)) (fun _ => trivial)
      _ (edgeValues SnapshotMemoryEnsemble.channelName) (sourceOrder snapshot false)
  case true =>
    let c := source (p := p) snapshot true
    let inputs := orderedInputs true (initialInput snapshot true) 0 rows
    exact Table.ofInputs_ledger c _ data ((WitnessGeneration.guardedRows_length inputs).trans_le ((orderedInputs_length true _ rows 0) ▸ fit)) (fun _ => trivial)
      _ (edgeValues SnapshotMemoryEnsemble.channelName) (sourceOrder snapshot true)

private theorem final_order_ledger (ram : Bool) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p)) (fit) :
    (finalTable ram rows data fit).interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw =
      (WitnessGeneration.guardedRows (F := ZMod p) (finalInputs ram 0 rows)).flatMap (edgeValues OrderedFinalProvider.channelName) :=
  Table.ofInputs_ledger (originalFinal ram) _ data ((WitnessGeneration.guardedRows_length _).trans_le fit) (fun _ => trivial)
    _ (edgeValues OrderedFinalProvider.channelName) (finalOrder ram)

private theorem initial_order_sum (snapshot : MemorySnapshot) (ram : Bool) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p)) (fit) (msg : Array (ZMod p)) :
    balanceOf ((initialTable snapshot ram rows data fit).interactionsWith (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw) msg =
      balanceOf (steps SnapshotMemoryEnsemble.channelName ram 0 rows) msg := by
  rw [initial_order_ledger, WitnessGeneration.guardedRows_balanceOf _ _ _ (zero_edges _ _)]
  rw [active_steps _ _ _ _]
  intro prev r
  cases ram <;> exact ⟨rfl, rfl⟩

private theorem final_order_sum (ram : Bool) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p)) (fit) (msg : Array (ZMod p)) :
    balanceOf ((finalTable ram rows data fit).interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw) msg =
      balanceOf (steps OrderedFinalProvider.channelName ram 0 rows) msg := by
  rw [final_order_ledger, WitnessGeneration.guardedRows_balanceOf _ _ _ (zero_edges _ _)]
  exact congrArg (balanceOf · msg) (active_steps _ _ _ (fun _ _ => ⟨rfl, rfl⟩) 0 rows)

private theorem end_balance (name : String) (distinct : name ≠ "SP1Byte") (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p))
    (reg ram : Table (ZMod p))
    (regSum : ∀ msg, balanceOf (reg.interactionsWith (OrderedBoundary.channel name).toRaw) msg = balanceOf (steps name false 0 rows) msg)
    (ramSum : ∀ msg, balanceOf (ram.interactionsWith (OrderedBoundary.channel name).toRaw) msg = balanceOf (steps name true 0 rows) msg) :
    let ch := OrderedBoundary.channel (p := p) name
    LogUpBalanced ([ch.pushedValue OrderedMemoryEnsemble.startKey, ch.pulledValue OrderedMemoryEnsemble.endKey] ++
      reg.interactionsWith ch.toRaw ++ ram.interactionsWith ch.toRaw ++ (terminalTable name distinct rows data).interactionsWith ch.toRaw) := by
  dsimp only
  intro msg
  simp only [balanceOf_append, regSum, ramSum, terminalTable_ledger, edge_sum]
  have opposite : balanceOf [(OrderedBoundary.channel (p := p) name).pushedValue OrderedMemoryEnsemble.startKey,
      (OrderedBoundary.channel name).pulledValue OrderedMemoryEnsemble.endKey] msg =
      delta OrderedMemoryEnsemble.startKey msg - delta OrderedMemoryEnsemble.endKey msg := by
    have perm := balanceOf_perm (List.Perm.swap (x := (OrderedBoundary.channel (p := p) name).pulledValue OrderedMemoryEnsemble.endKey)
      (y := (OrderedBoundary.channel name).pushedValue OrderedMemoryEnsemble.startKey) (l := [])) (message := msg)
    exact perm.trans (edge_sum name _ _ msg)
  rw [opposite]
  have combined := steps_sum name 0 rows msg
  rw [cursor_zero] at combined
  linear_combination combined

/-- Literal ordered-control ledger at the fixed verifier and its three physical register,
RAM and terminal tables. -/
noncomputable def orderLedger (name : String) (reg ram terminal : Table (ZMod p)) (env : Environment (ZMod p)) : List (Interaction (ZMod p)) :=
  let ch := (OrderedBoundary.channel (p := p) name).toRaw
  let verifier := OrderedBoundaryVerifier.verifierProgram (PublicIO := unit) name OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey
  verifier.circuitOperations.interactionValuesWith ch env ++ reg.interactionsWith ch ++ ram.interactionsWith ch ++ terminal.interactionsWith ch

omit [Fact (2 ^ 25 < p)] in
private theorem verifierValues (name : String) (env : Environment (ZMod p)) :
    let ch := OrderedBoundary.channel (p := p) name
    (OrderedBoundaryVerifier.verifierProgram (PublicIO := unit) name OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey).circuitOperations.interactionValuesWith ch.toRaw env =
      [ch.pushedValue OrderedMemoryEnsemble.startKey, ch.pulledValue OrderedMemoryEnsemble.endKey] := by
  simp only [Verifier.Program.circuitOperations, Verifier.Program.operations, OrderedBoundaryVerifier.verifierProgram]
  rw [Verifier.ofInteractions_values, OrderedBoundaryVerifier.interactionValues]

/-- The original snapshot verifier, both generated providers and the actual seal have zero
signed sum for every cursor value, including for an empty inventory. -/
theorem initial_order_balanced (snapshot : MemorySnapshot) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p))
    (fit : ∀ ram, WitnessGeneration.demandHeight (rows.filter (fun r => r.ram == ram)).length ≤ UInt64.size) (env : Environment (ZMod p)) :
    let table := fun ram => initialTable snapshot ram rows data (fit ram)
    let name := SnapshotMemoryEnsemble.channelName
    LogUpBalanced (orderLedger name (table false) (table true) (terminalTable name (by decide) rows data) env) := by
  dsimp only
  simp only [orderLedger, verifierValues]
  exact end_balance _ _ rows data _ _ (initial_order_sum snapshot false rows data _) (initial_order_sum snapshot true rows data _)

/-- The original finalizer verifier, both generated finalizers and the actual seal close on
the same physical address walk, with the private finalizer channel's own identity. -/
theorem final_order_balanced (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p))
    (fit : ∀ ram, WitnessGeneration.demandHeight (finalInputs ram 0 rows).length ≤ UInt64.size) (env : Environment (ZMod p)) :
    let table := fun ram => finalTable ram rows data (fit ram)
    let name := OrderedFinalProvider.channelName
    LogUpBalanced (orderLedger name (table false) (table true) (terminalTable name (by decide) rows data) env) := by
  dsimp only
  simp only [orderLedger, verifierValues]
  exact end_balance _ _ rows data _ _ (final_order_sum false rows data _) (final_order_sum true rows data _)

omit [Fact (2 ^ 25 < p)] in
private theorem edgeValues_length {Payload : TypeMap} [ProvableType Payload] (name : String)
    (rows : List (OrderedMemoryProvider.RowInput Payload (ZMod p))) :
    (rows.flatMap (edgeValues name)).length = 2 * rows.length := by
  induction rows with
  | nil => rfl
  | cons r rs ih => simp only [List.flatMap_cons, List.length_append, edgeValues, List.length_cons, List.length_nil] at ih ⊢; omega

private theorem initial_order_length (snapshot : MemorySnapshot) (ram : Bool) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p)) (fit) :
    ((initialTable snapshot ram rows data fit).interactionsWith (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw).length =
      2 * WitnessGeneration.demandHeight (rows.filter (fun r => r.ram == ram)).length := by
  rw [initial_order_ledger, edgeValues_length, WitnessGeneration.guardedRows_length, orderedInputs_length]

private theorem final_order_length (ram : Bool) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p)) (fit) :
    ((finalTable ram rows data fit).interactionsWith (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw).length =
      2 * WitnessGeneration.demandHeight (rows.filter (fun r => r.ram == ram)).length := by
  rw [final_order_ledger, edgeValues_length, WitnessGeneration.guardedRows_length, finalInputs, orderedInputs_length]

/-- Exact combined physical cost of either private order channel. Each physical provider row,
the verifier and the terminal contributes a literal pull/push pair. -/
def orderCost {F : Type} (rows : List (Terminal F)) : ℕ :=
  4 + 2 * WitnessGeneration.demandHeight (rows.filter (fun r => r.ram == false)).length +
    2 * WitnessGeneration.demandHeight (rows.filter (fun r => r.ram == true)).length

/-- The incoming and final control channel counts both coincide with the physical cost of
the common inventory, including padding and both fixed endpoints. -/
theorem orderLedger_lengths (snapshot : MemorySnapshot) (rows : List (Terminal (ZMod p))) (data : ProverData (ZMod p))
    (fit : ∀ ram, WitnessGeneration.demandHeight (rows.filter (fun r => r.ram == ram)).length ≤ UInt64.size)
    (fitFinal : ∀ ram, WitnessGeneration.demandHeight (finalInputs ram 0 rows).length ≤ UInt64.size) (env : Environment (ZMod p)) :
    let first := fun ram => initialTable snapshot ram rows data (fit ram)
    let last := fun ram => finalTable ram rows data (fitFinal ram)
    let left := SnapshotMemoryEnsemble.channelName
    let right := OrderedFinalProvider.channelName
    (orderLedger left (first false) (first true) (terminalTable left (by decide) rows data) env).length = orderCost rows ∧
      (orderLedger right (last false) (last true) (terminalTable right (by decide) rows data) env).length = orderCost rows := by
  dsimp only
  constructor <;> simp only [orderLedger, verifierValues, List.length_append, initial_order_length, final_order_length,
    terminalTable_ledger, List.length_cons, List.length_nil, orderCost] <;> omega

/-- The two concrete order verifiers and seals for the sparse register/RAM construction.
Each signed cursor ledger closes at its fixed endpoints and has the exact combined row cost. -/
theorem compiled_order (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess) (requested : List ℕ)
    (guest : ∀ a ∈ stream, ∀ cell, a.loc = .ram cell → NativeLayout.guestMemory.Contains (MemLoc.ram cell).busAddress)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (env : Environment (ZMod p)) :
    let rows := terminals snapshot stream requested data hint
    let start := SnapshotMemoryEnsemble.channelName
    let finish := OrderedFinalProvider.channelName
    let startSeal := terminalTable start (by decide) rows data
    let endSeal := terminalTable finish (by decide) rows data
    let first := fun ram => initialTable snapshot ram rows data (terminal_count_fit ram snapshot stream requested (canonical_addresses guest) data hint)
    let last := fun ram => finalTable ram rows data (terminals_fit ram snapshot stream requested (canonical_addresses guest) data hint)
    let incoming := orderLedger start (first false) (first true) startSeal env
    let outgoing := orderLedger finish (last false) (last true) endSeal env
    startSeal.Constraints ∧ startSeal.Guarantees ∧ endSeal.Constraints ∧ endSeal.Guarantees ∧
      LogUpBalanced incoming ∧ LogUpBalanced outgoing ∧ incoming.length = orderCost rows ∧ outgoing.length = orderCost rows := by
  have bounded := fun r hr => (terminals_valid snapshot stream requested guest data hint r hr).key_lt
  have start := terminalTable_valid SnapshotMemoryEnsemble.channelName (by decide) _ bounded data
  have finish := terminalTable_valid OrderedFinalProvider.channelName (by decide) _ bounded data
  let fit := fun ram => terminal_count_fit ram snapshot stream requested (canonical_addresses guest) data hint
  let fitFinal := fun ram => terminals_fit ram snapshot stream requested (canonical_addresses guest) data hint
  exact ⟨start.1, start.2, finish.1, finish.2, initial_order_balanced snapshot _ data fit env, final_order_balanced _ data fitFinal env,
    orderLedger_lengths snapshot _ data fit fitFinal env⟩

end SP1Clean.WriteProbe.SparseBoundary
