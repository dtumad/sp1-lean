import SP1Clean.Soundness.HostHintReadPartition
import SP1Clean.Soundness.HostHintReadLocalPermissions
import SP1Clean.Soundness.HostHintReadLocalRecords
import SP1Clean.Soundness.HostHintReadLocalExecution
import SP1Clean.Soundness.HostHintReadLocalQueue
import ToClean.Air.EnsembleBuild
import SP1CleanTest.Core.HintReadFixtures
import SP1Clean.Proofs.Chips.HostHintReadChip.Populate
import ToClean.Air.TableBuild

/-! # Executed shared HINT_READ table selection

Build the actual handler and consumer tables for different nodes, lengths, destinations, and
clocks. Check their computed cells and cursor ledger, then decode each selected physical table
back to the independent padded-write inventory. Installed permission and record-source tests
check their actual whole-witness ledgers and fixed lookups. These remain subsystem regressions:
the other channels and complete mixed execution are not claimed satisfied by these fixtures.
-/

namespace SP1CleanTest.Core.HostHintReadPartition

open Circuit Air.Flat SP1Clean Model.Core HintQueue Soundness HostChecks

private abbrev Fp := ZMod SP1Prime

private def hints : List Bytes := [HintReadFixtures.bytes 16, HintReadFixtures.bytes 8, []]

private def call (head previous now address : ℕ) : HostHintReadChip.Inputs Fp :=
  let store := (ofList hints).1
  let queue := (decode? store head).getD []
  let bytes := queue.headD []
  let host : HostState := { io := ⟨queue, []⟩ }
  let context : HostReadContext :=
    ⟨fun index => if index == 5 then some 241
      else if index == 10 then some (BitVec.ofNat 64 address)
      else if index == 11 then some (BitVec.ofNat 64 bytes.length) else none, fun _ => none⟩
  let executed := (host.run ⟨{ readOnly := fun _ => false }, SP1Prime⟩ context).getD
    ⟨.hintRead, 0, 0, 0, ⟨host, none⟩⟩
  HostHintReadChip.populate store head previous now executed

private def calls : List (HostHintReadChip.Inputs Fp) :=
  [call 3 0 1 65536, call 2 1 265 131064, call 1 265 (2 ^ 24 + 1) (2 ^ 48 - 8)]

private def words (call : HostHintReadChip.Inputs Fp) : List HintReadFixtures.Row :=
  let node := (node? (ofList hints).1 (Address.toNat call.node.pointer)).getD default
  (List.range (wordCount node.bytes)).map fun index =>
    let address := Address.ofNat (p := SP1Prime) (Address.toNat call.span.start + index * 8)
    let word := WordRecord.encode (p := SP1Prime) (Address.toNat call.node.pointer) node.bytes index
    let ram := HostRamAccessChip.populate ⟨0, 0, address[0], address[1], address[2], HintReadFixtures.oldWord⟩
      call.call.clk_high (call.call.clk_low.val % 65536 : ℕ) (call.call.clk_low.val / 65536 : ℕ) word.value
    let last := decide (index + 1 = wordCount node.bytes)
    (last, HintReadWordChip.populate last ram word.pointer word.index)

private def handlers (calls : List (HostHintReadChip.Inputs Fp)) : Table Fp :=
  Table.build HostHintReadCoverage.handler calls (fun _ _ => #[]) (ProverHint.empty Fp)

private def consumers (rows : List HintReadFixtures.Row) : List (Table Fp) :=
  HintReadCoverage.variants.map fun last => Table.build (HintReadCoverage.view last).component
    ((rows.filter (fun row => row.1 == last)).map (·.2)) (fun _ _ => #[]) (ProverHint.empty Fp)

private def checked (table : Table Fp) : Bool × Ledger :=
  let evaluated := table.table.map fun row =>
    let env := table.environment row
    let operations := table.component.rowOperations.toFlat
    let assertions := operations.all fun operation =>
      match operation with
      | .assert expression => env expression == 0
      | .lookup _ => false
      | _ => true
    let cursor := (FlatOperation.interactions operations).filterMap fun interaction =>
      if interaction.channel.name == "sp1.native.hint_read_state" then
        some (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult) else none
    (assertions, cursor)
  (evaluated.all (·.1), evaluated.flatMap (·.2))

private def shared (calls : List (HostHintReadChip.Inputs Fp)) (rows : List HintReadFixtures.Row) : Bool :=
  let checked := (handlers calls :: consumers rows).map checked
  checked.all (·.1) && HintReadFixtures.balanced (checked.flatMap (·.2))

private def unique (table : Table Fp) : Bool :=
  decide (((table.table.map table.environment).map Soundness.HostHintReadPartition.callClock).Nodup)

/-- Interleaved calls and reversed physical rows retain complete per-call writes across clock carries. -/
theorem sharedCalls :
    let table := handlers calls
    let rows := (calls.flatMap words).reverse
    let tables := consumers rows
    shared calls rows = true ∧ unique table = true ∧
      (table.table.map table.environment).all (fun env =>
        let call := HostHintReadCoverage.input env
        let key := Soundness.HostHintReadPartition.callClock env
        let selected := Soundness.HostHintReadPartition.tablesFor key tables
        let actual := ((node? (ofList hints).1 (Address.toNat call.node.pointer)).getD default).bytes
        let inventory := (HintReadCoverage.variants.zip selected).flatMap fun (last, table) =>
          table.table.map fun row => HintReadWrites.produced (last, table.environment row)
        HintReadFixtures.balanced
          ((checked (handlers [call])).2 ++ (selected.map checked).flatMap (·.2)) &&
          inventory.mergeSort (fun a b => a.1 ≤ b.1) == wordWrites (Address.toNat call.span.start) actual) = true := by
  native_decide

/-- A missing handler or consumer cannot borrow a different event's cursor endpoints. -/
theorem missingAndOrphanRows :
    let rows := calls.flatMap words
    shared (calls.drop 1) rows = false ∧ shared calls (rows.drop 1) = false ∧
      shared calls (rows ++ words (call 3 0 9 65536)) = false ∧
      ((Soundness.HostHintReadPartition.tablesFor (0, 9) (consumers rows)).map
        (fun table => table.table.length)) = [0, 0] := by native_decide

/-- Duplicating complete calls preserves cursor balance but violates the required event uniqueness. -/
theorem duplicateHandlers :
    let doubled := calls ++ calls
    shared doubled (doubled.flatMap words) = true ∧ unique (handlers doubled) = false := by native_decide

private def image : ProgramImage := ⟨[(65536, 0x73), (131072, 0x73)], 65536, []⟩

private def source : ExecutionSnapshot :=
  { sail := { registers := (Soundness.Target.configuredState 65536).regs, memory := image.initialMemory }
    host := {}, clock := 1 }

private def installedTable (calls : List (HostHintReadChip.Inputs Fp)) (rows : List HintReadFixtures.Row)
    (permissions : List (WritePermissionProvider.Inputs Fp)) (component : Component Fp) (index : ℕ) : Table Fp :=
  let table := if index == 59 then Table.build ⟨WritePermissionProvider.circuit image⟩ permissions
      (fun _ _ => #[]) (ProverHint.empty Fp)
    else if index == 60 then handlers calls
    else if index == 81 then (consumers rows)[0]'(by simp [consumers, HintReadCoverage.variants])
    else if index == 82 then (consumers rows)[1]'(by simp [consumers, HintReadCoverage.variants])
    else Table.build component [] (fun _ _ => #[]) (ProverHint.empty Fp)
  table.withComponent component

private theorem installedTable_component (calls : List (HostHintReadChip.Inputs Fp)) (rows : List HintReadFixtures.Row)
    (permissions : List (WritePermissionProvider.Inputs Fp)) (component : Component Fp) (index : ℕ) : (installedTable calls rows permissions component index).component = component := rfl

private theorem installedTable_data (calls : List (HostHintReadChip.Inputs Fp)) (rows : List HintReadFixtures.Row)
    (permissions : List (WritePermissionProvider.Inputs Fp)) (component : Component Fp) (index : ℕ) : (installedTable calls rows permissions component index).data = (fun _ _ => #[]) := by
  simp only [installedTable, Table.withComponent]
  split_ifs <;> rfl

/-- A physical ensemble witness used to test cursor extraction. Other channels are deliberately
not claimed balanced: source authentication and CPU instruction construction are separate tests. -/
private def installed (calls : List (HostHintReadChip.Inputs Fp)) (rows : List HintReadFixtures.Row)
    (permissions : List (WritePermissionProvider.Inputs Fp) := []) :
    EnsembleWitness (HostHintReadLocal.ensemble (p := SP1Prime) image source HostCallReceivers.available [] []) :=
  let ensemble := HostHintReadLocal.ensemble (p := SP1Prime) image source HostCallReceivers.available [] []
  EnsembleWitness.ofTables ensemble (ensemble.tables.zipIdx.map fun (component, index) =>
    installedTable calls rows permissions component index) (fun _ _ => #[])
    (valueFromOffset SP1PublicIO 0 (Environment.fromArray #[] (fun _ _ => #[])))
    (by simp only [List.map_map, Function.comp_def, installedTable_component, List.zipIdx_map_fst])
    (by
      intro table member
      obtain ⟨⟨component, index⟩, _, rfl⟩ := List.mem_map.mp member
      exact installedTable_data calls rows permissions component index)

/-- The installed 83-table assembly retains exactly the handler and both physical word tables.
Its complete cursor balances with reversed multi-call rows; missing handlers, missing words,
and orphan consumers fail at the same whole-witness channel boundary. -/
theorem installedCursor :
    let rows := (calls.flatMap words).reverse
    let witness := installed calls rows
    let handler := HostHintReadLocal.handlerTable witness
    let tables := HostHintReadLocal.wordTables witness
    let cursor := (witness.allTables.map checked).flatMap (·.2)
    witness.tables.length = 83 ∧ handler.table = (handlers calls).table ∧
      tables.map (·.table) = (consumers rows).map (·.table) ∧
      (handler :: tables).all (fun table => (checked table).1) = true ∧
      cursor = (checked handler).2 ++ (tables.map checked).flatMap (·.2) ∧
      HintReadFixtures.balanced cursor = true ∧
      HintReadFixtures.balanced (((installed (calls.drop 1) rows).allTables.map checked).flatMap (·.2)) = false ∧
      HintReadFixtures.balanced (((installed calls (rows.drop 1)).allTables.map checked).flatMap (·.2)) = false ∧
      HintReadFixtures.balanced (((installed calls (rows ++ words (call 3 0 9 65536))).allTables.map checked).flatMap (·.2)) = false := by
  native_decide

private def permissionRows (rows : List HintReadFixtures.Row) (forge := false) :
    List (WritePermissionProvider.Inputs Fp) :=
  rows.flatMap fun row => (List.range 8).filterMap fun index =>
    let address := Address.toNat row.2.address + index
    match WritePermissionProvider.populate? (p := SP1Prime) image address with
    | some input => some input
    | none => if forge then (WritePermissionProvider.populate? (p := SP1Prime) image (address - 8)).map
        (fun input => { input with address := Address.ofNat address }) else none

private def permissionRowsChecked (rows : List (WritePermissionProvider.Inputs Fp)) : Bool :=
  rows.all fun input =>
    (HostChecks.evaluateProgram (WritePermissionProvider.main image (varFromOffset WritePermissionProvider.Inputs 0))
      (toElements input).toList none [FiniteLookup.ofStatic image.writePermissionTable]).1

private def permissionLedger (witness : EnsembleWitness
    (HostHintReadLocal.ensemble (p := SP1Prime) image source HostCallReceivers.available [] [])) : Ledger :=
  witness.allTables.flatMap fun table => table.table.flatMap fun physical =>
    let env := table.environment physical
    (FlatOperation.interactions table.component.rowOperations.toFlat).filterMap fun interaction =>
      if interaction.channel.name == "SP1WritePermission" then
        some (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult) else none

/-- Installed permissions cover the padding and final native RAM cell. Dropping a permission fails
balance. Padding into ROM keeps cursor balance but lacks permissions; forged provider rows restore
that balance only by violating the fixed provider's actual assertions/lookup. -/
theorem installedPermissions :
    let permittedCalls := [call 2 1 265 131056, call 1 265 (2 ^ 24 + 1) (2 ^ 48 - 8)]
    let rows := permittedCalls.flatMap words
    let permissions := permissionRows rows
    let writable := installed permittedCalls rows permissions
    let romCalls := [call 2 1 265 131064]
    let romRows := romCalls.flatMap words
    let rom := installed romCalls romRows (permissionRows romRows)
    let forged := permissionRows romRows true
    permissionRowsChecked permissions = true ∧
      HintReadFixtures.balanced (permissionLedger writable) = true ∧
      HintReadFixtures.balanced (permissionLedger (installed permittedCalls rows (permissions.drop 1))) = false ∧
      HintReadFixtures.balanced ((rom.allTables.map checked).flatMap (·.2)) = true ∧
      HintReadFixtures.balanced (permissionLedger rom) = false ∧
      HintReadFixtures.balanced (permissionLedger (installed romCalls romRows forged)) = true ∧
      permissionRowsChecked forged = false := by native_decide

private def sourceTableAt (actual : List Bytes) (calls : List (HostHintReadChip.Inputs Fp))
    (rows : List HintReadFixtures.Row) (nodes : List (NodeRecord Fp)) (records : List (WordRecord Fp))
    (component : Component Fp) (index : ℕ) : Table Fp :=
  let table := if index == 83 then Table.build ⟨HostHintQueue.source actual⟩ nodes
      (fun _ _ => #[]) (ProverHint.empty Fp)
    else if index == 84 then Table.build ⟨HostHintQueue.sourceWord actual⟩ records
      (fun _ _ => #[]) (ProverHint.empty Fp)
    else installedTable calls rows [] component index
  table.withComponent component

private theorem sourceTableAt_component (actual : List Bytes) (calls : List (HostHintReadChip.Inputs Fp))
    (rows : List HintReadFixtures.Row) (nodes : List (NodeRecord Fp)) (records : List (WordRecord Fp))
    (component : Component Fp) (index : ℕ) :
    (sourceTableAt actual calls rows nodes records component index).component = component := rfl

private theorem sourceTableAt_data (actual : List Bytes) (calls : List (HostHintReadChip.Inputs Fp))
    (rows : List HintReadFixtures.Row) (nodes : List (NodeRecord Fp)) (records : List (WordRecord Fp))
    (component : Component Fp) (index : ℕ) :
    (sourceTableAt actual calls rows nodes records component index).data = (fun _ _ => #[]) := by
  simp only [sourceTableAt, Table.withComponent]
  split_ifs
  · rfl
  · rfl
  · exact installedTable_data calls rows [] component index

private def recordSnapshot (actual : List Bytes) : ExecutionSnapshot :=
  { source with host := { source.host with io := { source.host.io with hints := actual } } }

private def withSources (actual : List Bytes) (calls : List (HostHintReadChip.Inputs Fp))
    (rows : List HintReadFixtures.Row) (nodes : List (NodeRecord Fp)) (records : List (WordRecord Fp)) :
    EnsembleWitness (HostHintReadLocal.ensemble (p := SP1Prime) image (recordSnapshot actual)
      HostCallReceivers.available (HostHintReadLocal.sourceResources actual) []) :=
  let ensemble := HostHintReadLocal.ensemble (p := SP1Prime) image (recordSnapshot actual) HostCallReceivers.available
    (HostHintReadLocal.sourceResources actual) []
  EnsembleWitness.ofTables ensemble (ensemble.tables.zipIdx.map fun (component, index) =>
    sourceTableAt actual calls rows nodes records component index) (fun _ _ => #[])
    (valueFromOffset SP1PublicIO 0 (Environment.fromArray #[] (fun _ _ => #[])))
    (by simp only [List.map_map, Function.comp_def, sourceTableAt_component, List.zipIdx_map_fst])
    (by
      intro table member
      obtain ⟨⟨component, index⟩, _, rfl⟩ := List.mem_map.mp member
      exact sourceTableAt_data actual calls rows nodes records component index)

private def recordLedger (tables : List (Table Fp)) : Ledger :=
  tables.flatMap fun table => table.table.flatMap fun physical =>
    let env := table.environment physical
    (FlatOperation.interactions table.component.rowOperations.toFlat).filterMap fun interaction =>
      if interaction.channel.name == "sp1.native.hint_node" || interaction.channel.name == "sp1.native.hint_word" then
        some (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult) else none

private def sourceRowsChecked (actual : List Bytes) (nodes : List (NodeRecord Fp))
    (records : List (WordRecord Fp)) : Bool :=
  nodes.all (fun node => (evaluateProgram
    (HostHintQueue.sourceMain actual (varFromOffset NodeRecord 0)) (toElements node).toList none
    [FiniteLookup.ofStatic (sourceTable actual)]).1) &&
  records.all (fun record => (evaluateProgram
    (HostHintQueue.sourceWordMain actual (varFromOffset WordRecord 0)) (toElements record).toList none
    [FiniteLookup.ofStatic (sourceWordTable actual)]).1)

/-- The installed fixed sources authenticate every handler/consumer request, with duplicate demand
and reversed physical rows. Missing providers fail balance; changing fixed bytes preserves the
claimed ledger but fails the source lookup. Other channels are outside this regression. -/
theorem installedRecords :
    let rows := (calls.flatMap words).reverse
    let nodes := calls.map (·.node)
    let records := calls.map (·.endStep.word) ++ rows.map (fun row => (row.2.step row.1).word)
    let witness := withSources hints calls rows nodes records
    let changed := [[99] ++ (HintReadFixtures.bytes 16).drop 1, HintReadFixtures.bytes 8, []]
    witness.tables.length = 85 ∧ sourceRowsChecked hints nodes records = true ∧
      HintReadFixtures.balanced (recordLedger witness.allTables) = true ∧
      HintReadFixtures.balanced (recordLedger (withSources hints calls rows (nodes.drop 1) records).allTables) = false ∧
      HintReadFixtures.balanced (recordLedger (withSources hints calls rows nodes (records.drop 1)).allTables) = false ∧
      HintReadFixtures.balanced (recordLedger (withSources changed calls rows nodes records).allTables) = true ∧
      sourceRowsChecked changed nodes records = false := by native_decide

/-- Semantic 64-bit agreement does not establish canonical field limbs. -/
theorem noncanonicalNodeLength :
    let node := (call 3 0 1 65536).node
    let forged : NodeRecord Fp := { node with length := node.length.set 3 (node.length[3] + 65536) }
    Word.toBitVec64 forged.length = Word.toBitVec64 node.length ∧
      sourceRowsChecked hints [node] [] = true ∧ sourceRowsChecked hints [forged] [] = false := by native_decide

/-- Future nodes can have identical bytes and valid source records. Complete record balance still
does not authorize their use by an earlier call: its actual cursor ledger rejects the substitution. -/
theorem futureNodeConsumers :
    let earlier := call 3 0 1 65536
    let actual := HintReadFixtures.bytes 16 :: hints
    let rows := (words earlier).map fun row => (row.1, { row.2 with pointer := Address.ofNat 4 })
    let nodes := [earlier.node]
    let records := earlier.endStep.word :: rows.map (fun row => (row.2.step row.1).word)
    node? (ofList hints).1 4 = none ∧
      node? (ofList actual).1 4 = some ⟨HintReadFixtures.bytes 16, 3⟩ ∧
      sourceRowsChecked actual nodes records = true ∧
      HintReadFixtures.balanced (recordLedger (withSources actual [earlier] rows nodes records).allTables) = true ∧
      (consumers rows).all (fun table => (checked table).1) = true ∧
      shared [earlier] (words earlier) = true ∧ shared [earlier] rows = false := by native_decide

private def queueLedger (tables : List (Table Fp)) : Ledger :=
  tables.flatMap fun table => table.table.flatMap fun physical =>
    let env := table.environment physical
    (FlatOperation.interactions table.component.rowOperations.toFlat).filterMap fun interaction =>
      if interaction.channel.name == "sp1.native.hint_queue_state" then
        some (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult) else none

private def queueEndpoint (state : HostHintQueue.State Fp) (multiplicity : Fp) : String × List Fp × Fp :=
  ("sp1.native.hint_queue_state", (toElements state).toList, multiplicity)

/-- Active fixed-source fixtures satisfy their record subsystem but lack queue endpoints.
The explicit pair closes only that ledger; forged final heads or reset allocation frontiers fail. -/
theorem missingQueueEndpoints :
    let rows := (calls.flatMap words).reverse
    let nodes := calls.map (·.node)
    let records := calls.map (·.endStep.word) ++ rows.map (fun row => (row.2.step row.1).word)
    let witness := withSources hints calls rows nodes records
    let actual := queueLedger witness.allTables
    let initial := (call 3 0 1 65536).previous
    let final := (call 1 265 (2 ^ 24 + 1) (2 ^ 48 - 8)).next
    sourceRowsChecked hints nodes records = true ∧
      HintReadFixtures.balanced (recordLedger witness.allTables) = true ∧
      HintReadFixtures.balanced actual = false ∧
      HintReadFixtures.balanced (queueEndpoint initial 1 :: queueEndpoint final (-1) :: actual) = true ∧
      HintReadFixtures.balanced (queueEndpoint initial 1 ::
        queueEndpoint { final with head := Address.ofNat 1 } (-1) :: actual) = false ∧
      HintReadFixtures.balanced (queueEndpoint initial 1 ::
        queueEndpoint { final with allocated := Address.ofNat 0 } (-1) :: actual) = false := by native_decide

end SP1CleanTest.Core.HostHintReadPartition
