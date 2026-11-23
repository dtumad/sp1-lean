import SP1Clean.Soundness.WriteAccessInventory

/-! # Reading the actual WRITE supply inputs from the installed source tables

Every original predecessor contributes a typed record at its original gate. The order here
is the order of the physical ledger, including aliased records and inactive occurrences.
-/

namespace SP1Clean.WriteProbe.AccessInventory

open Circuit Air.Flat Soundness Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
/-- Use the input type installed by the ordinary chip registry. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := p) id).kind.Inputs :=
  (supportedChipFor (p := p) id).kind.provableInputs

/-- The source rows are read from the original physical cells, before adding the private bus. -/
noncomputable def rowRecords (id : Source) (env : Environment (ZMod p)) : List (ZMod p × Readback (ZMod p)) :=
  match id with
  | .ordinary instruction =>
    let layout := OrdinarySources.layout (p := p) instruction
    let input := varFromOffset (supportedChipFor (p := p) instruction).kind.Inputs 0
    (layout.pulls input (size (supportedChipFor (p := p) instruction).kind.Inputs)).map
      fun i => (env i.mult, AccessSupply.readback (eval env (layout.incoming input)) (eval env i.msg))
  | .host family =>
    let input := varFromOffset (HostSources.original (p := p) family).Input 0
    let offset := size (HostSources.original (p := p) family).Input
    (HostSources.sites family).map fun site => (env (site.gate input offset),
      eval env (AccessSupply.atClock (HostSources.clock family input) (site.message input offset)))
  | .refresh =>
    let input := valueFromOffset MemoryBumpChip.Inputs 0 env
    [(input.is_real, refreshReadback input)]
  | .finalizer ram =>
    [((valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env).2, finalReadback (finalRecordAt ram env))]

/-- Source input order agrees exactly with the messages and multiplicities Clean evaluates. -/
theorem table_records (id : Source) (table : Table (ZMod p)) (registered : table.component = original id) :
    (publish id table registered).interactionsWith readbackChannel.toRaw =
      (table.table.flatMap fun row => rowRecords id (table.environment row)).map
        fun r => readbackChannel.pushedIfValue r.1 r.2 := by
  cases id with
  | ordinary instruction =>
    simp only [publish, OrdinarySources.publish, Table.interactionsWith, Table.withComponent, Table.environment,
      OrdinarySources.row_receipts, rowRecords, List.map_flatMap, List.map_map, Function.comp_def]
  | host family =>
    simp only [publish, HostSources.publish, Table.interactionsWith, Table.withComponent, Table.environment,
      HostSources.row_receipts, rowRecords, List.map_flatMap, List.map_map, Function.comp_def]
  | refresh =>
    rw [show (publish .refresh table registered).interactionsWith readbackChannel.toRaw = _ from
      publishRefresh_receipts table registered]
    simp only [rowRecords, ← List.map_eq_flatMap, List.map_map, Function.comp_def]
  | finalizer ram =>
    rw [show (publish (.finalizer ram) table registered).interactionsWith readbackChannel.toRaw = _ from
      publishFinal_receipts ram table registered]
    simp only [rowRecords, ← List.map_eq_flatMap, List.map_map, Function.comp_def]

/-- Flatten the genuine 31 source families in physical table, row and access-site order. -/
noncomputable def records (raw : Source → Table (ZMod p)) : List (ZMod p × Readback (ZMod p)) :=
  sources.flatMap fun id => (raw id).table.flatMap fun row => rowRecords id ((raw id).environment row)

theorem ledger_records (raw : Source → Table (ZMod p)) (registered : ∀ id, (raw id).component = original id)
    (supply : Table (ZMod p)) :
    ledger raw registered supply = supply.interactionsWith readbackChannel.toRaw ++
      (records raw).map (fun r => readbackChannel.pushedIfValue r.1 r.2) := by
  simp only [ledger, List.flatMap_cons, List.flatMap_map, table_records, records, List.map_flatMap]

end SP1Clean.WriteProbe.AccessInventory
