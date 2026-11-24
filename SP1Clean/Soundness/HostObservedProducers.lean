import SP1Clean.Soundness.HostObservedLedger
import SP1Clean.Soundness.HostFinalMemoryInventory
import SP1Clean.Soundness.LocalCoreState
import SP1Clean.Soundness.OrdinaryObservation

/-! # Recover ordinary receipt producers from the physical CPU witness

The 25 protected instruction tables retain all arrays through the host, final-memory and
local-core projections. Decoding their guarded emissions in registration order identifies
precisely the ordinary successors consumed by the observation table.
-/

namespace SP1Clean.Soundness.HostObserved
open Circuit Air.Flat Channels Semantics
open SP1Clean.OrdinaryObservation (Inputs)
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}

attribute [local irreducible] ensemble HostFinalMemory.ensemble HostFinalMemory.coreWitness HostOrdinaryReceipts.ensemble

/-- Projecting the native supervisor retains all physical source arrays in registration order. -/
theorem baseWitness_rows (witness : EnsembleWitness (ensemble image source target final)) :
    (baseWitness witness).tables.map (·.table) = witness.tables.map (·.table) := by
  let produced := witness.withEnsemble (producers image source target final) (by simp only [ensemble, ClosedVerifier.withInteractions])
  exact HostOrdinaryReceipts.baseWitness_rows produced

/-- All table arrays before the legacy HALT retain their physical indices when projecting
from the native host supervisor to the execution core. -/
theorem core_rows_before_halt (witness : EnsembleWitness (ensemble image source target final)) (i : Fin 57)
    (h : i.val < (HostFinalMemory.coreWitness (baseWitness witness)).tables.length)
    (h' : i.val < witness.tables.length) :
    ((HostFinalMemory.coreWitness (baseWitness witness)).tables[i.val]'h).table = (witness.tables[i.val]'h').table := by
  let base := baseWitness witness
  let older := HostFinalMemory.baseWitness base
  let projected := HostHintQueueBoundary.projected older
  have first := HostLocalCore.localWitness_table projected ⟨i.val, by omega⟩ (by change 58 ≠ i.val; omega)
  have same := (HostFinalMemory.baseWitness_rows base).trans (baseWitness_rows witness)
  have ho : i.val < older.tables.length := by
    have lengths := congrArg List.length same
    simp only [List.length_map] at lengths
    exact lengths.symm ▸ h'
  have hp : i.val < projected.tables.length := by
    have lengths : projected.tables.length = older.tables.length := List.length_set ..
    exact lengths.symm ▸ ho
  have before : (projected.tables[i.val]'hp).table = (older.tables[i.val]'ho).table := by
    change ((older.tables.set 57 _)[i.val]'hp).table = _
    exact congrArg Table.table (List.getElem_set_ne (l := older.tables) (by omega : 57 ≠ i.val) _)
  have arrays := List.getElem_of_eq same (i := i.val) (by simpa only [List.length_map] using ho)
  simp only [List.getElem_map] at arrays
  simpa only [HostFinalMemory.coreWitness] using first.trans (before.trans arrays)

private theorem decode_zip (chips : List (SupportedChip p)) (tables : List (Table (ZMod p))) :
    decodeInstructionTables chips tables =
      (chips.zip tables).flatMap (fun pair => pair.2.table.map (fun physical => ⟨pair.1, physical⟩)) := by
  induction chips generalizing tables with
  | nil => rfl
  | cons chip rest ih => cases tables with
    | nil => rfl
    | cons table tail =>
      simp only [decodeInstructionTables, List.zip_cons_cons, List.flatMap_cons, ih]

/-- Every installed instruction occurrence, with its original multiplicity, is a receipt from
the same decoded row that the local execution proof uses. -/
theorem decoded_receipts (witness : EnsembleWitness (ensemble image source target final)) :
    let core := HostFinalMemory.coreWitness (baseWitness witness)
    ((witness.tables.drop 7).take 25).flatMap (·.interactionsWith InstructionReceipt.channel.toRaw) =
      (LocalCore.instructionRows core).map (fun row =>
        let chipRow := row.toChipRow core.data
        InstructionReceipt.channel.pushedIfValue chipRow.is_real (statePushMessage chipRow)) := by
  let core := HostFinalMemory.coreWitness (baseWitness witness)
  have hw := witness.same_length.symm.trans (tables_length (image := image) (source := source) (target := target) (final := final))
  have hc : core.tables.length = 61 := core.same_length.symm.trans (LocalCore.tables_length image source)
  have sz : (LocalCore.instructionTables core).length = 25 := by simp [LocalCore.instructionTables, hc]
  change _ = (LocalCore.instructionRows core).map _
  rw [LocalCore.instructionRows, decode_zip, List.map_flatMap]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.ext_getElem
  · simp [List.length_zip, supportedChips_length, hw, sz]
  · intro j hx hy
    have bound : j < 25 := by simp only [List.length_map, List.length_take, List.length_drop, hw] at hx; omega
    let i : Fin 25 := ⟨j,bound⟩
    let produced := witness.withEnsemble (producers image source target final) (by simp only [ensemble, ClosedVerifier.withInteractions])
    have receipts := HostOrdinaryReceipts.instructionTable_receipts i produced
    change (witness.tables[7 + j]'(by omega)).interactionsWith InstructionReceipt.channel.toRaw =
      (witness.tables[7 + j]'(by omega)).table.map _ at receipts
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_zip, LocalCore.instructionTables,
      supportedChips, List.map_map, Function.comp_def]
    rw [receipts, core_rows_before_halt witness ⟨7 + j, by omega⟩ (by change 7 + j < core.tables.length; omega) (by change 7 + j < witness.tables.length; omega)]
    apply List.map_congr_left
    intro physical _
    dsimp only [DecodedInstructionRow.toChipRow]
    rw [(supportedChipFor (p := p) (InstructionChipId.all[j]'(by rw [InstructionChipId.all_length]; exact bound))).decodeRow_setData
      produced.data core.data]

/-- The 25 producer tables and the active consumer rows describe the same complete multiset
of successor messages, including repeated PCs at different times. -/
theorem active_receipts (witness : EnsembleWitness (ensemble image source target final))
    (checked : witness.Constraints) (balanced : DeclarationsOpen witness)
    (consumerSpec : (observationTable witness 0).Spec) :
    let core := HostFinalMemory.coreWitness (baseWitness witness)
    ((LocalCore.activeInstructionRows core).map (fun row => statePushMessage (row.toChipRow core.data))).Perm
      ((OrdinaryObservation.activeRows (observationTable witness 0) witness.data).map Inputs.receipt) := by
  let core := HostFinalMemory.coreWitness (baseWitness witness)
  let observed := observationTable witness 0
  have registered : observed.component = OrdinaryObservation.consumer := (observationSlot 0).table_component witness
  have membership : observed ∈ witness.tables := (observationSlot 0).table_mem witness
  have channelIn : InstructionReceipt.channel.toRaw ∈ (ensemble image source target final).channels := by
    apply (ensemble image source target final).tables_channels observed.component (witness.component_mem_tables_of_mem membership)
    rw [registered]
    apply List.mem_append_right
    exact List.mem_cons_self
  have ledger := balanced _ channelIn (by simp [InstructionReceipt.channel, CommitmentDeclaration.channel, Channel.toRaw])
  change BalancedInteractions (witness.interactionsWith InstructionReceipt.channel.toRaw) at ledger
  rw [receipt_rows, decoded_receipts] at ledger
  have coreChecks : core.Constraints := by
    unfold core HostFinalMemory.coreWitness
    apply HostLocalCore.localWitness_constraints
    apply HostHintQueueBoundary.projected_constraints
    exact HostFinalMemory.baseWitness_constraints _ (baseWitness_constraints witness checked)
  have producer (row : DecodedInstructionRow p) (member : row ∈ LocalCore.instructionRows core) :
      IsBool (row.toChipRow core.data).is_real :=
    supportedChip_selectorConstraintShape row.chip (decodedInstructionRows_chip_mem (core.tables.drop 7) member)
      core.data row.physical (LocalCore.instructionRows_constraints core coreChecks row member)
  have consumer := OrdinaryObservation.rows_spec observed witness.data registered consumerSpec
  have matched := InstructionReceipt.channel.gated_perm_of_balanced (LocalCore.instructionRows core)
      (fun row => (row.toChipRow core.data).is_real) (fun row => statePushMessage (row.toChipRow core.data))
      (OrdinaryObservation.rows observed witness.data) Prod.snd (fun row => row.1.receipt) producer
      (fun row member => (consumer row member).1) ledger
  simp only [OrdinaryObservation.activeRows, LocalCore.activeInstructionRows, List.map_map, Function.comp_def]
  apply List.Perm.trans ?_ matched
  apply List.Perm.of_eq
  congr 1
  apply List.filter_congr
  intro row _
  exact decide_eq_decide.mpr Iff.rfl
end SP1Clean.Soundness.HostObserved
