import SP1Clean.Soundness.HostLocalCorePermissions
import SP1Clean.Soundness.HostLocalCoreMemory
import SP1Clean.Soundness.ProtectedLocalCoreRom

/-! # Ordinary ROM protection with host RAM effects installed

The decoded instructions retain their physical rows in the extended assembly. Its own permission
ledger authenticates their byte requests, even when host tables consume additional permissions.
The store footprints and instruction case split reuse the existing protected-core proofs.
-/

namespace SP1Clean.Soundness.HostLocalCore

open Circuit Air.Flat Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance instructionLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance instructionLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}

private theorem instruction_component (index : Fin 25) :
    (tables (p := p) image source auxiliary)[7 + index.val]'(by rw [tables_length]; omega) =
      (ProtectedLocalCore.tables image source)[7 + index.val]'(by
        rw [ProtectedLocalCore.tables_length]; omega) := by
  rw [core_component image source auxiliary ⟨7 + index.val, by omega⟩,
    if_neg (show ¬58 = 7 + index.val by omega)]

private theorem instructionRows_physical
    (witness : EnsembleWitness (ensemble image source auxiliary channels))
    {decoded : DecodedInstructionRow p}
    (member : decoded ∈ LocalCore.instructionRows (localWitness witness)) :
    ∃ index : Fin 25,
      decoded.chip = (supportedChips (p := p))[index.val]'(by rw [supportedChips_length]; exact index.isLt) ∧
      decoded.physical ∈ (witness.tables[7 + index.val]'(by
        rw [← witness.same_length]; change 7 + index.val < (tables image source auxiliary).length
        rw [tables_length]; omega)).table := by
  obtain ⟨index, chipBound, tableBound, same, physical⟩ := position_of_mem_decodeInstructionTables member
  have bound : index < 25 := by simpa only [supportedChips_length] using chipBound
  refine ⟨⟨index, bound⟩, same, ?_⟩
  simp only [LocalCore.instructionTables, List.getElem_take, List.getElem_drop] at physical
  rw [localWitness_table witness ⟨7 + index, by omega⟩] at physical
  exact physical

/-- The actual extended AIR bounds every ordinary write byte and excludes instruction bytes. -/
theorem instructionRows_write_authorized
    (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (pulls : ∀ component ∈ auxiliary, WritePermission.Pulls component)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {decoded : DecodedInstructionRow p}
    (member : decoded ∈ LocalCore.instructionRows (localWitness witness))
    (active : (decoded.toChipRow (localWitness witness).data).is_real = 1) :
    Target.RowWriteAuthorized image (decoded.toChipRow (localWitness witness).data).view := by
  obtain ⟨index, same, physicalMem⟩ := instructionRows_physical witness member
  let table := witness.tables[7 + index.val]'(by
    rw [← witness.same_length]; change 7 + index.val < (tables image source auxiliary).length
    rw [tables_length]; omega)
  have tableMem : table ∈ witness.allTables := witness.mem_allTables_of_mem_tables (List.getElem_mem _)
  have dataEq : table.data = (localWitness witness).data := witness.same_data table (List.getElem_mem _)
  have envEq : decoded.environment (localWitness witness).data = table.environment decoded.physical := by
    simp only [DecodedInstructionRow.environment, Table.environment, dataEq]
  change (decoded.toChipRow (localWitness witness).data).view.is_real = 1 at active
  rw [DecodedInstructionRow.toChipRow_view, envEq] at active ⊢
  rw [same] at active ⊢
  have descriptor : (supportedChips (p := p))[index.val]'(by
      rw [supportedChips_length]; exact index.isLt) =
      supportedChipFor (InstructionChipId.all[index.val]'index.isLt) := List.getElem_map _
  rw [descriptor] at active ⊢
  apply ProtectedLocalCore.supported_write_property (Target.RowWriteAuthorized image)
    (fun row empty write same => by rw [empty] at same; contradiction) _ (table.environment decoded.physical) ?_ ?_ ?_ ?_ active
  · intro identity real
    have position : index.val = 18 := by
      exact (InstructionChipId.all_nodup.getElem_inj_iff (hi := index.isLt) (hj := by decide)).mp identity
    apply ProtectedLocalCore.byte_write_authorized_of_row table decoded.physical
      (row_pull_permitted witness pulls constraints balanced table tableMem decoded.physical physicalMem) ?_ real
    dsimp only [table]
    rw [← witness.same_circuits _ (by
      change 7 + index.val < (tables (p := p) image source auxiliary).length
      rw [tables_length]; omega)]
    change (tables image source auxiliary)[7 + index.val]'
      (by rw [tables_length]; omega) = _
    rw [instruction_component index]
    simp only [position]
    rfl
  · intro identity real
    have position : index.val = 19 := by
      exact (InstructionChipId.all_nodup.getElem_inj_iff (hi := index.isLt) (hj := by decide)).mp identity
    apply ProtectedLocalCore.half_write_authorized_of_row table decoded.physical
      (row_pull_permitted witness pulls constraints balanced table tableMem decoded.physical physicalMem) ?_ real
    dsimp only [table]
    rw [← witness.same_circuits _ (by
      change 7 + index.val < (tables (p := p) image source auxiliary).length
      rw [tables_length]; omega)]
    change (tables image source auxiliary)[7 + index.val]'
      (by rw [tables_length]; omega) = _
    rw [instruction_component index]
    simp only [position]
    rfl
  · intro identity real
    have position : index.val = 20 := by
      exact (InstructionChipId.all_nodup.getElem_inj_iff (hi := index.isLt) (hj := by decide)).mp identity
    apply ProtectedLocalCore.word_write_authorized_of_row table decoded.physical
      (row_pull_permitted witness pulls constraints balanced table tableMem decoded.physical physicalMem) ?_ real
    dsimp only [table]
    rw [← witness.same_circuits _ (by
      change 7 + index.val < (tables (p := p) image source auxiliary).length
      rw [tables_length]; omega)]
    change (tables image source auxiliary)[7 + index.val]'
      (by rw [tables_length]; omega) = _
    rw [instruction_component index]
    simp only [position]
    rfl
  · intro identity real
    have position : index.val = 21 := by
      exact (InstructionChipId.all_nodup.getElem_inj_iff (hi := index.isLt) (hj := by decide)).mp identity
    apply ProtectedLocalCore.double_write_authorized_of_row table decoded.physical
      (row_pull_permitted witness pulls constraints balanced table tableMem decoded.physical physicalMem) ?_ real
    dsimp only [table]
    rw [← witness.same_circuits _ (by
      change 7 + index.val < (tables (p := p) image source auxiliary).length
      rw [tables_length]; omega)]
    change (tables image source auxiliary)[7 + index.val]'
      (by rw [tables_length]; omega) = _
    rw [instruction_component index]
    simp only [position]
    rfl

/-- ROM exclusion is a consequence of the full bounded byte authorization. -/
theorem instructionRows_write_permitted
    (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (pulls : ∀ component ∈ auxiliary, WritePermission.Pulls component)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {decoded : DecodedInstructionRow p}
    (member : decoded ∈ LocalCore.instructionRows (localWitness witness))
    (active : (decoded.toChipRow (localWitness witness).data).is_real = 1) :
    Target.RowWritePermitted image (decoded.toChipRow (localWitness witness).data).view := by
  exact (instructionRows_write_authorized witness pulls constraints balanced member active).permitted

end SP1Clean.Soundness.HostLocalCore
