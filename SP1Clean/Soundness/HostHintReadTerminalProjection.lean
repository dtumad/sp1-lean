import SP1Clean.Soundness.HostHintReadBanks
import SP1Clean.Soundness.HostQueueCPUReplay

/-! # Legacy padding has no event in the installed CPU inventory

The strengthened physical component projects to the original execution carrier without losing
its zero-selector assertion. Thus every HALT event in the mixed assembly comes from the full
syscall wrapper and participates in HostCall accounting.
-/

namespace SP1Clean.Soundness.HostHintReadTerminal

open Circuit Air.Flat Channels Model.Core NativeCore HostHintReadLocal

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
variable {image : ProgramImage} {source : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}
  {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

private theorem bound
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)) : 57 < witness.tables.length := by
  rw [← witness.same_length]
  change 57 < ((HostLocalCore.tables image source _).set 57 _).length
  rw [List.length_set, HostLocalCore.tables_length]
  omega

private theorem projected_table
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)) :
    LocalCore.systemTable (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)) 2 =
      (witness.tables[57]'(bound witness)).withComponent HaltPaddingChip.original := by
  unfold LocalCore.systemTable HostLocalCore.localWitness
  simp only [EnsembleWitness.project, EnsembleWitness.ofTables_tables, List.getElem_ofFn,
    HostHintQueueBoundary.expanded_tables]
  rw [List.getElem_append_left (by
      change 57 < _
      simpa only [List.length_set] using bound witness)]
  simp only [show (55 + ((2 : Fin 4) : ℕ) : ℕ) = 57 from rfl, List.getElem_set_self]
  rfl

/-- The original carrier contains no active legacy HALT row. -/
theorem legacy_rows_nil
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (constraints : witness.Constraints) :
    activeSystemRows (LocalCore.systemTable
      (HostLocalCore.localWitness (HostHintQueueBoundary.expanded witness)) 2) haltRow (·.is_real) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro row member
  obtain ⟨physical, physicalMem, rfl, real⟩ := activeSystemRows_member _ _ _ member
  rw [projected_table] at physicalMem real
  have checked := constraints _ (witness.mem_allTables_of_mem_tables (List.getElem_mem _)) physical physicalMem
  rw [HaltPadding.table_component witness] at checked
  have zero := ((HaltPaddingChip.constraints _).mp checked).2
  change (valueFromOffset HaltChip.Inputs 0 _).is_real = 0 at zero
  have same : (haltRow ((witness.tables[57]'(bound witness)).withComponent HaltPaddingChip.original)
      physical).is_real = 0 := by
    simpa only [haltRow, Table.withComponent, Table.environment] using zero
  exact zero_ne_one (same.symm.trans real)

end SP1Clean.Soundness.HostHintReadTerminal
