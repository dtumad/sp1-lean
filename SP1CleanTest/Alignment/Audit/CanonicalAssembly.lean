import SP1Clean.Proofs.Completeness.Assembly
import SP1Clean.Model.SP1Field

/-! # Generation inputs cannot supply uncommitted program metadata

The legacy 55-table inventory has no physical table named `sp1.pc_start`. Its canonical data
therefore cannot inherit that entry from witness-generation inputs. This catches the old
shared-data assumption without evaluating a concrete trace or assuming its semantic validity.
Program-binding consumers must use an authenticated boundary instead of that assumption.
-/

namespace SP1CleanTest.CanonicalAssembly

open SP1Clean SP1Clean.Soundness Air.Flat

/-- Canonical data contains no legacy initial-PC entry, for any generated trace. -/
theorem legacyInitialPcAbsent (trace : SupportedCoreTraceWitness SP1Prime) :
    trace.witness.data "sp1.pc_start" 3 = #[] := by
  have absent : "sp1.pc_start" ∉
      ((sp1Ensemble (p := SP1Prime)).tables.map fun component => component.circuit.name) := by
    decide
  have noTable : ∀ table ∈ trace.tables, table.component.circuit.name ≠ "sp1.pc_start" := by
    intro table member same
    apply absent
    rw [← trace.tables_map_component, List.map_map]
    exact List.mem_map.mpr ⟨table, member, same⟩
  exact deriveProverData_append_of_not_mem [] trace.tables "sp1.pc_start" noTable 3

/-- A nonempty generation-time entry cannot become committed data without a physical table. -/
theorem seedCannotChooseCommittedData (trace : SupportedCoreTraceWitness SP1Prime)
    (nonempty : trace.generationData "sp1.pc_start" 3 ≠ #[]) :
    trace.witness.data ≠ trace.generationData := by
  intro same
  apply nonempty
  rw [← same]
  exact legacyInitialPcAbsent trace

end SP1CleanTest.CanonicalAssembly
