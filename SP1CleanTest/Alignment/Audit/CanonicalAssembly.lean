module

public import SP1CleanTest.Alignment.Support.InstalledAssembly

/-! # Generation inputs cannot supply uncommitted program metadata

The complete installed 95-table inventory has no physical table named `sp1.pc_start`. Its
canonical data therefore cannot inherit that entry from witness-generation inputs. The check
applies to every witness of this inventory, independently of generation or semantic validity.
Program-binding consumers must use an authenticated boundary.
-/

@[expose] public section

namespace SP1CleanTest.CanonicalAssembly

open SP1Clean SP1Clean.Model.Core SP1CleanTest.Alignment.InstalledAssembly Air.Flat

/-- No witness of this physical inventory contains the legacy initial-PC data entry. -/
theorem uncommittedInitialPcAbsent {context : Context}
    (witness : EnsembleWitness (assembly context)) :
    witness.data "sp1.pc_start" 3 = #[] := by
  have absent : "sp1.pc_start" ∉
      ((assembly context).tables.map fun component => component.circuit.name) := by
    rw [tables_eq, List.map_append]
    simp only [List.mem_append, not_or]
    constructor
    · dsimp only [withoutCommitments]
      erw [Soundness.HostFinalMemory.tables_eq]
      simp only [List.map_set, Soundness.HostFinalMemory.beforeChecks,
        Soundness.HostLocalCore.tables_names, Soundness.ProtectedLocalCore.tables_names,
        Soundness.LocalCore.tables, Soundness.LocalCore.afterSourceTables,
        List.map_append, List.map_cons, List.map_nil,
        Soundness.SnapshotMemoryEnsemble.registerMembership, StaticTable.component,
        StaticTable.provider, MemorySnapshot.registerTable, StaticTable.ofRows,
        Soundness.FinalMemoryChecks.checkTables, FinalRegisterValue.membership]
      exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
  have noTable : ∀ table ∈ witness.tables, table.component.circuit.name ≠ "sp1.pc_start" := by
    intro table member same
    apply absent
    rw [← witness.tables_map_component, List.map_map]
    exact List.mem_map.mpr ⟨table, member, same⟩
  exact deriveProverData_append_of_not_mem [] witness.tables "sp1.pc_start" noTable 3

/-- A nonempty generation-time entry cannot become committed data without a physical table. -/
theorem seedCannotChooseCommittedData {context : Context}
    (witness : EnsembleWitness (assembly context))
    (generationData : ProverData Fp) (nonempty : generationData "sp1.pc_start" 3 ≠ #[]) :
    witness.data ≠ generationData := by
  intro same
  apply nonempty
  rw [← same]
  exact uncommittedInitialPcAbsent witness

end SP1CleanTest.CanonicalAssembly
