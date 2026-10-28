import SP1Clean.Soundness.HostFinalMemoryLookups
import SP1CleanTest.Alignment.Support.InstalledAssembly
import ToClean.Air.EnsembleCheck

/-! # Lookup-free complete installed assembly -/

namespace SP1CleanTest.Alignment.InstalledAssembly

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness SP1Clean.Channels

/-- All installed providers use AIR constraints and channels; no legacy lookup oracle remains. -/
def fixed (_context : Context) : List (FiniteLookup Fp) := []

/-- Every installed component is lookup-free, including currently unused physical slots. -/
theorem component_lookups (context : Context) (component : Component Fp)
    (member : component ∈ (assembly context).tables) : component.operations.lookups = [] := by
  rw [tables_eq] at member
  rcases List.mem_append.mp member with original | added
  · exact HostFinalMemory.installed_lookups component original
  · obtain rfl := List.mem_singleton.mp added
    simp [CommitmentDeclaration.source, StaticTable.payloadComponent, StaticTable.payloadProvider,
      Component.lookups_eq, Component.rowOperations, circuit_norm]

/-- The empty lookup inventory covers every installed operation. -/
theorem lookups_complete (context : Context) (component : Component Fp)
    (member : component ∈ (assembly context).tables) (lookup : Lookup Fp)
    (used : lookup ∈ component.operations.lookups) :
    ∃ fixedTable ∈ fixed context, fixedTable.table = lookup.table := by
  rw [component_lookups context component member] at used
  exact False.elim (List.not_mem_nil used)


end SP1CleanTest.Alignment.InstalledAssembly
