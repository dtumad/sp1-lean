import ToClean.Air.EnsembleExport
import SP1CleanTest.Core.EnsembleCheck

/-! # Legacy ensemble serialization fixture

Migration evidence for the JSON interpreter. The shared finite witness checks live independently
in EnsembleCheck; this serializer is replaced when the built-in Rust fixture covers this boundary.
-/

namespace SP1CleanTest.Core.EnsembleExport

open Air.Flat Circuit SP1CleanTest.Core.EnsembleCheck

instance : Hashable Fp := ⟨fun value => hash value.val⟩

def description : Air.Flat.EnsembleExport ensemble where
  componentNames := ["provider"]
  names_length := rfl
  verifierName := "public"
  names_unique := by decide
  names_nonempty := by simp
  channels_unique := by simp [ensemble]
  channels_nonempty := by simp [ensemble, values, Channel.toRaw]
  lookups := [FiniteLookup.ofStatic allowed]
  lookups_unique := by simp
  lookups_nonempty := by simp [FiniteLookup.ofStatic, allowed, StaticTable.toTable, Table.toRaw]
  lookups_complete := by
    simp [ensemble, Ensemble.allTables, Ensemble.verifierTable, Component.rowOperations,
      provider, verifier, circuit_norm]
    rfl
  channels_complete := by
    simp [ensemble, Ensemble.allTables, Ensemble.verifierTable, Component.rowOperations,
      provider, verifier, circuit_norm]

/-- Byte-stable instance consumed by the Rust whole-ensemble regression. -/
def instanceJson : Except String Lean.Json := description.toJson? SP1Clean.SP1Prime

example : instanceJson.isOk = true := by native_decide

end SP1CleanTest.Core.EnsembleExport
