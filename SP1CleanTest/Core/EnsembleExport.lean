import ToClean.Air.EnsembleExport
import SP1Clean.Model.SP1Field
import Clean.Utils.Tactics

/-! # A complete exported ensemble fixture

The fixture has a fixed lookup, a provider component, and a public verifier connected by a channel.
It exercises the generic export boundary independently of SP1 row layouts and faithfulness maps.
-/

namespace SP1CleanTest.Core.EnsembleExport

open Air.Flat Circuit

abbrev Fp := ZMod SP1Clean.SP1Prime

instance : Hashable Fp := ⟨fun value => hash value.val⟩

def values : Channel Fp field where
  name := "values"
  Guarantees _ _ := True

def allowed : StaticTable Fp field where
  name := "allowed"
  length := 2
  row index := if index.val = 0 then 7 else 9
  index value := if value = 7 then 0 else 1
  Spec value := value = 7 ∨ value = 9
  contains_iff := by
    intro value
    constructor
    · rintro ⟨index, rfl⟩
      split <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩

def provider : GeneralFormalCircuit Fp field unit where
  main value := do
    lookup allowed.toTable value
    values.push value
  Spec value _ _ := value = 7 ∨ value = 9
  ProverAssumptions value _ _ := value = 7 ∨ value = 9
  channelsWithRequirements := [values.toRaw]
  soundness := by
    circuit_proof_start [allowed, values]
    simp_all
  completeness := by
    circuit_proof_start [allowed, values]
    simp_all

def verifier : GeneralFormalCircuit Fp field unit where
  main value := values.pull value
  Spec _ _ _ := True
  soundness := by circuit_proof_start [values]
  completeness := by circuit_proof_start [values]

def ensemble : Ensemble Fp field where
  tables := [⟨provider⟩]
  channels := [values.toRaw]
  verifier := verifier
  verifier_length_zero := by intro value; rfl

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
