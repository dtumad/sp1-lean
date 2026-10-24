module

public import SP1CleanTest.Core.ComponentExport
public import SP1Clean.Model.SP1Field
public import ToClean.Air.StaticProvider
public import ToClean.Air.EnsembleCheck
public import ToClean.Circuit.StaticTable

/-! # Built-in export of empty, padded and duplicate membership tables

Use the production ToClean provider and Clean's scheduler directly. Independent raw checks retain
every original row and every inactive occurrence. Rust supplies separate fixed-row expectations
and backend mutations; these fixtures do not assert scheduler completeness or a lowering proof.
-/

@[expose] public section

namespace SP1CleanTest.Core.StaticProviderExport

open Air.Flat Circuit

abbrev Fp := ZMod SP1Clean.SP1Prime
abbrev Requests := ProvableVector field 2

/-- Small named inventories cover empty tables, padding, duplicates and genuine zero values. -/
structure Fixture where
  name : String
  rows : List Fp
  bounded : rows.length ≤ 5

def table (fixture : Fixture) : StaticTable Fp field :=
  StaticTable.ofRows "fixture.membership" fixture.rows

private theorem height_bounded (fixture : Fixture) : (table fixture).height < UInt64.size := by
  have padded := (table fixture).height_lt_double
  have bounded := fixture.bounded
  change (table fixture).height < 2 * max fixture.rows.length 1 at padded
  norm_num [UInt64.size] at *
  omega

def verifier (fixture : Fixture) : Verifier.Program Fp Requests where
  Spec _ _ := True
  soundness := by intros; trivial
  main requests := do
    Verifier.pull (table fixture).channel ⟨requests[0], 1⟩
    Verifier.pull (table fixture).channel ⟨requests[1], 1⟩

def ensemble (fixture : Fixture) : Ensemble Fp Requests where
  tables := [(table fixture).component (height_bounded fixture)]
  unique_names := by simp
  channels := [(table fixture).channel.toRaw]
  verifier := verifier fixture

def emptyEnsemble (fixture : Fixture) : Ensemble Fp unit where
  tables := [(table fixture).component (height_bounded fixture)]
  unique_names := by simp
  channels := [(table fixture).channel.toRaw]

def config (fixture : Fixture) : WitnessGeneration.Config Fp where
  components := [((table fixture).provider.name, {
    mode := .preallocated {
      rows := UInt64.ofNat (table fixture).height
      input := .ofFExprs #v[.const 0]
      input_valid := by rfl
      handlers := [{ interaction := 0, column := 2 }]
    }
    padding := { input := #[0, 0, 0], minimumRows := UInt64.ofNat (table fixture).height }
  })]
  fuel := 8

def description (fixture : Fixture) : Air.Flat.EnsembleCheck (ensemble fixture) where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [ensemble, Component.lookups_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, circuit_norm]
  channels_unique := by simp [ensemble]
  channels_complete := by
    simp [ensemble, Component.interactions_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, circuit_norm]
  verifier_channels_complete := by
    simp [ensemble, Ensemble.verifierOperations, verifier,
      Verifier.Program.circuitOperations, circuit_norm]

def emptyDescription (fixture : Fixture) : Air.Flat.EnsembleCheck (emptyEnsemble fixture) where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [emptyEnsemble, Component.lookups_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, circuit_norm]
  channels_unique := by simp [emptyEnsemble]
  channels_complete := by
    simp [emptyEnsemble, Component.interactions_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, circuit_norm]
  verifier_channels_complete := by
    simp [emptyEnsemble, Ensemble.verifierOperations, Verifier.Program.circuitOperations,
      Verifier.Program.empty, circuit_norm]

def generate (fixture : Fixture) (requests : Requests Fp) :
    Except String (EnsembleWitness (ensemble fixture)) :=
  WitnessGeneration.generate (ComponentExport.fixture (ensemble fixture)) (config fixture) requests () |>.mapError toString

def generateEmpty (fixture : Fixture) : Except String (EnsembleWitness (emptyEnsemble fixture)) :=
  WitnessGeneration.generate (ComponentExport.fixture (emptyEnsemble fixture)) (config fixture) () () |>.mapError toString

/-- Include a real zero payload beside zero padding and repeated first/non-first payloads. -/
def fixtures : List Fixture :=
  [⟨"empty", [], by decide⟩, ⟨"singleton", [0], by decide⟩, ⟨"uneven", [7, 0, 9], by decide⟩,
    ⟨"duplicates", [0, 7, 0, 7, 9], by decide⟩, ⟨"zeroes", [0, 0, 0, 0, 0], by decide⟩]

def requests : List (Requests Fp) :=
  ([0, 7, 9, 11] : List Fp).flatMap fun a =>
    ([0, 7, 9, 11] : List Fp).map fun b => #v[a, b]

def rustExports : List (String × Except String String) := fixtures.flatMap fun fixture =>
  [(s!"static_{fixture.name}.rs", Backends.Plonky3.Print.ensembleToRust (ComponentExport.fixture (ensemble fixture)) (config fixture)),
   (s!"static_{fixture.name}_unused.rs", Backends.Plonky3.Print.ensembleToRust (ComponentExport.fixture (emptyEnsemble fixture)) (config fixture))]

theorem cases_correct : fixtures.all (fun fixture => requests.all fun request =>
    (match generate fixture request with
    | .ok witness => (description fixture).checkWitness SP1Clean.SP1Prime witness
    | .error _ => false) == (fixture.rows.contains request[0] && fixture.rows.contains request[1])) = true := by
  native_decide

theorem unused_correct : fixtures.all (fun fixture =>
    (generateEmpty fixture).map (fun witness =>
      (emptyDescription fixture).checkWitness SP1Clean.SP1Prime witness &&
        witness.interactions.length == (table fixture).height &&
        witness.interactions.all (·.mult == 0)) == .ok true) = true := by native_decide

theorem exports_succeed : rustExports.all (fun entry => entry.2.isOk) = true := by native_decide

end SP1CleanTest.Core.StaticProviderExport
