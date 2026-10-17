import SP1Clean.Proofs.Chips.FixedProgramProvider.Preprocessed
import SP1CleanTest.Core.ComponentExport
import ToClean.Air.EnsembleCheck
import ToClean.Circuit.VerifierInteractions

/-! # Program preprocessing and count export

These fixtures export the production fixed-column component through Clean. Three literal
instructions and an empty inventory exercise unused rows, repeated requests and first-row
padding. Rust compares them with SP1's independent preprocessing, AIR and count generation.
The direct row index is specific to this contiguous fixture; the native model remains sparse.
-/

namespace SP1CleanTest.Core.ProgramExport

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Channels
open ComponentExport (Fp)

/-- Individual public fetch requests, retaining repeats. -/
abbrev Requests (n : ℕ) := ProvableVector ProgramMsg n

/-- ADDI x1,x2,7; ADD x1,x2,x3; ECALL. The last instruction is unused in the count fixture. -/
def image : ProgramImage := ⟨[(65536, 0x00710093), (65540, 0x003100b3), (65544, 0x73)], 65536, []⟩

/-- No decoded instruction is available to serve a request. -/
def emptyImage : ProgramImage := ⟨[], 65536, []⟩

/-- Public requests contribute one Program pull each. -/
def verifier (n : ℕ) : Verifier.Program Fp (Requests n) where
  Spec _ _ := True
  soundness := by intros; trivial
  main requests := Verifier.ofInteractions
    (requests.toList.map fun request => (programChannel.pulled request).toRaw)
    (by
      intro interaction member env
      obtain ⟨request, _, rfl⟩ := List.mem_map.mp member
      simp [circuit_norm, ChannelInteraction.Requirements])

/-- Close the Program channel with the production fixed provider. -/
def ensemble (rom : ProgramImage) (n : ℕ) : Ensemble Fp (Requests n) where
  tables := [FixedProgramProvider.Preprocessed.component rom]
  unique_names := by simp
  channels := [programChannel.toRaw]
  verifier := verifier n

/-- The contiguous fixture selects the original slot; Clean still checks the full message. -/
def config (rom : ProgramImage) : WitnessGeneration.Config Fp where
  components := [("sp1.native.program.fixed", {
    mode := .preallocated {
      rows := UInt64.ofNat (FixedProgramProvider.Preprocessed.height (p := SP1Prime) rom)
      input := .ofFExprs #v[.const 0]
      input_valid := by rfl
      handlers := if rom.rom.isEmpty then [] else [{
        interaction := 0
        column := 16
        rowIndex := some (.div (.val (.expr (.var ⟨0⟩))) (.const 4))
        rowIndex_valid := by rfl
      }]
    }
    padding := { input := Array.replicate 17 0 }
  })]
  fuel := 8

/-- Raw acceptance covers every constraint and Program occurrence. -/
def description (rom : ProgramImage) (n : ℕ) : EnsembleCheck (ensemble rom n) where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp only [ensemble, List.mem_singleton]
    rintro component rfl
    simp only [FixedProgramProvider.Preprocessed.component,
      FixedProgramProvider.Preprocessed.circuit]
    split <;> simp [Component.lookups_eq, Component.rowOperations, circuit_norm]
  channels_unique := by simp [ensemble]
  channels_complete := by
    simp only [ensemble, List.mem_singleton]
    rintro component rfl
    simp only [FixedProgramProvider.Preprocessed.component,
      FixedProgramProvider.Preprocessed.circuit]
    split <;> simp [Component.interactions_eq, Component.rowOperations, circuit_norm]
  verifier_channels_complete := by
    change ∀ i ∈ (verifier n).circuitOperations.interactions, i.channel ∈ _
    rw [Verifier.Program.circuitOperations, verifier, Verifier.ofInteractions_interactions]
    simp [ensemble, circuit_norm]

/-- Use Clean's unmodified preallocation and demand scheduling. -/
def generate (rom : ProgramImage) {n : ℕ} (requests : Requests n Fp) :
    Except String (EnsembleWitness (ensemble rom n)) :=
  WitnessGeneration.generate (ComponentExport.fixture (ensemble rom n)) (config rom) requests ()
    |>.mapError toString

/-- Two repeated ADDI fetches and one ADD fetch leave ECALL unused. -/
def requests : Requests 3 Fp :=
  let first := FixedProgramProvider.Preprocessed.message (p := SP1Prime) image 0
  let second := FixedProgramProvider.Preprocessed.message (p := SP1Prime) image 1
  #v[first, first, second]

/-- Active, unused and empty providers all use the built-in Rust emitter. -/
def rustExports : List (String × Except String String) :=
  [("program_fixed.rs", Backends.Plonky3.Print.ensembleToRust
      (ComponentExport.fixture (ensemble image 3)) (config image)),
   ("program_unused.rs", Backends.Plonky3.Print.ensembleToRust
      (ComponentExport.fixture (ensemble image 0)) (config image)),
   ("program_empty.rs", Backends.Plonky3.Print.ensembleToRust
      (ComponentExport.fixture (ensemble emptyImage 0)) (config emptyImage))]

end SP1CleanTest.Core.ProgramExport
