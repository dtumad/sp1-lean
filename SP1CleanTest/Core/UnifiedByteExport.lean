import SP1Clean.Proofs.Chips.ByteChip.Unified
import SP1CleanTest.Core.ComponentExport
import ToClean.Air.EnsembleCheck
import ToClean.Circuit.VerifierInteractions

/-! # Closed export fixture for the consolidated byte provider

The public boundary carries individual byte requests. Clean's unmodified demand scheduler
aggregates equal messages and pads the provider. Raw acceptance checks every generated row
and every ledger occurrence, including repeated requests and zero-count padding.
-/

namespace SP1CleanTest.Core.UnifiedByteExport

open Air.Flat Circuit SP1Clean
open SP1Clean.ByteChip
open ComponentExport (Fp)

abbrev Requests (n : ℕ) := ProvableVector ByteRow n

def component : Component Fp := { circuit := Unified.circuit }

def verifier (n : ℕ) : Verifier.Program Fp (Requests n) where
  main requests := Verifier.ofInteractions
    (requests.toList.map fun request =>
      ((Channels.byteChannel (p := SP1Prime)).pulled request).toRaw)
    (by
      intro interaction member env
      obtain ⟨request, _, rfl⟩ := List.mem_map.mp member
      simp [circuit_norm, ChannelInteraction.Requirements])

def ensemble (n : ℕ) : Ensemble Fp (Requests n) where
  tables := [component]
  unique_names := by simp
  channels := [Channels.byteChannel.toRaw]
  verifier := verifier n

def config : WitnessGeneration.Config Fp unit where
  modes := [.demand {
    channel := (Channels.byteChannel (p := SP1Prime)).name
    direction := .pull
    aggregation := .byMessage
    input := ⟨[.message 0, .message 1, .message 2, .message 3, .multiplicity]⟩
  }]
  padding := [{ input := #[0, 0, 0, 0, 0] }]
  fuel := 128

def description (n : ℕ) : Air.Flat.EnsembleCheck (ensemble n) where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [ensemble, component, Component.lookups_eq, Component.rowOperations,
      Unified.circuit, circuit_norm]
  channels_unique := by simp [ensemble]
  channels_complete := by
    simp [ensemble, component, Component.interactions_eq, Component.rowOperations,
      Unified.circuit, Unified.main, Gadgets.OneHot.circuit, Gadgets.OneHot.main,
      Gadgets.ToBits.toBits, Gadgets.ToBits.main, Gadgets.ToBits.rangeCheck,
      Gadgets.VariableRange.rangeCheck, Gadgets.VariableRange.main, Gadgets.Equality.main,
      GeneralFormalCircuit.toSubcircuit_interactions, FormalAssertion.toSubcircuit_interactions,
      Circuit.interactions_forEach,
      circuit_norm]
  verifier_channels_complete := by
    change ∀ i ∈ (verifier n).circuitOperations.interactions, i.channel ∈ _
    rw [Verifier.Program.circuitOperations, verifier, Verifier.ofInteractions_interactions]
    simp [ensemble, circuit_norm]

def generate (rows : List (ByteRow Fp)) : Except String (EnsembleWitness (ensemble rows.length)) :=
  WitnessGeneration.generate (ensemble rows.length) config ⟨rows.toArray, by simp⟩ ()

def request (opcode a b c : ℕ) : ByteRow Fp := ⟨opcode, a, b, c⟩

def cases : List (String × List (ByteRow Fp) × Bool) :=
  [("empty", [], true),
   ("all-opcodes", [request 0 128 128 255, request 1 255 128 127,
     request 2 255 128 127, request 3 0 255 0, request 4 1 127 128,
     request 5 1 128 0, request 6 65535 16 0], true),
   ("repeated", List.replicate 5 (request 0 128 128 255) ++ List.replicate 4 (request 6 0 0 0), true),
   ("range-widths", (List.range 17).map fun width => request 6 (2 ^ width - 1) width 0, true),
   ("distinct-64", (List.range 64).map fun value => request 6 value 16 0, true),
   ("distinct-65", (List.range 65).map fun value => request 6 value 16 0, true)] ++
  ([request 7 0 0 0, request 0 0 256 0, request 1 0 0 256, request 2 1 0 0,
    request 3 1 0 0, request 4 2 0 1, request 5 0 0 1,
    request 6 0 17 0, request 6 1 0 0, request 6 0 16 1].zipIdx.map fun (row, index) =>
    (s!"invalid-{index}", [row], false))

def exportSizes : List ℕ := [0, 1, 7, 9, 17, 64, 65]

def rustExports : List (String × Except String String) :=
  [("unified_byte_row.rs", ComponentExport.exportRust "UnifiedByteRow" Unified.circuit)] ++
  exportSizes.map fun n =>
    (s!"unified_byte_{n}.rs", Extraction.Rust.ensembleToRust "UnifiedByte" (ensemble n) config)

theorem cases_correct : cases.all (fun (_, input, expected) =>
    (match generate input with
    | .ok witness => (description input.length).checkWitness SP1Prime witness
    | .error _ => false) == expected) = true := by native_decide

theorem exports_succeed : rustExports.all (fun entry => entry.2.isOk) = true := by native_decide

end SP1CleanTest.Core.UnifiedByteExport
