import SP1Clean.Proofs.Chips.ByteChip.Preprocessed
import SP1CleanTest.Core.UnifiedByteBenchmarks

/-! # SP1-shaped provider export experiment

The two fixed tables preserve physical duplicates. Message predicates route the shared bus;
direct indices select SP1's honest count slot, with the full interaction still checked by Clean.
-/
namespace SP1CleanTest.Core.PreprocessedByteExport
open Air.Flat Circuit SP1Clean SP1Clean.ByteChip
open ComponentExport (Fp)
open UnifiedByteExport (Requests)

def components : List (Component Fp) := [Preprocessed.byteComponent, Preprocessed.rangeComponent]

def ensemble (n : ℕ) : Ensemble Fp (Requests n) where
  tables := components
  unique_names := by decide
  channels := [Channels.byteChannel.toRaw]
  verifier := UnifiedByteExport.verifier n

private def message (i : ℕ) : Witgen.FExpr Fp := .proverInputGet (.const (UInt64.ofNat i))
private def opcode (i : ℕ) : Witgen.BExpr Fp := .feq (message 0) (.const i)

def byteHandler (op : Fin 6) : WitnessGeneration.PreallocatedHandler Fp where
  interaction := op.val
  column := 7 + op.val
  predicate := opcode op.val
  predicate_valid := by rfl
  rowIndex := some (.add (.mul (.val (message 2)) (.const 256)) (.val (message 3)))
  rowIndex_valid := by rfl

def config : WitnessGeneration.Config Fp unit where
  modes := [.preallocated {
    rows := 65536
    input := .ofFExprs #v[.const 0, .const 0, .const 0, .const 0, .const 0, .const 0]
    input_valid := by rfl
    handlers := (List.finRange 6).map byteHandler
  }, .preallocated {
    rows := 131072
    input := .ofFExprs #v[.const 0]
    input_valid := by rfl
    handlers := [{
      interaction := 0
      column := 2
      predicate := opcode 6
      predicate_valid := by rfl
      rowIndex := some (.add (.pow2 (.val (message 2))) (.val (message 1)))
      rowIndex_valid := by rfl
    }]
  }]
  padding := [{ input := Array.replicate 13 0 }, { input := Array.replicate 3 0 }]
  fuel := 131074

def generate (rows : List (ByteRow Fp)) : Except String (EnsembleWitness (ensemble rows.length)) :=
  WitnessGeneration.generate (ensemble rows.length) config ⟨rows.toArray, by simp⟩ ()

/-- The existing 23 circuits with honest channel-driven generation, rather than precounted rows. -/
def baselineMode (index : ℕ) : WitnessGeneration.Mode Fp := .demand {
  channel := "SP1Byte"
  direction := .pull
  aggregation := .byMessage
  predicate := if index < 6 then opcode index
    else .and (opcode 6) (.feq (message 2) (.const (index - 6)))
  predicate_valid := by split <;> rfl
  input := ⟨if index = 5 then [.message 2, .multiplicity]
    else if index < 6 then [.message 2, .message 3, .multiplicity]
    else [.message 1, .multiplicity]⟩
}

def baselineConfig : WitnessGeneration.Config Fp unit where
  modes := (List.range 23).map baselineMode
  padding := UnifiedByteBenchmarks.components.map fun c => { input := Array.replicate c.rowOffset 0 }
  fuel := 131074

def unifiedConfig : WitnessGeneration.Config Fp unit :=
  { UnifiedByteExport.config with fuel := 131074 }

def smallRustExports : Except String (List (String × Except String String)) := do
  let fixtures := UnifiedByteExport.exportSizes.map fun n =>
    (s!"preprocessed_byte_{n}.rs", Extraction.Rust.ensembleToRust "PreprocessedByte" (ensemble n) config)
  let benchmarks := (← UnifiedByteBenchmarks.workloads).flatMap fun (name, rows) =>
    [(s!"byte_routed_{name}.rs", Extraction.Rust.ensembleToRust "ByteRouted"
        (UnifiedByteBenchmarks.ensemble rows.length) baselineConfig),
     (s!"byte_fixed_{name}.rs", Extraction.Rust.ensembleToRust "PreprocessedByte"
        (ensemble rows.length) config)]
  return fixtures ++ benchmarks

/-- Common request rows for scaling measurements. These benchmarks measure internal lookup
closure; public-input binding is exercised separately by the small public-request fixtures. -/
def requestCircuit : GeneralFormalCircuit Fp ByteRow unit where
  name := "benchmark.requests"
  main input := Channels.byteChannel.pull input
  Spec _ _ _ := True
  ProverAssumptions input _ _ := ByteRowSpec input
  soundness := by circuit_proof_start
  completeness := by
    circuit_proof_start [Channels.byteChannel]
    exact h_assumptions

def requestMode (n : ℕ) : WitnessGeneration.Mode Fp := .preallocated {
  rows := n
  input := .ofFExprs #v[
    .proverInputGet (.mul .idx (.const 4)),
    .proverInputGet (.add (.mul .idx (.const 4)) (.const 1)),
    .proverInputGet (.add (.mul .idx (.const 4)) (.const 2)),
    .proverInputGet (.add (.mul .idx (.const 4)) (.const 3))]
  input_valid := by rfl
  handlers := []
}

def largeEnsemble (providers : List (Component Fp))
    (unique : (providers.map (·.circuit.name)).Nodup)
    (fresh : "benchmark.requests" ∉ providers.map (·.circuit.name)) : Ensemble Fp unit where
  tables := { circuit := requestCircuit } :: providers
  unique_names := by simpa [requestCircuit] using And.intro fresh unique
  channels := [Channels.byteChannel.toRaw]
  verifier := { main _ := pure () }

def largeConfig (n : ℕ) (providers : WitnessGeneration.Config Fp unit) :
    WitnessGeneration.Config Fp (fields (4 * n)) where
  modes := requestMode n :: providers.modes
  padding := { input := #[0, 0, 0, 0] } :: providers.padding
  fuel := 131074

def largeRustExports : List (String × Except String String) :=
  [1024, 16384, 65536].flatMap fun n =>
    [(s!"byte_large_routed_{n}.rs", Extraction.Rust.ensembleToRust "ByteRouted"
        (largeEnsemble UnifiedByteBenchmarks.components (by decide) (by decide))
        (largeConfig n baselineConfig)),
     (s!"byte_large_candidate_{n}.rs", Extraction.Rust.ensembleToRust "UnifiedByte"
        (largeEnsemble [UnifiedByteExport.component] (by decide) (by decide))
        (largeConfig n unifiedConfig)),
     (s!"byte_large_fixed_{n}.rs", Extraction.Rust.ensembleToRust "PreprocessedByte"
        (largeEnsemble components (by decide) (by decide)) (largeConfig n config))]

def rustExports : Except String (List (String × Except String String)) := do
  return (← smallRustExports) ++ largeRustExports

end SP1CleanTest.Core.PreprocessedByteExport
