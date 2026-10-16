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

private def message (i : ℕ) : Witgen.FExpr Fp := .expr (.var ⟨i⟩)
private def opcode (i : ℕ) : Witgen.BExpr Fp := .feq (message 0) (.const i)

def byteHandler (op : Fin 6) : WitnessGeneration.PreallocatedHandler Fp where
  interaction := op.val
  column := 7 + op.val
  predicate := opcode op.val
  predicate_valid := by rfl
  rowIndex := some (.add (.mul (.val (message 2)) (.const 256)) (.val (message 3)))
  rowIndex_valid := by rfl

def config : WitnessGeneration.Config Fp where
  components := [((Preprocessed.byteCircuit (p := SP1Prime)).name, {
    mode := .preallocated {
      rows := 65536
      input := .ofFExprs #v[.const 0, .const 0, .const 0, .const 0, .const 0, .const 0]
      input_valid := by rfl
      handlers := (List.finRange 6).map byteHandler
    }
    padding := { input := Array.replicate 13 0 }
  }), ((Preprocessed.rangeCircuit (p := SP1Prime)).name, {
    mode := .preallocated {
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
    }
    padding := { input := Array.replicate 3 0 }
  })]
  fuel := 131074

def generate (rows : List (ByteRow Fp)) : Except String (EnsembleWitness (ensemble rows.length)) :=
  WitnessGeneration.generate (ComponentExport.fixture (ensemble rows.length)) config ⟨rows.toArray, by simp⟩ () |>.mapError toString

/-- The existing 23 circuits with honest channel-driven generation, rather than precounted rows. -/
def baselineMode (index : ℕ) : WitnessGeneration.Mode Fp := .demand {
  channel := (Channels.byteChannel (p := SP1Prime)).toRaw
  direction := .pull
  aggregation := .byMessage
  predicate := if index < 6 then opcode index
    else .and (opcode 6) (.feq (message 2) (.const (index - 6)))
  predicate_valid := by split <;> rfl
  input := ⟨if index = 5 then [.message 2, .multiplicity]
    else if index < 6 then [.message 2, .message 3, .multiplicity]
    else [.message 1, .multiplicity]⟩
}

def baselineConfig : WitnessGeneration.Config Fp where
  components := UnifiedByteBenchmarks.components.zipIdx.map fun (component, index) =>
    (component.circuit.name, {
      mode := baselineMode index
      padding := { input := Array.replicate component.rowOffset 0 }
    })
  fuel := 131074

def unifiedConfig : WitnessGeneration.Config Fp :=
  { UnifiedByteExport.config with fuel := 131074 }

def smallRustExports : Except String (List (String × Except String String)) := do
  let fixtures := UnifiedByteExport.exportSizes.map fun n =>
    (s!"preprocessed_byte_{n}.rs", Backends.Plonky3.Print.ensembleToRust (ComponentExport.fixture (ensemble n)) config)
  let benchmarks := (← UnifiedByteBenchmarks.workloads).flatMap fun (name, rows) =>
    [(s!"byte_routed_{name}.rs", Backends.Plonky3.Print.ensembleToRust (ComponentExport.fixture (UnifiedByteBenchmarks.ensemble rows.length)) baselineConfig),
     (s!"byte_fixed_{name}.rs", Backends.Plonky3.Print.ensembleToRust (ComponentExport.fixture (ensemble rows.length)) config)]
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

def requestMode (n : UInt64) : WitnessGeneration.Mode Fp := .preallocated {
  rows := n
  input := .ofFExprs #v[
    .hintGet "requests" 4 .idx 0, .hintGet "requests" 4 .idx 1,
    .hintGet "requests" 4 .idx 2, .hintGet "requests" 4 .idx 3]
  input_valid := by rfl
  handlers := []
}

def largeEnsemble (providers : List (Component Fp))
    (unique : (providers.map (·.circuit.name)).Nodup)
    (fresh : "benchmark.requests" ∉ providers.map (·.circuit.name)) : Ensemble Fp unit where
  tables := { circuit := requestCircuit, Assumptions := (requestCircuit).Assumptions } :: providers
  unique_names := by simpa [requestCircuit] using And.intro fresh unique
  channels := [Channels.byteChannel.toRaw]
  verifier := Verifier.Program.empty Fp unit

def largeConfig (n : UInt64) (providers : WitnessGeneration.Config Fp) :
    WitnessGeneration.Config Fp where
  components := (requestCircuit.name, {
    mode := requestMode n, padding := { input := #[0, 0, 0, 0] }
  }) :: providers.components
  fuel := 131074

/-- A rectangular hint view supplies request rows directly to Clean's row initializer. -/
def largeFormal (n : UInt64) (providers : List (Component Fp))
    (unique : (providers.map (·.circuit.name)).Nodup)
    (fresh : "benchmark.requests" ∉ providers.map (·.circuit.name)) : FormalEnsemble Fp unit :=
  { ComponentExport.fixture (largeEnsemble providers unique fresh) (fields (4 * n.toNat)) with
    hintTables := [{ key := "requests", width := 4, offset := 0, rows := n.toNat }] }

def largeRustExports : List (String × Except String String) :=
  [1024, 16384, 65536].flatMap fun n =>
    [(s!"byte_large_routed_{n}.rs", Backends.Plonky3.Print.ensembleToRust
        (largeFormal n UnifiedByteBenchmarks.components (by decide) (by decide))
        (largeConfig n baselineConfig)),
     (s!"byte_large_candidate_{n}.rs", Backends.Plonky3.Print.ensembleToRust
        (largeFormal n [UnifiedByteExport.component] (by decide) (by decide))
        (largeConfig n unifiedConfig)),
     (s!"byte_large_fixed_{n}.rs", Backends.Plonky3.Print.ensembleToRust
        (largeFormal n components (by decide) (by decide)) (largeConfig n config))]

def rustExports : Except String (List (String × Except String String)) := do
  return (← smallRustExports) ++ largeRustExports

end SP1CleanTest.Core.PreprocessedByteExport
