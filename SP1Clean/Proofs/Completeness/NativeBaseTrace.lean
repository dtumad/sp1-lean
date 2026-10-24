module

public import SP1Clean.Proofs.Completeness.ExecutionInventory
public import SP1Clean.Proofs.Completeness.Assembly

/-! # Bounded base assembly from the native execution compiler

The checked chronological compiler determines instruction inputs, Memory boundaries and refreshes,
and State refreshes. Its exact capacity bundle makes those lists physical Clean tables without
adding a caller premise to semantic execution. Public clock and PC endpoints are decoded once from
the statement. Preprocessed provider lists are empty here; their demand-driven closure belongs to
`NativeTraceCompiler` and does not participate in base construction or its local validity proof.
-/

@[expose] public section

namespace SP1Clean.Soundness

open SP1Clean.Execution SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Decode the public initial clock once, at the same boundary used by execution semantics and
the committed prover-data encoder. -/
def nativeInitialClock (statement : SupportedCoreStatement p) : ℕ :=
  SP1Clean.Semantics.clkNat statement.publicValues.init_clk_high
    statement.publicValues.init_clk_low

/-- Decode the public final clock. -/
def nativeFinalClock (statement : SupportedCoreStatement p) : ℕ :=
  SP1Clean.Semantics.clkNat statement.publicValues.final_clk_high
    statement.publicValues.final_clk_low

/-- Decode the public initial program counter into the field-free State-history representation. -/
def nativeInitialPc (statement : SupportedCoreStatement p) : ℕ :=
  (supportedPcBits statement.publicValues.init_pc0 statement.publicValues.init_pc1
    statement.publicValues.init_pc2).toNat

/-- Decode the public final program counter. -/
def nativeFinalPc (statement : SupportedCoreStatement p) : ℕ :=
  (supportedPcBits statement.publicValues.final_pc0 statement.publicValues.final_pc1
    statement.publicValues.final_pc2).toNat

/-- The canonical field-free endpoints used by the State hand-off proof. -/
def nativeStateBoundary (statement : SupportedCoreStatement p) : StateBoundary :=
  StateBoundary.canonical (nativeInitialClock statement) (nativeInitialPc statement)
    (nativeFinalClock statement) (nativeFinalPc statement)

/-- Provider/boundary occurrences determined before preprocessed closure. -/
def nativeBaseProviderOccurrences (compiled : CompiledExecution) :
    (id : ProviderTableId) → List id.Occurrence
  | .byte _ => []
  | .range _ => []
  | .program => []
  | .memoryInit => memoryInitialEntries compiled.memoryHistory
  | .memoryFinalize => memoryFinalEntries compiled.memoryHistory
  | .memoryBump => compiled.memoryBumps
  | .stateBump => stateBumpEvents compiled.routedEvents
  | .halt => []
  -- The syscall table is empty rather than one padding row: its Exit push is positively gated, so
  -- it needs no anti-gated companion to balance the verifier's ungated pull.
  | .syscallInstrs => []

/-- Assemble the unique unclosed native trace from one chronological compiler result.  The three
preprocessed provider families are empty here; provider closure reconstructs them from
this trace's own evaluated consumer interactions. -/
noncomputable def nativeBaseTraceOfCompiled (statement : SupportedCoreStatement p)
    (compiled : CompiledExecution) (capacity : compiled.Capacity) : SupportedCoreTraceWitness p where
  instructionEvents := compiled.instructionEvents
  providerOccurrences := nativeBaseProviderOccurrences compiled
  instructionCapacity := capacity.instruction
  providerCapacity := by
    intro id
    cases id with
    | byte _ | range _ | program | halt | syscallInstrs => exact Nat.zero_le _
    | memoryInit => exact capacity.memoryInitial
    | memoryFinalize => exact capacity.memoryFinal
    | memoryBump => exact capacity.memoryBumps
    | stateBump => exact capacity.stateBumps
  generationData := Commit.dataOfAt statement.program (nativeInitialClock statement)
  hint := ProverHint.empty (ZMod p)
  boundary := statement.publicValues

/-- Total base trace.  Outside the supported compiler image this uses `compileExecution`'s empty
fallback; admissibility proves that branch unreachable. -/
noncomputable def nativeBaseTrace (statement : SupportedCoreStatement p)
    (execution : Machine.EventExecutionTrace) : SupportedCoreTraceWitness p :=
  nativeBaseTraceOfCompiled statement
    (TraceGen.compileExecution statement.program execution (nativeInitialClock statement))
    (compileExecution_capacity statement.program execution (nativeInitialClock statement))

@[simp] theorem nativeBaseTraceOfCompiled_publicValues
    (statement : SupportedCoreStatement p) (compiled : CompiledExecution) (capacity : compiled.Capacity) :
    (nativeBaseTraceOfCompiled statement compiled capacity).publicValues = statement.publicValues := rfl

@[simp] theorem nativeBaseTrace_publicValues
    (statement : SupportedCoreStatement p) (execution : Machine.EventExecutionTrace) :
    (nativeBaseTrace statement execution).publicValues = statement.publicValues := rfl

/-! ## Local trace well-formedness -/

/-- The base trace's table-local side conditions are exactly the compiler's indexed event facts,
the two refresh schedulers' facts, and the public limb bounds.  Boundary inventories are valid by
construction. -/
theorem nativeBaseTraceOfCompiled_wellFormed
    (statement : SupportedCoreStatement p) (compiled : CompiledExecution) (capacity : compiled.Capacity)
    (publicWellFormed : statement.publicValues.LimbBounds)
    (compiledWellFormed : compiled.WellFormed)
    (stateBumpsReady : StateBumpReady compiled.routedEvents) :
    (nativeBaseTraceOfCompiled statement compiled capacity).WellFormed := by
  constructor
  · intro id event member
    exact compiledWellFormed.instruction id event member
  · intro id event member
    cases id with
    | byte provider => cases provider <;> simp [nativeBaseTraceOfCompiled,
        nativeBaseProviderOccurrences] at member
    | range width => simp [nativeBaseTraceOfCompiled, nativeBaseProviderOccurrences] at member
    | program => simp [nativeBaseTraceOfCompiled, nativeBaseProviderOccurrences] at member
    | memoryInit =>
        exact memoryInitialEntries_wellFormed compiled.memoryHistory event member
    | memoryFinalize => trivial
    | memoryBump => exact compiledWellFormed.memoryBumps event member
    | stateBump => exact stateBumpEvents_wellFormed stateBumpsReady event member
    | halt => exact event.elim
    | syscallInstrs => exact event.elim
  · exact publicWellFormed

end SP1Clean.Soundness
