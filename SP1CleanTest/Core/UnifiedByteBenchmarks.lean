import SP1CleanTest.Core.UnifiedByteExport
import SP1CleanTest.Core.NonVacuityReal
import SP1Clean.Proofs.Chips.ByteChip.RangeChip

/-! # Comparable workloads for the byte-provider decision

The installed 23-provider layout uses preallocated, counted rows with no demand handlers.
The prototype uses Clean's demand scheduler. Both close the same literal public requests;
each keeps its own physical padding and occurrence count. Three workloads are projected
from existing checked ADD, BEQ and LB circuit rows, rather than hand-authored byte requests.
-/

namespace SP1CleanTest.Core.UnifiedByteBenchmarks

open Air.Flat Circuit SP1Clean SP1Clean.ByteChip
open ComponentExport (Fp)
open UnifiedByteExport (Requests request)

def components : List (Component Fp) :=
  [{ circuit := AndByte.circuit, Assumptions := (AndByte.circuit).Assumptions }, { circuit := OrByte.circuit, Assumptions := (OrByte.circuit).Assumptions },
   { circuit := XorByte.circuit, Assumptions := (XorByte.circuit).Assumptions }, { circuit := U8Range.circuit, Assumptions := (U8Range.circuit).Assumptions },
   { circuit := Ltu.circuit, Assumptions := (Ltu.circuit).Assumptions }, { circuit := MSB.circuit, Assumptions := (MSB.circuit).Assumptions }] ++
  RangeChip.allWidths.map fun width => { circuit := RangeChip.circuitFor width, Assumptions := (RangeChip.circuitFor width).Assumptions }

def ensemble (n : ℕ) : Ensemble Fp (Requests n) where
  tables := components
  unique_names := by decide
  channels := [Channels.byteChannel.toRaw]
  verifier := UnifiedByteExport.verifier n

private theorem lookup_inventory : components.map (fun c => c.operations.lookups) =
    List.replicate 23 [] := by
  simp [components, Component.lookups_eq, Component.rowOperations,
    AndByte.circuit, OrByte.circuit, XorByte.circuit, U8Range.circuit, Ltu.circuit, MSB.circuit,
    AndByte.main, OrByte.main, XorByte.main, U8Range.main, Ltu.main, MSB.main,
    RangeChip.circuitFor, RangeChip.circuit, RangeChip.allWidths,
    Gadgets.BitwiseByte.circuit, Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits,
    Function.comp_def, circuit_norm]

private theorem channel_inventory :
    components.map (fun c => c.operations.interactions.map (·.channel)) =
      List.replicate 23 [(Channels.byteChannel (p := SP1Prime)).toRaw] := by
  simp [components, Component.interactions_eq, Component.rowOperations,
    AndByte.circuit, OrByte.circuit, XorByte.circuit, U8Range.circuit, Ltu.circuit, MSB.circuit,
    AndByte.main, OrByte.main, XorByte.main, U8Range.main, Ltu.main, MSB.main,
    RangeChip.circuitFor, RangeChip.circuit, RangeChip.main, RangeChip.allWidths,
    Gadgets.BitwiseByte.circuit, Gadgets.BitwiseByte.main,
    Gadgets.ToBits.toBits, Gadgets.ToBits.rangeCheck, Gadgets.ToBits.main, Gadgets.Equality.main,
    GeneralFormalCircuit.toSubcircuit_interactions, FormalAssertion.toSubcircuit_interactions,
    Circuit.interactions_forEach, Function.comp_def, circuit_norm]

def description (n : ℕ) : Air.Flat.EnsembleCheck (ensemble n) where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    intro component member lookup used
    change component ∈ components at member
    have present := List.mem_map_of_mem (f := fun c : Component Fp => c.operations.lookups) member
    rw [lookup_inventory] at present
    have empty := (List.mem_replicate.mp present).2
    simp [empty] at used
  channels_unique := by simp [ensemble]
  channels_complete := by
    intro component member interaction used
    change component ∈ components at member
    have present := List.mem_map_of_mem
      (f := fun c : Component Fp => c.operations.interactions.map (·.channel)) member
    rw [channel_inventory] at present
    have channels := (List.mem_replicate.mp present).2
    have found := List.mem_map_of_mem (f := fun i : AbstractInteraction Fp => i.channel) used
    simpa only [channels, ensemble] using found
  verifier_channels_complete := (UnifiedByteExport.description n).verifier_channels_complete

/-- Aggregate only fixture inputs; allocation and witness generation remain Clean's job. -/
def inputs (rows : List (ByteRow Fp)) (table : ℕ) : List (Array Fp) :=
  let messages := rows.map fun row => (toElements row).toArray
  messages.eraseDups.filterMap fun key =>
    let opcode := key[0]!.val
    let index := if opcode = 6 then 6 + key[2]!.val else opcode
    if index != table then none else
    let count : Fp := messages.count key
    if opcode = 6 then some #[key[1]!, count]
    else if opcode = 5 then some #[key[2]!, count]
    else some #[key[2]!, key[3]!, count]

def mode (width : ℕ) (rows : List (Array Fp)) : Except String (WitnessGeneration.Mode Fp) := do
  if bounded : rows.length < UInt64.size then
    return .preallocated {
      rows := UInt64.ofNatLT rows.length bounded
      input := .ofFExprs (Vector.ofFn fun column : Fin width =>
        if rows.isEmpty then .const 0
        else .listGet ((rows.map fun row => row[column.val]?.getD 0).map .const) .idx)
      input_valid := by
        simp only [Witgen.RowProgram.Valid, Witgen.RowProgram.ofFExprs,
          Witgen.VExpr.validForRow, Vector.toList_ofFn, List.all_nil, Bool.true_and,
          decide_eq_true_eq, List.all_eq_true, List.forall_mem_ofFn_iff]
        intro column
        split
        · rfl
        · simp only [Witgen.FExpr.validForRow, Witgen.U64Expr.validForRow, Bool.and_true]
          exact Witgen.FExprList.validForRow_map_const _ _
      handlers := []
    }
  else throw "precounted fixture exceeds the physical row index"

def config (rows : List (ByteRow Fp)) : Except String (WitnessGeneration.Config Fp) := do
  let generations ← components.zipIdx.mapM fun (component, index) => do
    let mode ← mode component.rowOffset (inputs rows index)
    return (component.circuit.name, ({
      mode
      padding := { input := Array.replicate component.rowOffset 0 }
    } : WitnessGeneration.Generation Fp))
  return { components := generations, fuel := 128 }

def generate (rows : List (ByteRow Fp)) : Except String (EnsembleWitness (ensemble rows.length)) :=
  match config rows with
  | .error error => .error error
  | .ok config =>
    WitnessGeneration.generate (ComponentExport.fixture (ensemble rows.length)) config
      ⟨rows.toArray, by simp⟩ () |>.mapError toString

structure Source where
  name : String
  component : Component Fp
  input : component.Input Fp

def sources : List Source :=
  let add : Component Fp := { circuit := AddChip.circuit, Assumptions := (AddChip.circuit).Assumptions }
  [{ name := "add", component := add,
     input := fromElements (Vector.ofFn fun i =>
       (SP1Clean.TraceGenTests.rTypeEventInputs NonVacuityRealTests.addEvent)[i.val]?.getD 0) },
   { name := "beq", component := { circuit := BranchChip.circuit, Assumptions := (BranchChip.circuit).Assumptions },
     input := NonVacuityRealTests.branchBeqInputs },
   { name := "load-byte", component := { circuit := LoadByteChip.circuit, Assumptions := (LoadByteChip.circuit).Assumptions },
     input := NonVacuityRealTests.loadByteInputs }]

def Source.row (source : Source) : Array Fp :=
  source.component.buildRow source.input (fun _ _ => #[]) (ProverHint.empty _)

def Source.interactions (source : Source) : List (Interaction Fp) :=
  source.component.rowOperations.interactionValues (Environment.fromArray source.row (fun _ _ => #[]))

def Source.requests (source : Source) : Except String (List (ByteRow Fp)) := do
  let mut requests := []
  for entry in source.interactions do
    if entry.channel.name == "SP1Byte" && entry.mult != 0 then
      unless entry.assumeGuarantees && entry.mult == -1 && entry.msg.size == 4 do
        throw s!"unexpected byte demand in {source.name}"
      requests := requests ++ [fromElements (Vector.ofFn fun i => entry.msg[i.val]?.getD 0)]
  return requests

def workloads : Except String (List (String × List (ByteRow Fp))) := do
  let actual ← sources.mapM fun source => return (source.name, ← source.requests)
  return [("empty", []), ("and-only", [request 0 128 128 255]),
    ("range-heavy", (List.range 32).map fun value => request 6 value 16 0),
    ("mixed", [request 0 128 128 255, request 1 255 128 127, request 2 255 128 127,
      request 3 0 255 0, request 4 1 127 128, request 5 1 128 0, request 6 65535 16 0]),
    ("distinct-64", (List.range 64).map fun value => request 6 value 16 0),
    ("distinct-65", (List.range 65).map fun value => request 6 value 16 0)] ++ actual

def rustExports : Except String (List (String × Except String String)) := do
  return (← workloads).flatMap fun (name, rows) =>
    [(s!"byte_baseline_{name}.rs", (config rows).bind fun config => Backends.Plonky3.Print.ensembleToRust
        (ComponentExport.fixture (ensemble rows.length)) config),
     (s!"byte_candidate_{name}.rs", Backends.Plonky3.Print.ensembleToRust
        (ComponentExport.fixture (UnifiedByteExport.ensemble rows.length)) UnifiedByteExport.config)]

theorem exports_succeed : (rustExports.map fun entries => entries.all (·.2.isOk)) = .ok true := by
  native_decide

end SP1CleanTest.Core.UnifiedByteBenchmarks
