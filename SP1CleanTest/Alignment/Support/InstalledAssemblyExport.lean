import SP1CleanTest.Alignment.Support.InstalledAssembly
import Clean.Backends.Program

/-! # Export of the complete installed native assembly

Production components own their typed generation modes. This fixture only encodes private inputs
for those modes, through Clean's named hint tables and the shared sparse index. Clean owns row
completion, scheduling, AIR lowering and Rust printing. Finite comparisons do not claim general
witness-generation completeness or correctness of lowering.
-/

namespace SP1CleanTest.Alignment.InstalledAssemblyExport

open Circuit Air.Flat SP1Clean SP1Clean.Soundness SP1CleanTest.Alignment.InstalledAssembly
open SP1Clean.Export.InstalledAssembly

/-- Encoded private inputs and their upstream hint-table views. `samples` identifies each physical
component's first supplied input for mutation tests; it is not the generation hint schema. -/
structure Prepared where
  data : Array Fp
  hints : List HintTable
  samples : List HintTable

private def word (message : Array Fp) (offset width : ℕ) : ℕ :=
  (List.range width).foldl (fun acc digit =>
    acc + (message[offset + digit]?.getD 0).val * 65536 ^ digit) 0

private def clock (message : Array Fp) : ℕ :=
  (message[0]?.getD 0).val * 16777216 + (message[1]?.getD 0).val

/-- Read the actual circuit's response to its demand channel, using upstream row completion. -/
private def response (component : Component Fp) (seed : Seed)
    (channel : String) (trigger : Channel.Direction) : Except String (Array Fp) := do
  let data := ProverData.empty Fp
  let row := seed.build component data
  let some interaction := (component.operations.interactionValues (Environment.fromArray row data)).find?
      (fun interaction => interaction.channel.name == channel &&
        interaction.direction != trigger && interaction.mult != 0)
    | throw s!"{component.circuit.name}: supplied input has no active demand response"
  pure interaction.msg

/-- Encode all private inputs once. Duplicate keys, invalid widths and unsupported input routes
fail before either Lean generation or Rust export. No mode is replaced or preallocated here. -/
def prepare (context : Context) (consumers : List Seed) : Except String Prepared := do
  let tables := (assembly context).tables
  let (consumers, hintClock) ← fixtureInputs context consumers
  let mut data : Array Fp := #[]
  let mut hints : List HintTable := []
  let mut samples : List HintTable := []
  let mut indices : List (String × Array (Array Fp)) := []
  for (component, position) in tables.zipIdx do
    let seeds := consumers.filter (·.table == position)
    let inputs := seeds.map (fun seed => (seed.cells.toArray))
    let mut encoded := inputs.toArray
    if component.circuit.name == HostHintQueueTerminal.tableName then
      let descriptor : HintTable := { key := HostHintQueueTerminal.tableName, width := 2, offset := data.size, rows := 1 }
      hints := hints ++ [descriptor]
      samples := samples ++ [descriptor]
      data := data ++ #[((hintClock / 2 ^ 24 : ℕ) : Fp), ((hintClock % 2 ^ 24 : ℕ) : Fp)]
      continue
    let mut first := 0
    if !seeds.isEmpty then
      match component.generation with
      | .preallocated _ => throw "immutable providers do not accept fixture inputs"
      | .demand mode =>
        let name := mode.channel.name
        if name == "SP1State" && position != 56 then
          let keyed ← seeds.mapM fun seed => do
            let message ← response component seed name mode.trigger
            let time := clock message
            unless time ≥ context.source.clock && (time - context.source.clock) % 8 == 0 do
              throw "instruction hint clock does not occupy a relative eight-clock slot"
            pure ((time - context.source.clock) / 8, seed.cells.toArray)
          unless (keyed.map Prod.fst).Nodup do throw "duplicate instruction hint slot"
          let height := keyed.foldl (fun height entry => max height (entry.1 + 1)) 0
          encoded := Array.replicate height (Array.replicate component.rowOffset 0)
          for (slot, input) in keyed do encoded := encoded.set! slot input
          first := (keyed.head?.map Prod.fst).getD 0
        else if name == (InstructionReceipt.channel (p := SP1Prime)).name ||
            position ∈ [0, 1, 3, 4, 55, 57, 63, 64, 65] ||
            (66 ≤ position && position ≤ 85) || position == 94 || position == 95 then
          let keyed ← seeds.mapM fun seed => do
            let message ← response component seed name mode.trigger
            let keys :=
              if name == "sp1.native.host_call" || name == (InstructionReceipt.channel (p := SP1Prime)).name then [clock message]
              else if name == "sp1.native.hint_read_state" then [clock message, word message 5 3]
              else if name == "SP1Exit" then [word message 0 1]
              else if name == "SP1Memory" then [clock message * 32 + word message 2 1]
              else if position == 94 || position == 95 then [word message 2 3]
              else [word message 0 4]
            unless keys.all (· < UInt64.size) do throw "private-input key exceeds UInt64"
            pure (keys.map UInt64.ofNat, rowPrefix component.rowOffset seed.cells.toArray)
          let prepared ← Witgen.HintIndex.prepareKeys (Input := fields component.rowOffset) keyed
          encoded := prepared.inputs.map (·.toArray)
          indices := indices ++ [(component.circuit.name ++ ".index", prepared.index.map (·.toArray))]
          first := 1
        else if seeds.length > 1 then
          throw s!"{component.circuit.name}: terminal hint must have exactly one input"
    let descriptor : HintTable := {
      key := component.circuit.name, width := component.rowOffset, offset := data.size, rows := encoded.size }
    hints := hints ++ [descriptor]
    samples := samples ++ [{ descriptor with
      offset := data.size + first * component.rowOffset
      rows := seeds.length }]
    data := data ++ encoded.flatten
  for (name, rows) in indices do
    hints := hints ++ [{ key := name, width := 1, offset := data.size, rows := rows.size }]
    data := data ++ rows.flatten
  hints := hints ++ [{ key := "sp1.state.origin", width := 2, offset := data.size, rows := 1 }]
  data := data ++ #[((context.source.clock / 16777216 : ℕ) : Fp), ((context.source.clock % 16777216 : ℕ) : Fp)]
  hints := hints ++ [{ key := SP1Clean.OrdinaryObservation.terminalModeHint, width := 1, offset := data.size, rows := 1 }]
  data := data.push (SP1Clean.OrdinaryObservation.Mode.of context.source.sail context.target.sail).sentinel
  pure ⟨data, hints, samples⟩

/-- Native generation uses the same upstream scheduler and private-input schema as emitted Rust. -/
def generate (context : Context) (prepared : Prepared) (publicInput : SP1PublicIO Fp)
    (input : fields prepared.data.size Fp := ⟨prepared.data, rfl⟩) :=
  WitnessGeneration.generate (proverAssembly context (fields prepared.data.size) prepared.hints) 4096 publicInput input
    |>.mapError toString

/-- Built-in validated lowering, shared by inline and shared-module emission. -/
def exportProgram (context : Context) (consumers : List Seed) : Except String (Backends.Program Fp) := do
  let prepared ← prepare context consumers
  Backends.lower (proverAssembly context (fields prepared.data.size) prepared.hints) 4096 |>.mapError toString

end SP1CleanTest.Alignment.InstalledAssemblyExport
