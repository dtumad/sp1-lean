import Clean.Air.Balance
import ToClean.Air.StaticProvider
import ToClean.Air.TableBuild

/-! # Physical static-membership fixtures

Shared test construction for verifier-fixed membership rows. Counts come from the supplied
consumer ledger; the fixed messages and every physical row come from the component's own
fixed-column program. Actual circuit generation and interaction evaluation remain Clean's.
These fixtures do not implement the production channel scheduler.
-/

namespace SP1CleanTest.StaticMembership

open Circuit Air.Flat

variable {F : Type} [FiniteField F]

/-- Channel names, message cells and signed multiplicities in physical occurrence order. -/
abbrev Ledger (F : Type) := List (String × List F × F)

open WitnessGeneration

/-- Evaluate the upstream input program with no private hint, keeping each fixed cell literal. -/
def inputAt {Input : TypeMap} [ProvableType Input] (mode : PreallocatedMode F Input)
    (index : UInt64) (multiplicity : F) : Input F :=
  let (cells, steps) := inputCells (mode.input .idx)
  fromElements (cells.map (Cell.eval (inputContext steps (rowEnvironment (.empty F)) index.toNat) multiplicity))

private theorem inputAt_fixed {Input : TypeMap} [ProvableType Input]
    (mode : PreallocatedMode F Input) (index : UInt64) (multiplicity : F) :
    mode.FixedAt index (inputAt mode index multiplicity) := by
  simp only [PreallocatedMode.FixedAt, inputAt, inputCells, ProvableType.toElements_fromElements,
    Vector.toList_map, List.forall₂_map_right_iff]
  apply List.forall₂_same.mpr
  intro cell _
  cases cell <;> simp [Cell.FixedMatches, Cell.eval]

/-- Counts are allocated to the first eligible occurrence; all later and padding rows remain. -/
def count {Input : TypeMap} [ProvableType Input] (mode : PreallocatedMode F Input)
    (ledger : Ledger F) (index : UInt64) : F :=
  let cells := (toElements (inputAt mode index 0)).toArray
  let message := cells.take (size mode.Message)
  if (cells.size == size mode.Message + 2 && cells[size mode.Message]?.getD 0 == 0) ||
      (List.range index.toNat).any (fun earlier =>
        (toElements (inputAt mode (UInt64.ofNat earlier) 0)).toArray.take (size mode.Message) == message) then 0
  else -((ledger.filter fun entry => entry.1 == mode.channel.name && entry.2.1 == message.toList).map (·.2.2)).sum

/-- Materialize every upstream preallocated row, including unused rows. -/
def preallocatedTable (component : Component F) (mode : PreallocatedMode F component.Input)
    (generation : component.generation = .preallocated mode) (ledger : Ledger F)
    (data : ProverData F) (hint : ProverHint F) : Table F :=
  let inputs := List.ofFn fun index : Fin mode.height.toNat =>
    inputAt mode (UInt64.ofNat index.val) (count mode ledger (UInt64.ofNat index.val))
  let ownData := component.inputData inputs data
  Table.build component inputs ownData hint
    (by simp only [inputs, List.length_ofFn]; exact mode.height.toNat_lt_size.le)
    (by
      simp only [Component.FixedRowsMatch, generation, List.length_map, inputs, List.length_ofFn]
      refine ⟨True.intro, ?_⟩
      intro index bound
      simp only [List.getElem_map, List.getElem_ofFn, Component.rowPrefix_buildRow,
        ProvableType.fromElements_toElements]
      exact inputAt_fixed _ _ _)
    (component.inputData_consistent inputs data)

/-- Evaluate the actual physical provider, including every zero-count occurrence. -/
def table {Row : TypeMap} [ProvableType Row] (source : StaticTable F Row) (ledger : Ledger F)
    (bounded : source.height < UInt64.size := by decide) : Table F :=
  preallocatedTable (source.component bounded) (source.generation bounded) rfl ledger
    (.empty F) (.empty F)

/-- The canonical interaction ledger of the actual provider rows. -/
def providerLedger {Row : TypeMap} [ProvableType Row] (source : StaticTable F Row)
    (ledger : Ledger F) (bounded : source.height < UInt64.size := by decide) : Ledger F :=
  (table source ledger bounded).interactions.map fun interaction =>
    (interaction.channel.name, interaction.msg.toList, interaction.signedMult)

/-- Evaluate a fixed payload provider on its semantic channel, retaining unused occurrences. -/
def payloadLedger {Row : TypeMap} [ProvableType Row] (source : StaticTable F Row)
    (channel : Channel F Row) (valid : ∀ row, source.Spec row → ∀ data, channel.Guarantees row data)
    (ledger : Ledger F) (bounded : source.height < UInt64.size) : Ledger F :=
  let physical := preallocatedTable (source.payloadComponent channel valid bounded)
    (source.payloadGeneration channel bounded) rfl ledger (.empty F) (.empty F)
  physical.interactions.map fun interaction =>
    (interaction.channel.name, interaction.msg.toList, interaction.signedMult)

/-- A subsystem membership check retains forged messages in the complete ledger. -/
def check {Row : TypeMap} [ProvableType Row] (source : StaticTable F Row) (ledger : Ledger F)
    (bounded : source.height < UInt64.size := by decide) : Bool :=
  let complete := (ledger ++ providerLedger source ledger bounded).filter (fun entry => entry.1 == source.channel.name)
  complete.all fun entry =>
    ((complete.filter (fun other => other.2.1 == entry.2.1)).map (·.2.2)).sum == 0

/-- Generate demand only from components declaring the selected channel. Unrelated rows need
not be regenerated to compute membership counts; their full constraints and ledgers are still
checked in the assembled witness. Channel declarations cover actual circuit interactions. -/
def demandLedger (components : List (Component F)) (inputs : ℕ → List (List F))
    (channels : List String) (data : ProverData F) (hint : ProverHint F) : Ledger F :=
  components.zipIdx.flatMap fun (component, index) =>
    if component.circuit.channels.any (fun declared => channels.contains declared.name) then
      (inputs index).flatMap fun cells =>
        let input : component.Input F :=
          fromElements (Vector.ofFn fun cell => cells[cell.val]?.getD 0)
        let env := Environment.fromArray (component.buildRow input data hint) data
        (component.rowOperations.interactionValues env).filterMap fun interaction =>
          if channels.contains interaction.channel.name then
            some (interaction.channel.name, interaction.msg.toList, interaction.signedMult)
          else none
    else []

/-- Fixture seeds supply dynamic rows; preallocated rows come from their declared input program. -/
def acceptsSeed (component : Component F) : Bool :=
  match component.generation with
  | .demand _ => true
  | .preallocated _ => false

/-- Ordinary fixture inputs retain order; fixed providers retain their entire upstream inventory. -/
def buildTable (component : Component F) (inputs : List (component.Input F))
    (ledger : Ledger F) (data : ProverData F) (hint : ProverHint F)
    (bounded : inputs.length ≤ UInt64.size) : Table F :=
  match generation : component.generation with
  | .preallocated mode => preallocatedTable component mode generation ledger data hint
  | .demand _ => Table.build component inputs (component.inputData inputs data) hint bounded
      (by simp [Component.FixedRowsMatch, generation]) (component.inputData_consistent inputs data)

@[simp] theorem buildTable_component (component : Component F) (inputs : List (component.Input F))
    (ledger : Ledger F) (data : ProverData F) (hint : ProverHint F)
    (bounded : inputs.length ≤ UInt64.size) :
    (buildTable component inputs ledger data hint bounded).component = component := by
  unfold buildTable
  split <;> rfl

/-- Build all registered fixtures without dropping inactive or repeated entries. -/
def buildTables (components : List (Component F)) (inputs : ℕ → List (List F))
    (ledger : Ledger F) (data : ProverData F) (hint : ProverHint F)
    (bounded : ∀ index : Fin components.length, (inputs index.val).length ≤ UInt64.size) : List (Table F) :=
  List.ofFn fun index : Fin components.length =>
    let component := components[index]
    buildTable component ((inputs index.val).map fun cells =>
      fromElements (Vector.ofFn fun cell => cells[cell.val]?.getD 0))
      ledger data hint (by simpa only [List.length_map] using bounded index)

/-- Construction preserves the whole physical inventory and its order. -/
theorem buildTables_components (components : List (Component F)) (inputs : ℕ → List (List F))
    (ledger : Ledger F) (data : ProverData F) (hint : ProverHint F)
    (bounded : ∀ index : Fin components.length, (inputs index.val).length ≤ UInt64.size) :
    (buildTables components inputs ledger data hint bounded).map (·.component) = components := by
  simp only [buildTables, List.map_ofFn, Function.comp_def, buildTable_component]
  exact List.ofFn_getElem

end SP1CleanTest.StaticMembership
