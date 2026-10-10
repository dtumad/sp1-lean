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

abbrev Ledger (F : Type) := List (String × List F × F)

/-- Assign demand to the first matching physical row. Repeated fixed messages remain as
zero-count rows, and unmatched demand remains unbalanced. -/
def suffix (channel : String) (ledger : Ledger F) (fixed : FixedColumns F) (index : ℕ) : Array F :=
  if (List.range index).any (fun prior => fixed.row prior == fixed.row index) then #[0] else
  #[-((ledger.filter fun entry => entry.1 == channel && entry.2.1 == (fixed.row index).toList).map
    (·.2.2)).sum]

/-- Evaluate the actual physical provider, including every zero-count occurrence. -/
def table {Row : TypeMap} [ProvableType Row] (source : StaticTable F Row) (ledger : Ledger F) : Table F :=
  Table.buildPreallocated source.component source.fixedColumns rfl
    (suffix source.channel.name ledger source.fixedColumns) (fun _ _ => #[]) (ProverHint.empty F)

/-- The canonical interaction ledger of the actual provider rows. -/
def providerLedger {Row : TypeMap} [ProvableType Row] (source : StaticTable F Row)
    (ledger : Ledger F) : Ledger F :=
  ((table source ledger).interactions (fun _ _ => #[])).map fun interaction =>
    (interaction.channel.name, interaction.msg.toList, interaction.mult)

/-- A subsystem membership check retains forged messages in the complete ledger. -/
def check {Row : TypeMap} [ProvableType Row] (source : StaticTable F Row) (ledger : Ledger F) : Bool :=
  let complete := (ledger ++ providerLedger source ledger).filter (fun entry => entry.1 == source.channel.name)
  complete.all fun entry =>
    ((complete.filter (fun other => other.2.1 == entry.2.1)).map (·.2.2)).sum == 0

/-- Generate demand only from components declaring the selected channel. Unrelated rows need
not be regenerated to compute membership counts; their full constraints and ledgers are still
checked in the assembled witness. Channel declarations cover actual circuit interactions. -/
def demandLedger (components : List (Component F)) (inputs : ℕ → List (List F))
    (channel : String) (data : ProverData F) (hint : ProverHint F) : Ledger F :=
  components.zipIdx.flatMap fun (component, index) =>
    if component.circuit.channels.any (fun declared => declared.name == channel) then
      (inputs index).flatMap fun cells =>
        let input : component.Input F :=
          fromElements (Vector.ofFn fun cell => cells[cell.val]?.getD 0)
        let env := Environment.fromArray (component.buildRow input data hint) data
        (component.rowOperations.interactionValues env).filterMap fun interaction =>
          if interaction.channel.name == channel then
            some (interaction.channel.name, interaction.msg.toList, interaction.mult)
          else none
    else []

/-- Keep each installed component and its fixed rows. Current snapshot assemblies have one
fixed membership provider; ordinary components retain the supplied input order verbatim. -/
def buildTables (components : List (Component F)) (inputs : ℕ → List (List F))
    (channel : String) (ledger : Ledger F) (data : ProverData F) (hint : ProverHint F) : List (Table F) :=
  List.ofFn fun index : Fin components.length =>
    let component := components[index]
    Table.buildWithFixed component ((inputs index.val).map fun cells =>
      fromElements (Vector.ofFn fun cell => cells[cell.val]?.getD 0))
      (suffix channel ledger) data hint

/-- Construction preserves the whole physical inventory and its order. -/
theorem buildTables_components (components : List (Component F)) (inputs : ℕ → List (List F))
    (channel : String) (ledger : Ledger F) (data : ProverData F) (hint : ProverHint F) :
    (buildTables components inputs channel ledger data hint).map (·.component) = components := by
  simp only [buildTables, List.map_ofFn, Function.comp_def, Table.buildWithFixed_component]
  exact List.ofFn_getElem

end SP1CleanTest.StaticMembership
