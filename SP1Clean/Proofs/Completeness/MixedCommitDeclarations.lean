import SP1Clean.Proofs.Completeness.MixedCommitLedger
import SP1Clean.Soundness.HostCallReceivers

/-! # Physical declaration reads of the sixteen commitment lanes

Each guarded lane emits one declaration occurrence per padded row. The sum on a given
message agrees with one pull for each actual call, including repeated writes to the same slot.
-/

namespace SP1Clean.TraceGen.CommitBanks

open Circuit Air.Flat Machine Soundness HostCommitChip WitnessGeneration

private abbrev F := ZMod SP1Prime

/-- The immutable statement entry requested by an active bank input. -/
def declaration (d : Bool) (slot : Fin 8) (input : Inputs F) : CommitmentDeclaration.Row F :=
  ⟨if d then 1 else 0, slot.val, input.call.arg2, 1⟩

private abbrev ch := CommitmentDeclaration.channel (p := SP1Prime)

/-- Every row emits its full declaration payload at its physical activity. -/
theorem lane_declarations (d : Bool) (slot : Fin 8) (rows : List Entry) (data : ProverData F) (fit) :
    (laneTable d slot rows data fit).interactionsWith ch.toRaw =
      (guardedRows (lane slot rows)).map (fun r => ch.pulledIfValue r.2 (declaration d slot r.1)) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger
  intro env
  have argument := HostCallReceivers.commit_message (p := SP1Prime) d slot env
  change Eval.eval env (varFromOffset (F := F) RowInput 0).1.call = _ at argument
  have value : Eval.eval env (varFromOffset (F := F) RowInput 0).1.call.arg2 =
      (valueFromOffset RowInput 0 env).1.call.arg2 := by
    rw [← argument]
    simp only [circuit_norm]
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
  change (((circuit d slot).main (varFromOffset (F := F) RowInput 0)).operations (size RowInput)).interactionValuesWith ch.toRaw env = _
  rw [guarded_declaration_values]
  rw [Guarded.eval_activity, eval_varFromOffset_valueFromOffset]
  simp only [circuit_norm] at value
  simp only [CommitmentDeclaration.request, declaration, circuit_norm, value]
  rfl

/-- Active declaration requests in physical lane order, keeping every repeated read. -/
def bankRequests (d : Bool) (rows : List Entry) : List (CommitmentDeclaration.Row F) :=
  (List.finRange 8).flatMap fun slot => (lane slot rows).map (declaration d slot)

/-- Number of declaration sites over the eight physical table heights. -/
def declarationSites (rows : List Entry) : ℕ :=
  ((List.finRange 8).map fun slot => demandHeight (lane slot rows).length).sum

/-- The signed ledger of the original lane tables at their generated heights. -/
noncomputable def declarationLedger (d : Bool) (rows : List Entry) (data : ProverData F)
    (fits : ∀ slot, demandHeight (lane slot rows).length ≤ UInt64.size) : List (Interaction F) :=
  (List.finRange 8).flatMap fun slot => (laneTable d slot rows data (fits slot)).interactionsWith ch.toRaw

theorem declarationLedger_length (d : Bool) (rows : List Entry) (data : ProverData F) (fits) :
    (declarationLedger d rows data fits).length = declarationSites rows := by
  simp only [declarationLedger, declarationSites, List.length_flatMap,
    lane_declarations, List.length_map, guardedRows_length]

/-- Zero-activity rows contribute their physical site and zero signed multiplicity. -/
theorem declarationLedger_sum (d : Bool) (rows : List Entry) (data : ProverData F) (fits) (msg : Array F) :
    balanceOf (declarationLedger d rows data fits) msg = balanceOf ((bankRequests d rows).map ch.pulledValue) msg := by
  unfold declarationLedger bankRequests
  rw [List.map_flatMap]
  generalize List.finRange 8 = slots
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
    simp only [List.flatMap_cons, balanceOf_append, ih]
    rw [lane_declarations, WitnessGeneration.guarded_pull_sum]

/-- The public event limit bounds each rounded lane height independently of the argument values. -/
theorem declarationSites_le (rows : List Entry) (count : rows.length ≤ 2^21) :
    declarationSites rows ≤ 8 * 2^21 := by
  have each (slot : Fin 8) : demandHeight (lane slot rows).length ≤ 2^21 :=
    demandHeight_le_pow ((List.length_filterMap_le ..).trans count)
  have total := List.sum_le_sum (l := List.finRange 8) (f := fun slot => demandHeight (lane slot rows).length)
    (g := fun _ => 2^21) (fun slot _ => each slot)
  simpa only [declarationSites, List.map_const', List.length_finRange, List.sum_replicate_nat] using total

end SP1Clean.TraceGen.CommitBanks
