import SP1Clean.Proofs.Completeness.MixedCommitTables
import ToClean.Air.GuardedLedger
import ToMathlib.ListChronology

/-! # Closing each original commitment bank's signed state ledger

Grouping by the physical lane permutes every chronological update exactly once. Padding remains
in the physical ledgers with zero weight, and the one terminal transfers the last update to the
verifier's outgoing timestamp.
-/

namespace SP1Clean.TraceGen.CommitBanks

open Circuit Air.Flat Machine Soundness HostCommitChip
open WitnessGeneration

private abbrev F := ZMod SP1Prime

private def pair (d : Bool) (r : Entry) : List (Interaction F) :=
  [(stateChannel d).pulledValue r.2.previous, (stateChannel d).pushedValue (r.2.next r.1)]

private def guardedPair (d : Bool) (slot : Fin 8) (r : RowInput F) : List (Interaction F) :=
  [(stateChannel d).pulledIfValue r.2 r.1.previous, (stateChannel d).pushedIfValue r.2 (r.1.next slot)]

/-- The actual physical bank lane emits both state occurrences on every padded row. -/
theorem lane_ledger (d : Bool) (slot : Fin 8) (rows : List Entry) (data : ProverData F) (fit) :
    (laneTable d slot rows data fit).interactionsWith (stateChannel d).toRaw =
      (guardedRows (lane slot rows)).flatMap (guardedPair d slot) := by
  apply Table.ofInputs_ledger
  intro env
  have point := (HostCommitHistory.view (p := SP1Prime) d slot).interactions env
  rw [point]
  simp only [HostCommitHistory.view, Guarded.eval_activity, eval_varFromOffset_valueFromOffset, guardedPair]
  rfl

/-- The unpadded terminal consumes its last real state and emits the verifier's sentinel. -/
theorem terminal_ledger (d : Bool) (last : State F) (data : ProverData F) :
    (terminalTable d last data).interactionsWith (stateChannel d).toRaw =
      [(stateChannel d).pulledValue last, (stateChannel d).pushedValue (HostCommitBoundary.final last.values)] := by
  let values (s : State F) := [(stateChannel d).pulledValue s, (stateChannel d).pushedValue (HostCommitBoundary.final s.values)]
  change _ = [last].flatMap values
  apply Table.ofInputs_ledger
  intro env
  exact (HostCommitBank.terminalView (p := SP1Prime) d).interactions env

private theorem stable_lane (slot : Fin 8) (rows : List Entry) :
    lane slot rows = (rows.filter (fun r => decide (r.1 = slot))).map Prod.snd := by
  induction rows with
  | nil => rfl
  | cons r rest ih =>
    by_cases selected : r.1 = slot <;> simp [lane, selected, ← ih]

private theorem lane_sum (d : Bool) (slot : Fin 8) (rows : List Entry) (data : ProverData F) (fit) (msg : Array F) :
    balanceOf ((laneTable d slot rows data fit).interactionsWith (stateChannel d).toRaw) msg =
      balanceOf ((rows.filter (fun r => decide (r.1 = slot))).flatMap (pair d)) msg := by
  rw [lane_ledger, guardedRows_balanceOf _ _ _ ?_, stable_lane, List.flatMap_map]
  · apply congrArg (balanceOf · msg)
    apply List.flatMap_congr
    intro r selected
    obtain rfl := of_decide_eq_true (List.mem_filter.mp selected).2
    rfl
  · simp only [guardedPair, balanceOf_cons, Channel.pulledIfValue, Channel.pushedIfValue,
      Interaction.signedMult, show (0 : RowInput F).2 = 0 from rfl, neg_zero, ite_self,
      show balanceOf ([] : List (Interaction F)) msg = 0 from rfl, add_zero]

private theorem bank_sum (d : Bool) (rows : List Entry) (data : ProverData F) (fit : ∀ slot : Fin 8, demandHeight (lane slot rows).length ≤ UInt64.size)
    (msg : Array F) :
    balanceOf ((List.finRange 8).flatMap (fun slot =>
      (laneTable d slot rows data (fit slot)).interactionsWith (stateChannel d).toRaw)) msg =
      balanceOf (rows.flatMap (pair d)) msg := by
  have grouped (keys : List (Fin 8)) : balanceOf (keys.flatMap (fun slot =>
      (laneTable d slot rows data (fit slot)).interactionsWith (stateChannel d).toRaw)) msg =
      balanceOf ((keys.flatMap (fun slot => rows.filter (fun r => decide (r.1 = slot)))).flatMap (pair d)) msg := by
    induction keys with
    | nil => rfl
    | cons slot rest ih => simp only [List.flatMap_cons, List.flatMap_append, balanceOf_append, lane_sum, ih]
  rw [grouped]
  apply balanceOf_perm
  apply List.Perm.flatMap_right
  exact List.flatMap_filter_key_perm _ rows Prod.fst (by decide) (by simp)

/-- The original bank's two verifier endpoints and its nine tables have zero net field
multiplicity for every state, including repeated values and the no-call path. -/
theorem state_balanced (d : Bool) (rows : List Entry) (first last : State F) (data : ProverData F) (fit)
    (chain : first :: rows.map (fun r => r.2.next r.1) = rows.map (fun r => r.2.previous) ++ [last]) :
    LogUpBalanced ([(stateChannel d).pushedValue first, (stateChannel d).pulledValue (HostCommitBoundary.final last.values)] ++
      HostCommitBank.indices.flatMap (fun i => (bankTable d rows last data fit i).interactionsWith (stateChannel d).toRaw)) := by
  let ch := stateChannel (p := SP1Prime) d
  let edge (r : Entry) := (r.2.previous,r.2.next r.1)
  have ordered : (first :: rows.map (fun r => (edge r).2)).Perm (last :: rows.map (fun r => (edge r).1)) := by
    rw [show rows.map (fun r => (edge r).2) = rows.map (fun r => r.2.next r.1) from rfl, chain]
    exact List.perm_append_comm ..
  have closed := (ch.transitionLedger_balanced_iff first last rows edge).mpr ordered
  have boolean : ∀ x ∈ ch.transitionLedger first last rows edge, IsBool x.mult := by
    intro x member
    change x ∈ [ch.pushedValue first,ch.pulledValue last] ++ rows.flatMap (pair d) at member
    rcases List.mem_append.mp member with endpoint | row
    · rcases List.mem_cons.mp endpoint with rfl | rest
      · exact Or.inr rfl
      · obtain rfl := List.mem_singleton.mp rest
        exact Or.inr rfl
    · obtain ⟨r, _, given⟩ := List.mem_flatMap.mp row
      rcases List.mem_cons.mp given with rfl | rest
      · exact Or.inr rfl
      · obtain rfl := List.mem_singleton.mp rest
        exact Or.inr rfl
  have paid : LogUpBalanced ([ch.pushedValue first,ch.pulledValue last] ++ rows.flatMap (pair d)) := closed.logUp_of_isBool boolean
  have withTerminal := ch.logUp_append_terminal first last (HostCommitBoundary.final last.values) _ paid
  intro msg
  have total := withTerminal msg
  simp only [balanceOf_append] at total
  simp only [HostCommitBank.indices, List.flatMap_append, List.flatMap_map, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, bankTable, terminal_ledger, balanceOf_append, bank_sum]
  exact (add_assoc ..).symm.trans total

end SP1Clean.TraceGen.CommitBanks
