import SP1Clean.Soundness.CoreRowTransport
import SP1Clean.Math.WordEquality
import SP1Clean.Semantics.Memory.MemorySnapshot

/-! # Read-only observations at a cut in the physical Memory history

The incoming public snapshot seeds each location. A physical push in the row's effect slot
replaces the held word; all earlier accesses are read-backs. Sampling the held word takes no
Memory interaction. The same location can be sampled repeatedly at the same or different cuts.
-/

namespace SP1Clean.Soundness.WriteObservationHistory

open Semantics Target TimedGrounding
open Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime]

private def atEffect (row : RowFacts p) (loc : MemLoc) (msg : MemoryMsg (ZMod p)) : Bool :=
  decide (MemoryMsg.locOf msg = loc ∧
    MemoryMsg.timeNat msg = StateMsg.timeNat row.statePull + writeOffset loc)

/-- Carry a single physical word across this row, using the row's existing full Memory footprint. -/
def carry (loc : MemLoc) (prior : Word (ZMod p)) (row : RowFacts p) : Word (ZMod p) :=
  ((row.memPushes.find? (atEffect row loc)).map (·.value)).getD prior

/-- Observe the prefix ending strictly before `cut`, seeded by the complete incoming snapshot. -/
def wordAt (snapshot : MemorySnapshot) (rows : List (RowFacts p)) (cut : ℕ) (loc : MemLoc) : Word (ZMod p) :=
  (rows.take cut).foldl (carry loc) (bitVecToWord (snapshot.read loc))

private theorem carry_truth {program : GuestProgram} {traj : Trajectory} {initial : SailState} {tl : Timeline}
    {row physical : RowFacts p} {clock n : ℕ} {loc : MemLoc} {prior : Word (ZMod p)}
    (time : StateMsg.timeNat physical.statePull = StateMsg.timeNat row.statePull)
    (pushes : physical.memPushes.Perm row.memPushes)
    (ok : RowOKCore clock row) (grounded : Grounded program traj initial tl row)
    (step : LocalStepFact program traj initial tl row) (frame : FrameFact program traj initial tl row)
    (start : StateMsg.timeNat row.statePull = tl.start n)
    (finish : StateMsg.timeNat row.statePush = tl.start (n + 1))
    (bounded : prior.isU64) (current : LocalValueAt traj initial tl loc (tl.start n) prior) :
    (carry loc prior physical).isU64 ∧ LocalValueAt traj initial tl loc (tl.start (n + 1)) (carry loc prior physical) := by
  have inputs := fun mp (member : mp ∈ row.memPulls) =>
    And.intro (grounded.2 mp member).1.1 (And.intro (grounded.2 mp member).1.2.1 (grounded.2 mp member).2)
  cases found : physical.memPushes.find? (atEffect physical loc) with
  | none =>
    simp only [carry, found, Option.map_none, Option.getD_none]
    refine ⟨bounded, ?_⟩
    rw [← finish]
    apply frame grounded.1 inputs loc prior _ (start ▸ current)
    intro m member same
    obtain ⟨pull, occurs, touch⟩ := forall₂_exists_left ok.touches m member
    have readLoc := touch.loc_eq.symm.trans same
    rcases touch.push_kind with ⟨value, _⟩ | effect
    · rw [value]
      have now := (grounded.2 pull occurs).2
      have lo := touch.read_lo
      have hi := touch.read_hi
      rw [readLoc] at now hi
      rw [start] at lo hi
      have priorRead := localValueAt_shift_window loc lo hi le_rfl (Nat.le_add_right _ _) now
      exact Word.eq_of_toBitVec64_eq (grounded.2 pull occurs).1.1 bounded
        (Option.some.inj (priorRead.symm.trans current))
    · exact False.elim (List.find?_eq_none.mp found m (pushes.mem_iff.mpr member) (by simp [atEffect, same, effect, time]))
  | some m =>
    simp only [carry, found, Option.map_some, Option.getD_some]
    obtain ⟨same, effect⟩ : MemoryMsg.locOf m = loc ∧
        MemoryMsg.timeNat m = StateMsg.timeNat row.statePull + writeOffset loc := by
      simpa only [atEffect, decide_eq_true_eq, time] using List.find?_some found
    have valid := (step grounded.1 inputs).2 m (pushes.mem_iff.mp (List.mem_of_find?_eq_some found))
    refine ⟨valid.1, ?_⟩
    have posted := valid.2.2
    have gap := ok.timeGap
    rw [start, finish] at gap
    rw [start] at effect
    rw [same] at posted
    cases loc with
    | reg i =>
      rw [writeOffset_reg] at effect
      exact localValueAt_shift_reg (n := n) (Or.inr ⟨by omega, by omega, by omega, by omega⟩) posted
    | ram a =>
      rw [writeOffset_ram] at effect
      exact localValueAt_shift_ram (n := n) (Or.inr ⟨by omega, by omega, by omega, by omega⟩) posted

variable [Fact (2 ^ 17 < p)]

/-- For every processed prefix, physical effect-slot pushes and the authenticated snapshot determine
the unique four-limb word held at its outgoing cut. Only rows strictly before the cut need grounding. -/
theorem wordAt_prefix {snapshot : MemorySnapshot} {rows : List (RowFacts p)}
    {program : GuestProgram} {traj : Trajectory} {initial : SailState} {tl : Timeline}
    {cut clock : ℕ} {loc : MemLoc} (zero : traj 0 = some initial)
    (seed : locContent initial loc = some (snapshot.read loc)) (within : cut ≤ rows.length)
    (beforeCut : ∀ n, (idx : n < cut) →
      let physical := rows[n]'(by omega)
      ∃ row : RowFacts p, StateMsg.timeNat physical.statePull = StateMsg.timeNat row.statePull ∧
        physical.memPushes.Perm row.memPushes ∧ StateMsg.timeNat row.statePull = tl.start n ∧
        StateMsg.timeNat row.statePush = tl.start (n+1) ∧ RowOKCore clock row ∧
        Grounded program traj initial tl row ∧ LocalStepFact program traj initial tl row ∧
        FrameFact program traj initial tl row) :
    (wordAt snapshot rows cut loc).isU64 ∧
      LocalValueAt traj initial tl loc (tl.start cut) (wordAt snapshot rows cut loc) := by
  induction cut with
  | zero =>
    refine ⟨isU64_bitVecToWord _, (localValueAt_stepStart_iff zero).mpr ?_⟩
    simpa only [wordAt, List.take_zero, List.foldl_nil, toBitVec64_bitVecToWord] using seed
  | succ n ih =>
    have inside : n < rows.length := by omega
    obtain ⟨bounded, current⟩ := ih (by omega) (fun j hj => beforeCut j (by omega))
    obtain ⟨row, time, pushes, start, finish, ok, rowGrounded, step, frame⟩ := beforeCut n (by omega)
    simpa only [wordAt, List.take_succ_eq_append_getElem inside, List.foldl_append,
      List.foldl_cons, List.foldl_nil] using carry_truth time pushes ok rowGrounded step frame start finish bounded current

section Carrier

open NativeCore

variable [Fact (2 ^ 25 < p)]
variable {facts : ExecutionRow p → RowFacts p} {events : List (ExecutionRow p)}
  {incoming outgoing : StateMsg (ZMod p)} {first last : MemLoc → Option (MemoryMsg (ZMod p))}

/-- Apply prefix readback directly to the physical rows in State-channel order. The carrier
may re-order a row's pushes for grounding, including equal-key accesses; the code reads the
original event's Memory messages. -/
theorem wordAt_carrier (carrier : ExecutionCarrier facts events incoming outgoing first last)
    {snapshot : MemorySnapshot} {program : GuestProgram} {traj : Trajectory} {initial : SailState}
    (zero : traj 0 = some initial) (realizes : snapshot.Realizes initial)
    (initialState : LocalStateTruth program traj carrier.timeline incoming)
    (initialMemory : LiveOK traj initial carrier.timeline (StateMsg.timeNat incoming) first)
    (steps : ∀ event ∈ events, LocalStepFact program traj initial carrier.timeline (facts event) ∧
      FrameFact program traj initial carrier.timeline (facts event))
    {cut : ℕ} (within : cut ≤ carrier.ordered.length) (loc : MemLoc) (bound : loc.busAddress < 2 ^ 48) :
    let word := wordAt snapshot (carrier.ordered.map facts) cut loc
    word.isU64 ∧ LocalValueAt traj initial carrier.timeline loc (carrier.timeline.start cut) word := by
  have grounded := (carrier.ground program traj initial initialState initialMemory steps).1
  have semantic := carrier.engineFacts program traj initial carrier.timeline steps
  apply wordAt_prefix (clock := StateMsg.timeNat incoming) zero (realizes.locContent_of_address_lt loc bound)
    (by simpa only [List.length_map] using within)
  intro n hn
  have physicalBound : n < (carrier.ordered.map facts).length := by simp only [List.length_map]; omega
  have rowBound : n < carrier.rows.length := carrier.aligned.length_eq ▸ physicalBound
  let row := carrier.rows[n]
  have aligned := carrier.aligned.get rowBound physicalBound
  have member : row ∈ carrier.rows := List.getElem_mem rowBound
  have start := rowTimeline_pullTime_of_getElem? carrier.stateWalk
    (fun r h => (carrier.rowOK r h).timeGap) (List.getElem?_eq_getElem rowBound)
  exact ⟨row, aligned.pullTime.symm, aligned.pushes.symm, start, carrier.timeStep row member n start,
    carrier.rowOK row member, grounded row member, semantic row member⟩

end Carrier

end SP1Clean.Soundness.WriteObservationHistory
