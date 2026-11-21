import SP1Clean.Soundness.LocalCoreEventUniqueness
import SP1Clean.Soundness.CoreExecutionEvents
import SP1Clean.Semantics.Execution.SailBookkeeping

/-! # Reading ordinary receipts in the order of the grounded CPU tape

Filtering the actual CPU State walk keeps exactly the ordinary instruction successors, before
StateBump canonicalization. Their timestamps fix the same order as the observation history.
The last such successor is the semantic nextPC, including when host calls follow it.
-/

namespace SP1Clean.Soundness.OrdinaryObservation

open Circuit Air.Flat Channels NativeCore Semantics Machine

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Each ordinary CPU row carries its raw receipt, and host rows carry none. -/
noncomputable def cpuReceipt (data : ProverData (ZMod p)) : ExecutionRow p → Option (StateMsg (ZMod p))
  | .instruction row => some (statePushMessage (row.toChipRow data))
  | .halt _ | .syscall _ => none

/-- Undo the uncarried eight-tick successor increment to rank the original ordinary source. -/
def receiptRank (message : StateMsg (ZMod p)) : ℕ :=
  clkNat message.clk_high (message.clk_low - 8)

/-- Exactly the physical ordinary CPU source clock ranks each published receipt. -/
private theorem cpuReceipt_time (data : ProverData (ZMod p)) (row : ExecutionRow p)
    (message : StateMsg (ZMod p)) (present : cpuReceipt data row = some message) :
    receiptRank message = StateMsg.timeNat (row.edge data).1 := by
  cases row with
  | instruction instruction =>
    cases present
    simp only [receiptRank, ExecutionRow.edge, decodedStateEdge, statePushMessage, statePushOfView,
      statePullMessage, statePullOfView, stateAccess, add_sub_cancel_right]
    rfl
  | halt _ | syscall _ => cases present

/-- Ordinary count on the machine tape counts active CPU receipts exactly. -/
theorem cpuReceipt_count (data : ProverData (ZMod p)) (cpu : List (ExecutionRow p)) :
    (cpu.filterMap (cpuReceipt data)).length = (cpu.map ExecutionRow.event).countP ExecutionEvent.isOrdinary := by
  induction cpu with
  | nil => rfl
  | cons row rest ih =>
    cases row <;> simp only [List.filterMap_cons, cpuReceipt, List.map_cons, ExecutionRow.event,
      List.countP_cons,
      ExecutionEvent.isOrdinary, List.length_cons, ih] <;> rfl

/-- The physical active receipt multiset and strict ranks recover the exact chronological list.
Repeated raw PC values remain possible at different instruction clocks. -/
theorem ordered_receipts (data : ProverData (ZMod p)) (cpu : List (ExecutionRow p)) (receipts : List (StateMsg (ZMod p)))
    (same : (cpu.filterMap (cpuReceipt data)).Perm receipts)
    (cpuSorted : (cpu.map fun row => StateMsg.timeNat (row.edge data).1).Pairwise (· < ·))
    (sorted : (receipts.map receiptRank).Pairwise (· < ·)) : cpu.filterMap (cpuReceipt data) = receipts := by
  apply same.eq_of_pairwise (le := fun a b => receiptRank a < receiptRank b)
  · intro a b _ _ forward backward
    exact (Nat.lt_asymm forward backward).elim
  · apply (List.pairwise_map.mp cpuSorted).filterMap
    intro a b ordered x hx y hy
    rw [cpuReceipt_time data a x hx, cpuReceipt_time data b y hy]
    exact ordered
  · exact List.pairwise_map.mp sorted

/-- The actual nextPC fold selects the last ordinary CPU successor, with exact preservation of the
supplied initial register when the tape is all host calls or empty. -/
theorem cpuReceipt_nextPC (data : ProverData (ZMod p)) (cpu : List (ExecutionRow p))
    (initial : Option (BitVec 64)) (first last : StateMsg (ZMod p))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge data) first last cpu)
    (good : ∀ row ∈ cpu, StateChronology.Good (row.edge data).1 ∧ StateChronology.Good (row.edge data).2) :
    nextPcAfter (cpu.map ExecutionRow.event) initial (some (StateMsg.pcBits last)) =
      (cpu.filterMap (cpuReceipt data)).foldl (fun _ message => some (StateMsg.pcBits message)) initial := by
  induction cpu using List.reverseRecOn generalizing last with
  | nil => rfl
  | append_singleton before row ih =>
    obtain ⟨middle, partialWalk, left, right⟩ := (Walk.isWalk_append _ before [row] first last).mp walk
    change (row.canonEdge data).1 = middle at left
    change (row.canonEdge data).2 = last at right
    have bounds := good row (by simp)
    have tail := ih middle partialWalk (fun event member => good _ (List.mem_append_left _ member))
    have sourcePC : StateMsg.pcBits middle = StateMsg.pcBits (row.edge data).1 := by
      rw [← left]
      exact pcBits_canonState bounds.1.2.1 bounds.1.2.2
    have targetPC : StateMsg.pcBits last = StateMsg.pcBits (row.edge data).2 := by
      rw [← right]
      exact pcBits_canonState bounds.2.2.1 bounds.2.2.2
    simp only [List.map_append, List.map_cons, List.map_nil, List.filterMap_append, List.foldl_append]
    cases row with
    | instruction instruction =>
      rw [show (ExecutionRow.instruction instruction).event = .ordinary from rfl, nextPcAfter_ordinary]
      exact congrArg some targetPC
    | halt row =>
      rw [show (ExecutionRow.halt row).event = .syscall (haltEventOfRow row) from rfl, nextPcAfter_syscall]
      exact (congrArg (nextPcAfter (before.map ExecutionRow.event) initial) (congrArg some sourcePC).symm).trans tail
    | syscall row =>
      rw [show (ExecutionRow.syscall row).event = .syscall (syscallEventOfRow row) from rfl, nextPcAfter_syscall]
      exact (congrArg (nextPcAfter (before.map ExecutionRow.event) initial) (congrArg some sourcePC).symm).trans tail

/-- In the local State inventory the ordinary receipts are exactly the active decoded instruction
rows. Both HALT and syscall wrapper rows are excluded by their native event type. -/
theorem inventory_receipts {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (LocalCore.ensemble (p := p) image source)) :
    (LocalCore.executionRows witness).filterMap (cpuReceipt witness.data) =
      (LocalCore.activeInstructionRows witness).map (fun row => statePushMessage (row.toChipRow witness.data)) := by
  simp only [LocalCore.executionRows, List.filterMap_append, List.filterMap_map, Function.comp_def,
    cpuReceipt, List.filterMap_none, List.append_nil, List.filterMap_eq_map']

/-- For the physical active receipt multiset, strict observation order fixes the exact ordinary
count and nextPC of the same grounded CPU tape. The image, header and State walk are the ones
already used by the local execution proof. -/
theorem cpu_agreement {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (LocalCore.ensemble (p := p) image source))
    (constraints : witness.Constraints) (channels : LocalCore.OrderingChannels witness)
    {cpu : List (ExecutionRow p)} (exhaustive : cpu.Perm (LocalCore.executionRows witness))
    (walk : Walk.IsWalk (ExecutionRow.canonEdge witness.data) (initialBoundaryStateMessage witness.publicInput)
      (finalBoundaryStateMessage witness.publicInput) cpu)
    (receipts : List (StateMsg (ZMod p)))
    (matched : ((LocalCore.activeInstructionRows witness).map
      (fun row => statePushMessage (row.toChipRow witness.data))).Perm receipts)
    (sorted : (receipts.map receiptRank).Pairwise (· < ·))
    (initialPC : Option (BitVec 64)) :
    (cpu.map ExecutionRow.event).countP ExecutionEvent.isOrdinary = receipts.length ∧
      nextPcAfter (cpu.map ExecutionRow.event) initialPC (some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput))) =
        receipts.foldl (fun _ message => some (StateMsg.pcBits message)) initialPC := by
  have permutations := exhaustive.filterMap (cpuReceipt witness.data)
  rw [inventory_receipts] at permutations
  have same := ordered_receipts witness.data cpu receipts (permutations.trans matched)
    (LocalCore.ordered_times_pairwise witness constraints channels exhaustive walk) sorted
  rw [← same]
  exact ⟨(cpuReceipt_count witness.data cpu).symm, cpuReceipt_nextPC witness.data cpu initialPC _ _ walk
    (fun row member => LocalCore.executionRows_good_of_orderingChannels witness constraints channels
      (exhaustive.mem_iff.mp member))⟩

end SP1Clean.Soundness.OrdinaryObservation
