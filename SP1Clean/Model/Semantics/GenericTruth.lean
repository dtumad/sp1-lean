import SP1Clean.Model.Semantics.Truth

/-! # Shard-local truth over a trajectory

A State message is true when the trajectory reaches a state with that pc at the message's clock;
a Memory record is true when the state at the record's micro-time holds that value. The trajectory
is a parameter: the grounding walk instantiates it with the carrier's replay of `ExecutionStep`,
whose steps are official-Sail retirements or host syscalls with their own clock windows.

Two conventions are load-bearing:

* A `Trajectory` is `Option`-valued and may be undefined past the shard's own length. Every
  predicate is written so that "undefined" fails to witness truth rather than needing a side
  condition.
* The initial state is a separate parameter from the trajectory. Reads before the timeline's
  genesis go to that state directly and do not consult the trajectory. -/

namespace SP1Clean.Semantics

open Sail LeanRV64D LeanRV64D.Functions
open LeanRV64D
open SP1Clean.Soundness.Target
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The machine state after `n` semantic steps, where the shard defines one. -/
abbrev Trajectory := ℕ → Option SailState

/-! ## The predicates -/

/-- The timeline reader over an arbitrary trajectory. Below the timeline's genesis the initial state
answers directly; at or after it, step `k`'s window is read pre- or post-effect at the location's own
effect offset. -/
noncomputable def microValue (traj : Trajectory) (s0 : SailState) (tl : Timeline)
    (loc : MemLoc) (τ : ℕ) : Option (BitVec 64) :=
  if τ < tl.start 0 then
    locContent s0 loc
  else
    let k := tl.stepOf τ
    let δ := τ - tl.start k
    let takePost : Bool := match loc with
      | .reg _ => regEffectOffset ≤ δ
      | .ram _ => ramEffectOffset ≤ δ
    (traj (if takePost then k + 1 else k)).bind (locContent · loc)

/-- `value` is the content of `location` at `time` on this trajectory. -/
def LocalValueAt (traj : Trajectory) (s0 : SailState) (tl : Timeline) (location : MemLoc)
    (time : ℕ) (value : Word (ZMod p)) : Prop :=
  microValue traj s0 tl location time = some (Word.toBitVec64 value)

/-- A State message is true when the trajectory reaches a state with that pc at that clock. -/
def LocalStateTruth (program : GuestProgram) (traj : Trajectory) (tl : Timeline)
    (m : StateMsg (ZMod p)) : Prop :=
  ∃ (n : ℕ) (state : SailState),
    traj n = some state ∧
    StateMsg.timeNat m = tl.start n ∧
    state.regs.get? Register.PC = some (pcBits m.pc0 m.pc1 m.pc2) ∧
    RomLoaded program state ∧
    SailConfigured state

/-- Memory grounding: row-local hygiene in the channel's own `Guarantees` order, then the semantic
conjunct. The field order matches `LocalMemTruth`'s so the common `.1` projection is unchanged. -/
def LocalMemTruth (traj : Trajectory) (s0 : SailState) (tl : Timeline)
    (message : MemoryMsg (ZMod p)) : Prop :=
  SP1Clean.Channels.MemoryMsg.isU64 message ∧
  SP1Clean.Channels.MemoryMsg.ClkBound message ∧
  LocalValueAt traj s0 tl (MemoryMsg.locOf message) (MemoryMsg.timeNat message) message.value

/-- The shard-local advance obligation: pulled truth and operand currency give pushed truth. -/
def LocalStepFact (program : GuestProgram) (traj : Trajectory) (s0 : SailState) (tl : Timeline)
    (r : RowFacts p) : Prop :=
  LocalStateTruth program traj tl r.statePull →
  (∀ mp ∈ r.memPulls,
    SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
    SP1Clean.Channels.MemoryMsg.ClkBound mp.1 ∧
    LocalValueAt traj s0 tl (MemoryMsg.locOf mp.1) mp.2 mp.1.value) →
  LocalStateTruth program traj tl r.statePush ∧
    ∀ message ∈ r.memPushes, LocalMemTruth traj s0 tl message

/-- Untouched locations keep their value across the row's window. -/
def FrameFact (program : GuestProgram) (traj : Trajectory) (s0 : SailState) (tl : Timeline)
    (r : RowFacts p) : Prop :=
  LocalStateTruth program traj tl r.statePull →
  (∀ mp ∈ r.memPulls, SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
      SP1Clean.Channels.MemoryMsg.ClkBound mp.1 ∧
      LocalValueAt traj s0 tl (MemoryMsg.locOf mp.1) mp.2 mp.1.value) →
  ∀ (loc : MemLoc) (v : Word (ZMod p)),
    (∀ m ∈ r.memPushes, MemoryMsg.locOf m = loc → m.value = v) →
    LocalValueAt traj s0 tl loc (StateMsg.timeNat r.statePull) v →
    LocalValueAt traj s0 tl loc (StateMsg.timeNat r.statePush) v

/-- The genesis per-key frontier is true and current at the head time. -/
def LiveOK (traj : Trajectory) (s0 : SailState) (tl : Timeline) (t : ℕ)
    (live : MemLoc → Option (MemoryMsg (ZMod p))) : Prop :=
  ∀ (loc : MemLoc) (m : MemoryMsg (ZMod p)), live loc = some m →
    MemoryMsg.locOf m = loc ∧
    LocalMemTruth traj s0 tl m ∧
    LocalValueAt traj s0 tl loc t m.value ∧
    MemoryMsg.timeNat m ≤ t

/-- What the walk hands back per row. -/
def Grounded (program : GuestProgram) (traj : Trajectory) (s0 : SailState) (tl : Timeline)
    (r : RowFacts p) : Prop :=
  LocalStateTruth program traj tl r.statePull ∧
  ∀ mp ∈ r.memPulls, LocalMemTruth traj s0 tl mp.1 ∧
    LocalValueAt traj s0 tl (MemoryMsg.locOf mp.1) mp.2 mp.1.value

end SP1Clean.Semantics
