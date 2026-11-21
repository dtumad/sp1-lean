import SP1Clean.FormalModel.Contracts.OrdinaryObservation
import SP1Clean.Semantics.Execution.SailBookkeeping
import SP1Clean.Semantics.Execution.ExecutionSnapshot
import SP1Clean.Semantics.Sail.SailPlatform
import SP1Clean.Semantics.ISA.Decode

/-! # Fixed endpoints of the ordinary observation chain

The chain starts at clock zero, below every ordinary source clock, with the incoming retirement
counter, nextPC and retirement flag. A terminal row moves the last observation to its mode's
sentinel clock, at or above `2^48` and outside every ordinary source clock, so a fixed verifier can
bind the outgoing counter and nextPC without exposing the last ordinary clock.

The terminal's mode records what the supplied target says about whether the segment retired an
ordinary instruction. That matters only when the target's retirement flag, interrupt refresh and
written event index differ between the two cases. The mode is static data of the target; the
terminal checks it against its own last observation.
-/

namespace SP1Clean.OrdinaryObservation

open Circuit Semantics Soundness.Target
open LeanRV64D (Register)

variable {p : ℕ} [Fact p.Prime]

/-- What the supplied target fixes about whether the segment observed an ordinary retirement. -/
inductive Mode
  /-- No ordinary instruction retired: the last observation is the start. -/
  | empty
  /-- At least one ordinary instruction retired: the last observation is a receipt. -/
  | nonempty
  /-- The target's bookkeeping is the same either way. -/
  | any
deriving DecidableEq

/-- Each mode's sentinel high clock limb: all three are at or above `2^24`, so every sentinel clock is
outside every ordinary source clock, and distinct, so the verifier selects one mode's link. -/
def Mode.sentinel {R : Type} [OfNat R 16777216] [OfNat R 16777217] [OfNat R 16777218] : Mode → R
  | .empty => 16777216
  | .nonempty => 16777217
  | .any => 16777218

/-- Seed the chain with the incoming counter, nextPC limbs and retirement flag, below every
ordinary clock. -/
def start (counter : Word (ZMod p)) (pc : Vector (ZMod p) 3) (enabled : ZMod p) : State (ZMod p) :=
  ⟨0, 0, counter, pc, enabled⟩

/-- The terminal's outgoing link for a mode, at its sentinel clock. -/
def final {R : Type} [OfNat R 16777216] [OfNat R 16777217] [OfNat R 16777218] [Zero R]
    (mode : Mode) (counter : Word R) (pc : Vector R 3) (enabled : R) : State R :=
  ⟨mode.sentinel, 0, counter, pc, enabled⟩

/-- The terminal's last observation has a bounded clock, consistent with the mode: the start's
clock is zero, and every observed receipt's is not. -/
def TerminalSpec (mode : Mode) (input : State (ZMod p)) : Prop :=
  input.clkHigh.val < 2 ^ 24 ∧ input.clkLow.val < 2 ^ 24 ∧
    match mode with
    | .empty => input.clkHigh = 0 ∧ input.clkLow = 0
    | .nonempty => ¬ (input.clkHigh = 0 ∧ input.clkLow = 0)
    | .any => True

/-- The last raw observation and the two base-65536 carries used to bind its numerical PC. -/
structure TerminalInputs (F : Type) where
  previous : State F
  carryLow : F
  carryMiddle : F
deriving ProvableStruct
provable_struct_eval_lemmas TerminalInputs

/-- Move each carry to its next limb. The verifier fixes the resulting limbs canonically. -/
def TerminalInputs.pc {R : Type} [Add R] [Sub R] [Mul R] [OfNat R 65536]
    (input : TerminalInputs R) : Vector R 3 :=
  #v[input.previous.pc[0] - input.carryLow * 65536,
     input.previous.pc[1] + input.carryLow - input.carryMiddle * 65536,
     input.previous.pc[2] + input.carryMiddle]

/-- A terminal advances from the selected clock mode with two single-bit carries. -/
def TerminalInputs.Valid (mode : Mode) (input : TerminalInputs (ZMod p)) : Prop :=
  IsBool input.carryLow ∧ IsBool input.carryMiddle ∧ TerminalSpec mode input.previous

/-- Compute the two carries from the last raw observation, including a low- and middle-limb rollover. -/
def terminalInput (previous : State (ZMod p)) : TerminalInputs (ZMod p) :=
  let low := previous.pc[0].val / 65536
  ⟨previous, low, ((previous.pc[1].val + low) / 65536 : ℕ)⟩

/-- The three State-bus PC limbs of a 64-bit PC. -/
def pcLimbs (pc : BitVec 64) : Vector (ZMod p) 3 :=
  #v[(bitVecToWord pc)[0], (bitVecToWord pc)[1], (bitVecToWord pc)[2]]

/-- The source's retirement flag, as the chain carries it. -/
def flagFor (source : SailSnapshot) : ZMod p :=
  if retirementEnabled source.skeleton then 1 else 0

/-- The supplied source's retirement counter, nextPC and retirement flag seed the chain. -/
def startFor (source : SailSnapshot) : State (ZMod p) :=
  start (bitVecToWord ((source.registers.get? Register.minstret : Option (BitVec 64)).getD 0))
    (pcLimbs ((source.registers.get? Register.nextPC : Option (BitVec 64)).getD 0)) (flagFor source)

/-- With no ordinary retirement the entire nextPC, including its high bits and presence, and
the retirement bookkeeping stay at their incoming values. -/
def quiet (source target : SailSnapshot) : Bool :=
  (target.registers.get? Register.minstret_increment : Option Bool) ==
      source.registers.get? Register.minstret_increment &&
    (target.registers.get? Register.mip : Option (BitVec 64)) == source.registers.get? Register.mip &&
    (target.registers.get? Register.written_event_index : Option (Option (ℕ × LeanRV64D.event_csr))) ==
      source.registers.get? Register.written_event_index &&
    (target.registers.get? Register.nextPC : Option (BitVec 64)) == source.registers.get? Register.nextPC

/-- An ordinary successor supplies a present 48-bit nextPC, the updated retirement flag,
refreshed interrupts and a cleared event index. -/
def refreshed (source target : SailSnapshot) : Bool :=
  (target.registers.get? Register.minstret_increment : Option Bool) ==
      some (retirementEnabled source.skeleton) &&
    (target.registers.get? Register.mip : Option (BitVec 64)) ==
      some (TryStepReduction.refreshedMip source.skeleton) &&
    (target.registers.get? Register.written_event_index : Option (Option (ℕ × LeanRV64D.event_csr))) ==
      some none &&
    (target.registers.get? Register.nextPC : Option (BitVec 64)).any (fun pc => decide (pc.toNat < 2 ^ 48))

/-- `quiet` compares all four register entries, including absent keys. -/
theorem quiet_iff (source target : SailSnapshot) : quiet source target = true ↔
    (target.registers.get? Register.minstret_increment : Option Bool) =
        source.registers.get? Register.minstret_increment ∧
      (target.registers.get? Register.mip : Option (BitVec 64)) = source.registers.get? Register.mip ∧
      (target.registers.get? Register.written_event_index : Option (Option (ℕ × LeanRV64D.event_csr))) =
        source.registers.get? Register.written_event_index ∧
      (target.registers.get? Register.nextPC : Option (BitVec 64)) = source.registers.get? Register.nextPC := by
  simp only [quiet, Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- `refreshed` checks the high bits and presence before the three PC limbs enter the chain. -/
theorem refreshed_iff (source target : SailSnapshot) : refreshed source target = true ↔
    (target.registers.get? Register.minstret_increment : Option Bool) =
        some (retirementEnabled source.skeleton) ∧
      (target.registers.get? Register.mip : Option (BitVec 64)) =
        some (TryStepReduction.refreshedMip source.skeleton) ∧
      (target.registers.get? Register.written_event_index : Option (Option (ℕ × LeanRV64D.event_csr))) =
        some none ∧
      ∃ pc : BitVec 64, target.registers.get? Register.nextPC = some pc ∧ pc.toNat < 2 ^ 48 := by
  cases pc : target.registers.get? Register.nextPC <;> simp [refreshed, pc, and_assoc]

/-- The mode the supplied target fixes. A target consistent with neither case is rejected by the
static target check. -/
def Mode.of (source target : SailSnapshot) : Mode :=
  match quiet source target, refreshed source target with
  | true, true => .any
  | true, false => .empty
  | false, _ => .nonempty

/-- The supplied target's retirement counter and nextPC close the chain at the sentinel of the mode
the target fixes, with the source's flag unchanged. -/
def finalFor (source target : SailSnapshot) : State (ZMod p) :=
  final (Mode.of source target)
    (bitVecToWord ((target.registers.get? Register.minstret : Option (BitVec 64)).getD 0))
    (pcLimbs ((target.registers.get? Register.nextPC : Option (BitVec 64)).getD 0)) (flagFor source)

end SP1Clean.OrdinaryObservation
