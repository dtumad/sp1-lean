import SP1Clean.FormalModel.Contracts.WriteReadback
import ToClean.Circuit.EmittedInteraction
import Clean.Air.FlatComponent
import Clean.Gadgets.Boolean
import SP1Clean.Semantics.Transition.MicroTime
import Clean.Gadgets.Bits
import ToClean.Air.HintIndex

/-! # Supplying true intervals from read-back receipts

One row consumes each mandatory source receipt, even if its query count is zero. Active output
multiplicity may fund repeated probes. The circuit checks 16/8/8/16-bit pieces so the two
24-bit Memory limbs and the three 16-bit version limbs represent the same natural timestamp.
A read-back preserves the word at both ends of the closed interval.
-/

namespace SP1Clean.WriteProbe.ReadbackSupply

open Circuit Air.Flat Semantics

/-- Split the middle of a 48-bit timestamp at both native bus boundaries. -/
structure ClockParts (F : Type) where
  /-- Bits 0 through 15. -/
  low : F
  /-- Bits 16 through 23. -/
  midLow : F
  /-- Bits 24 through 31. -/
  midHigh : F
  /-- Bits 32 through 47. -/
  high : F
deriving ProvableStruct
provable_struct_eval_lemmas ClockParts

/-- Upper Memory bus timestamp limb. -/
def ClockParts.high24 {F} [Add F] [Mul F] [OfNat F 256] (parts : ClockParts F) : F :=
  parts.midHigh + parts.high * 256

/-- Lower Memory bus timestamp limb. -/
def ClockParts.low24 {F} [Add F] [Mul F] [OfNat F 65536] (parts : ClockParts F) : F :=
  parts.low + parts.midLow * 65536

/-- Version bus timestamp in its three 16-bit limbs. -/
def ClockParts.address {F} [Add F] [Mul F] [OfNat F 256] (parts : ClockParts F) : fields 3 F :=
  #v[parts.low, parts.midLow + parts.midHigh * 256, parts.high]

/-- Each of the four chunks fits its place in both timestamp encodings. -/
def ClockParts.Bounded {p} (parts : ClockParts (ZMod p)) :=
  parts.low.val < 2 ^ 16 ∧ parts.midLow.val < 2 ^ 8 ∧
    parts.midHigh.val < 2 ^ 8 ∧ parts.high.val < 2 ^ 16

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
private theorem pack (x y : ZMod p) (k : ℕ) (fits : x.val + y.val * k < p) :
    (x + y * (k : ZMod p)).val = x.val + y.val * k := by
  have cast : ((x.val + y.val * k : ℕ) : ZMod p) = x + y * (k : ZMod p) := by simp
  rw [← cast, ZMod.val_natCast_of_lt fits]

/-- In either representation, the physical timestamp denotes exactly the same natural. -/
theorem ClockParts.time (parts : ClockParts (ZMod p)) (bound : parts.Bounded) :
    Address.toNat parts.address = clkNat parts.high24 parts.low24 := by
  obtain ⟨low, midLow, midHigh, high⟩ := bound
  have field := Fact.out (p := 2 ^ 24 < p)
  have lo := pack parts.low parts.midLow 65536 (by omega)
  have mid := pack parts.midLow parts.midHigh 256 (by omega)
  have hi := pack parts.midHigh parts.high 256 (by omega)
  change (parts.low.val + (parts.midLow + parts.midHigh * 256).val * 65536 + parts.high.val * 4294967296) =
    (parts.midHigh + parts.high * 256).val * 16777216 + (parts.low + parts.midLow * 65536).val
  simp only [Nat.cast_ofNat] at mid hi lo
  rw [mid, hi, lo]
  omega

/-- Input records have no independent clock or version columns. Both messages use these same cells. -/
structure Inputs (F : Type) where
  /-- The complete Memory address copied from the source. -/
  key : fields 3 F
  /-- Split lower endpoint. -/
  previous : ClockParts F
  /-- Split upper endpoint. -/
  current : ClockParts F
  /-- Word copied verbatim from the source receipt. -/
  value : Word F
  /-- One for a genuine receipt and zero for padding. -/
  active : F
  /-- Number of private version queries funded by this row. -/
  count : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Original receipt reconstructed in the Memory bus clock layout. -/
def Inputs.receipt {F} [Add F] [Mul F] [OfNat F 256] [OfNat F 65536] (r : Inputs F) : Readback F :=
  ⟨r.key, r.previous.high24, r.previous.low24, r.current.high24, r.current.low24, r.value⟩

/-- Probe version using the same clock chunks, address and word. -/
def Inputs.version {F} [Add F] [Mul F] [OfNat F 256] (r : Inputs F) : Version F :=
  ⟨r.key, r.previous.address, r.current.address, r.value⟩

/-- Binary activity, disabled counts and canonical clock chunks for one physical row. -/
def Valid (r : Inputs (ZMod p)) : Prop :=
  (r.active = 0 ∨ r.active = 1) ∧ (r.active = 0 → r.count = 0) ∧
    r.previous.Bounded ∧ r.current.Bounded

/-- Range-check the four pieces at the actual boundaries of the two encodings. -/
def checkClock (c : Var ClockParts (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.ToBits.rangeCheck 16 (by have := Fact.out (p := 2 ^ 24 < p); omega)) c.low
  assertion (Gadgets.ToBits.rangeCheck 8 (by have := Fact.out (p := 2 ^ 24 < p); omega)) c.midLow
  assertion (Gadgets.ToBits.rangeCheck 8 (by have := Fact.out (p := 2 ^ 24 < p); omega)) c.midHigh
  assertion (Gadgets.ToBits.rangeCheck 16 (by have := Fact.out (p := 2 ^ 24 < p); omega)) c.high

/-- Consume an active source and publish its converted version with the chosen count. -/
def main (r : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertZero (r.active * (r.active - 1))
  assertZero ((1 - r.active) * r.count)
  checkClock r.previous
  checkClock r.current
  readbackChannel.pullIf r.active r.receipt
  versionChannel.emit r.count r.version

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  unfold main checkClock
  elaborate_circuit_with { channelsWithGuarantees := [readbackChannel.toRaw] }

/-- Local checker for distributing a genuine read-back version at any query count. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.write_readback_supply"
  main
  elaborated
  channelsWithRequirements := [versionChannel.toRaw]
  Spec r _ _ := Valid r
  ProverAssumptions r _ _ := Valid r
  soundness := by
    circuit_proof_start [main, checkClock, Gadgets.ToBits.rangeCheck, Valid, ClockParts.Bounded,
      readbackChannel, versionChannel]
    obtain ⟨binary, count, a, b, c, d, e, f, g, h⟩ := h_holds
    have bit := bool_of_mul_pred binary
    exact ⟨⟨bit, fun zero => by simpa [zero] using count, ⟨a, b, c, d⟩, e, f, g, h⟩, bit⟩
  completeness := by
    circuit_proof_start [main, checkClock, Gadgets.ToBits.rangeCheck, Valid, ClockParts.Bounded,
      readbackChannel, versionChannel]
    obtain ⟨binary, count, ⟨a, b, c, d⟩, e, f, g, h⟩ := h_assumptions
    refine ⟨?_, ?_, a, b, c, d, e, f, g, h⟩
    · rcases binary with off | on <;> simp [*]
    · rcases binary with off | on
      · simp [off, count off]
      · simp [on]
  requirementsChannelsLawful input offset := by
    preserve_tactic_target
    simp only [main, checkClock, circuit_norm, readbackChannel, versionChannel]
    constructor
    · simp [Gadgets.ToBits.rangeCheck, circuit_norm]
    · constructor
      · intro channel member
        rcases member with rfl | rfl
        · exact Or.inl (List.mem_cons_self ..)
        · exact Or.inr rfl
      · intro env checked
        exact bool_of_mul_pred checked.1

/-- A counted supply row has a mandatory original receipt with the same address and unchanged
word, and the closed interval is the actual pair of natural Memory timestamps. -/
theorem Valid.counted {r : Inputs (ZMod p)} (valid : Valid r) (counted : r.count ≠ 0) :
    r.active = 1 ∧ r.version.key = r.receipt.key ∧ r.version.value = r.receipt.value ∧
      Address.toNat r.version.lower = clkNat r.receipt.previousHigh r.receipt.previousLow ∧
      Address.toNat r.version.upper = clkNat r.receipt.currentHigh r.receipt.currentLow :=
  ⟨valid.1.resolve_left (fun off => counted (valid.2.1 off)), rfl, rfl,
    r.previous.time valid.2.2.1, r.current.time valid.2.2.2⟩

/-- Construct the four pieces from the two bounded Memory limbs. -/
def ClockParts.split (hi lo : ZMod p) : ClockParts (ZMod p) :=
  ⟨(lo.val % 65536 : ℕ), (lo.val / 65536 : ℕ), (hi.val % 256 : ℕ), (hi.val / 256 : ℕ)⟩

theorem ClockParts.split_spec (hi lo : ZMod p) (hiBound : hi.val < 2 ^ 24) (loBound : lo.val < 2 ^ 24) :
    (split hi lo).Bounded ∧ (split hi lo).high24 = hi ∧ (split hi lo).low24 = lo := by
  have primeBound := Fact.out (p := 2 ^ 24 < p)
  refine ⟨?_, ?_, ?_⟩
  · unfold split Bounded
    repeat' rw [ZMod.val_natCast_of_lt (by omega)]
    exact ⟨by omega, by omega, by omega, by omega⟩
  · have recombine : hi.val % 256 + hi.val / 256 * 256 = hi.val := by omega
    simpa only [split, high24, low24, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
      using congrArg (fun n : ℕ => (n : ZMod p)) recombine
  · have recombine : lo.val % 65536 + lo.val / 65536 * 65536 = lo.val := by omega
    simpa only [split, high24, low24, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
      using congrArg (fun n : ℕ => (n : ZMod p)) recombine

/-- Query multiplicity is the only freely selected datum of an active source row. -/
def populate (record : Readback (ZMod p)) (count : ZMod p) : Inputs (ZMod p) :=
  ⟨record.key, .split record.previousHigh record.previousLow, .split record.currentHigh record.currentLow,
    record.value, 1, count⟩

/-- Every genuine bounded receipt yields a valid physical source and reconstructs all its fields. -/
theorem populate_valid (record : Readback (ZMod p)) (count : ZMod p)
    (ph : record.previousHigh.val < 2 ^ 24) (pl : record.previousLow.val < 2 ^ 24)
    (ch : record.currentHigh.val < 2 ^ 24) (cl : record.currentLow.val < 2 ^ 24) :
    Valid (populate record count) ∧ (populate record count).receipt = record := by
  obtain ⟨previous, high, low⟩ := ClockParts.split_spec _ _ ph pl
  obtain ⟨current, high', low'⟩ := ClockParts.split_spec _ _ ch cl
  exact ⟨⟨Or.inr rfl, fun impossible => (one_ne_zero impossible).elim, previous, current⟩, by
    cases record
    simp only [populate, Inputs.receipt, high, low, high', low']⟩

private def splitFE (hi lo : Expression (ZMod p)) : ClockParts (Witgen.FExpr (ZMod p)) :=
  ⟨(lo.val % 65536).toField, (lo.val / 65536).toField, (hi.val % 256).toField, (hi.val / 256).toField⟩

/-- Every genuine receipt is consumed exactly once by the normal scheduler. The private
count index uses the full original receipt as a tuple, including its value and both clocks. -/
def generation : WitnessGeneration.Generation (ZMod p) Inputs :=
  .demand {
    channel := readbackChannel
    trigger := .push
    input msg := do
      let keys := (toElements (M := Readback) msg).toList.map (·.val)
      let count := Witgen.HintIndex.inputKeys (Input := field) "sp1.native.write_readback_counts" keys
      let input : Inputs (Witgen.FExpr (ZMod p)) :=
        ⟨msg.key.map Witgen.FExpr.expr, splitFE msg.previousHigh msg.previousLow, splitFE msg.currentHigh msg.currentLow,
          msg.value.map Witgen.FExpr.expr, 1, count⟩
      pure (fromElements ((toElements input).map WitnessGeneration.Cell.witness))
  }

/-- The source component has its own scheduler and local physical checks. -/
def component : Component (ZMod p) :=
  { circuit, generation, Assumptions := circuit.Assumptions }

end SP1Clean.WriteProbe.ReadbackSupply
