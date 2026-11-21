import SP1CleanTest.Core.HostChecks
import Clean.Circuit.WitnessExport
import SP1Clean.Proofs.Operations.OrdinaryObservation

/-! # Executed ordinary retirement observations

These fixtures evaluate the actual composed program, including its Byte obligations. Explicit
observation endpoints test the subsystem ledger, without claiming their mixed-ensemble binding.
-/

namespace SP1CleanTest.Core.OrdinaryObservation

open Circuit Air.Flat SP1Clean SP1Clean.OrdinaryObservation HostChecks

private abbrev Fp := ZMod SP1Prime

private def word (value : ℕ) : Word Fp :=
  Soundness.Target.bitVecToWord (BitVec.ofNat 64 value)

private def initial (enabled : Bool) (value : ℕ) : State Fp :=
  ⟨0, 0, word value, #v[13, 7, 0], if enabled then 1 else 0⟩

private def receipt (high low : Fp) : Channels.StateMsg Fp := ⟨high, low, 65536, 1, 0⟩

private def evaluate (input : Inputs Fp) (corrupt : Option ℕ := none) :=
  evaluateProgram (main (varFromOffset Inputs 0)) (toElements input).toList corrupt

private def first (enabled : Bool) (counter : ℕ) : Inputs Fp :=
  populate (initial enabled counter) (receipt 0 17)

/-- Enabled/inhibited retirement, each carry boundary and full u64 wrap use the real program. -/
theorem counters : [false, true].all (fun enabled =>
    [0, 65535, 2 ^ 32 - 1, 2 ^ 48 - 1, 2 ^ 64 - 1].all fun counter =>
      (evaluate (first enabled counter)).1 &&
        Word.toBitVec64 (first enabled counter).counter ==
          BitVec.ofNat 64 (counter + if enabled then 1 else 0)) = true := by native_decide

/-- Clock ordering uses the recovered source, so successor overflow and refresh remain legal.
The raw PC limb 65536 is intentionally retained rather than spuriously range-checked. -/
theorem clockCrossings :
    (evaluate (populate (initial true 0) (receipt 0 (2 ^ 24 + 1)))).1 = true ∧
    (evaluate (populate
      ⟨0, 2 ^ 24 - 7, word 1, #v[65536, 1, 0], 1⟩ (receipt 1 9))).1 = true := by native_decide

/-- Equal/reversed/wrapped source clocks, forged counters, a non-Boolean flag and corrupt gadget
witnesses fail. -/
theorem rejectsMalformed :
    [populate (initial true 0) (receipt 0 8),
     populate { initial true 0 with clkLow := 10 } (receipt 0 17),
     populate (initial true 0) (receipt 0 0),
     populate (initial true 0) (receipt (2 ^ 24) 9),
     populate (initial true 0) (receipt 0 (2 ^ 24 + 8)),
     populate { initial true 0 with enabled := 2 } (receipt 0 17),
     { first true 0 with counter := word 2 },
     { first true 0 with counter := #v[65536, 0, 0, 0] }].all
      (fun input => !(evaluate input).1) = true ∧
    (evaluate { first false 7 with counter := word 8 }).1 = false ∧
    [0, 24, 48, 72, 97, 98, 121, 122, 185].all (fun index =>
      !(evaluate (first true 0) (some index)).1) = true := by native_decide

private def balance (ledger : Ledger) : Bool :=
  ledger.all fun key =>
    ((ledger.filter (fun item => item.1 == key.1 && item.2.1 == key.2.1)).map (·.2.2)).sum == 0

private def accepts (start finish : State Fp) (inputs : List (Inputs Fp)) : Bool :=
  let evaluated := inputs.map (evaluate ·)
  let ledger := (evaluated.flatMap (·.2)).filter (fun item => item.1 == "SP1OrdinaryObservation")
  evaluated.all (·.1) && balance (ledger ++
    [("SP1OrdinaryObservation", (toElements start).toList, 1),
     ("SP1OrdinaryObservation", (toElements finish).toList, -1)])

/-- Physical table order is irrelevant; balance authenticates the chronological counter, PC and
the chain's flag. Empty inventories preserve the complete initial observation. -/
theorem histories : [false, true].all (fun enabled =>
    let a := first enabled (2 ^ 64 - 1)
    let b := populate a.next ⟨0, 33, 0x2010, 0, 0⟩
    accepts a.previous b.next [b, a] &&
    accepts a.previous a.previous [] &&
    !accepts a.previous b.next [] &&
    !accepts a.previous b.next [a] &&
    !accepts a.previous b.next [a, a, b] &&
    !accepts a.previous { b.next with pc := #v[0x2011, 0, 0] } [a, b] &&
    !accepts a.previous { b.next with counter := word 17 } [a, b] &&
    !accepts a.previous { b.next with enabled := if enabled then 0 else 1 } [a, b] &&
    !accepts a.previous b.next [a, populate a.previous b.receipt]) = true := by native_decide

/-- Exact physical cost is independent of the retirement flag. -/
theorem cost : [false, true].all (fun enabled =>
    let evaluated := evaluate (first enabled 0)
    evaluated.2.length == 7 &&
      (evaluated.2.filter (fun item => item.1 == "SP1Byte")).length == 4 &&
      (evaluated.2.filter (fun item => item.1 == "SP1OrdinaryStateReceipt")).length == 1 &&
      (evaluated.2.filter (fun item => item.1 == "SP1OrdinaryObservation")).length == 2) = true := by native_decide

/-- info: exportable ✓ (186 witness cells) -/
#guard_msgs in
#assert_exportable (circuit (p := SP1Prime))

end SP1CleanTest.Core.OrdinaryObservation
