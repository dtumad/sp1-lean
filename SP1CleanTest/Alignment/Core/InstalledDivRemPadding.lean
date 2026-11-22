import SP1Clean.Proofs.Completeness.InstalledInstructionTables

/-! # The fourth row produced by the installed DivRem scheduler

Three successive unsigned divides exercise the first nontrivial demand-padding boundary.
The regression runs the registered row generators, decodes committed inputs from the full
physical rows, and inspects the actual receipt emitted by the fourth row.
-/

namespace SP1CleanTest.Alignment.Core.InstalledDivRemPadding
open SP1Clean SP1Clean.TraceGen SP1Clean.Soundness Circuit Air.Flat WitnessGeneration

private abbrev Fp := ZMod SP1Prime

private def event (n : Nat) : RTypeEvent where
  clk := 9 + 8 * n
  pc := 65536 + 4 * n
  opcode := 16
  opA := 1
  opB := 2
  opC := 3
  b := 28
  c := 4
  prevA := if n = 0 then 0 else 7
  prevTsA := if n = 0 then 0 else 8 * n + 5
  prevTsB := if n = 0 then 0 else 8 * n + 4
  prevTsC := if n = 0 then 0 else 8 * n + 3

private def decode (row : GeneratedRow Fp) : DivRemChip.Inputs Fp :=
  fromElements (rowPrefix (size DivRemChip.Inputs) row.values)

private def check : Bool := Id.run do
  let registered := ProtectedOrdinaryReceipt.component (p := SP1Prime) .divRem
  let initial := ComponentState.initial registered none
  let data := ProverData.empty Fp
  let hint := ProverHint.empty Fp
  let before := [event 0, event 1, event 2].foldl (fun state e => state.pushRow
    (completeRow state (toElements (e.toDivRemInputs (p := SP1Prime))).toArray data hint)) initial
  let (after, interactions) := before.pad data hint
  let some last := after.rows[3]? | return false
  let input := decode last
  let receipts := interactions.filter (·.channel.name == "SP1OrdinaryStateReceipt")
  return before.rows.size == 3 && after.rows.size == 4 &&
    (after.rows.map (fun row => (decode row).is_real)) == #[1, 1, 1, 0] &&
    input.selectors == #v[0, 0, 0, 0, 0, 0, 0] &&
    input.adapter.op_c_memory.prev_value == #v[1, 0, 0, 0] &&
    receipts.map (·.mult) == [0]

/-- A real inactive DIVU row with denominator one occupies the fourth physical slot. -/
theorem three_to_four : check = true := by native_decide

end SP1CleanTest.Alignment.Core.InstalledDivRemPadding
