import SP1Clean.Model.SP1Field
import SP1Clean.Proofs.Chips.AddChip.Formal
import SP1Clean.Proofs.Chips.AddChip.Witgen
import SP1Clean.Proofs.Chips.AddiChip.Formal
import SP1Clean.Proofs.Chips.AddiChip.Witgen
import SP1Clean.Proofs.Chips.AddwChip.Formal
import SP1Clean.Proofs.Chips.AddwChip.Witgen
import SP1Clean.Proofs.Chips.AluX0Chip.Formal
import SP1Clean.Proofs.Chips.AluX0Chip.Witgen
import SP1Clean.Proofs.Chips.BitwiseChip.Formal
import SP1Clean.Proofs.Chips.BitwiseChip.Witgen
import SP1Clean.Proofs.Chips.BranchChip.Formal
import SP1Clean.Proofs.Chips.BranchChip.Witgen
import SP1Clean.Proofs.Chips.DivRemChip.Formal
import SP1Clean.Proofs.Chips.DivRemChip.Witgen
import SP1Clean.Proofs.Chips.JalChip.Formal
import SP1Clean.Proofs.Chips.JalChip.Witgen
import SP1Clean.Proofs.Chips.JalrChip.Formal
import SP1Clean.Proofs.Chips.JalrChip.Witgen
import SP1Clean.Proofs.Chips.LoadByteChip.Formal
import SP1Clean.Proofs.Chips.LoadByteChip.Witgen
import SP1Clean.Proofs.Chips.LoadDoubleChip.Formal
import SP1Clean.Proofs.Chips.LoadDoubleChip.Witgen
import SP1Clean.Proofs.Chips.LoadHalfChip.Formal
import SP1Clean.Proofs.Chips.LoadHalfChip.Witgen
import SP1Clean.Proofs.Chips.LoadWordChip.Formal
import SP1Clean.Proofs.Chips.LoadWordChip.Witgen
import SP1Clean.Proofs.Chips.LoadX0Chip.Formal
import SP1Clean.Proofs.Chips.LoadX0Chip.Witgen
import SP1Clean.Proofs.Chips.LtChip.Formal
import SP1Clean.Proofs.Chips.LtChip.Witgen
import SP1Clean.Proofs.Chips.MulChip.Formal
import SP1Clean.Proofs.Chips.MulChip.Witgen
import SP1Clean.Proofs.Chips.ShiftLeftChip.Formal
import SP1Clean.Proofs.Chips.ShiftLeftChip.Witgen
import SP1Clean.Proofs.Chips.ShiftRightChip.Formal
import SP1Clean.Proofs.Chips.ShiftRightChip.Witgen
import SP1Clean.Proofs.Chips.StoreByteChip.Formal
import SP1Clean.Proofs.Chips.StoreByteChip.Witgen
import SP1Clean.Proofs.Chips.StoreDoubleChip.Formal
import SP1Clean.Proofs.Chips.StoreDoubleChip.Witgen
import SP1Clean.Proofs.Chips.StoreHalfChip.Formal
import SP1Clean.Proofs.Chips.StoreHalfChip.Witgen
import SP1Clean.Proofs.Chips.StoreWordChip.Formal
import SP1Clean.Proofs.Chips.StoreWordChip.Witgen
import SP1Clean.Proofs.Chips.SubChip.Formal
import SP1Clean.Proofs.Chips.SubChip.Witgen
import SP1Clean.Proofs.Chips.SubwChip.Formal
import SP1Clean.Proofs.Chips.SubwChip.Witgen
import SP1Clean.Proofs.Chips.UTypeChip.Formal
import SP1Clean.Proofs.Chips.UTypeChip.Witgen
import Clean.Circuit.WitnessExport

/-! # Witness-generator exportability

The point of moving chip witness generation off Lean closures and onto Clean's witness IR is that
the generator becomes *data* — serializable, so a Rust prover can run it. `#assert_exportable` is the
check that this actually happened: it walks a circuit's flattened operations and fails, naming the
flat indices of the offending witnesses, if any of them is still a `WitgenIR.native` closure. On
success it prints the circuit's witness cell count.

That makes this file the thing that keeps "we removed the closures" honest. `scripts/check_no_witness_native.sh`
greps for the tokens; this evaluates the circuits.

**Coverage is the converted set.** A chip is listed here exactly when its `main` is
closure-free, so adding a line is the last step of converting a chip and the line fails
loudly if a conversion regresses. With the DivRem port (the terminal wave: 30 sites, 217
cells) every registered chip is listed.

The nine memory chips appear here without ever having been converted individually: their only
witnesses come from the `AddressOperation` subcircuit, so converting that one operation cleared all
of them at once.

These are `#eval`-backed commands rather than proofs, so they contribute no axioms — but they do run
compiled code, which is why they live in the test library. -/

namespace SP1Clean.ExportableTests

open SP1Clean

/-! The concrete field and all standard size instances come from `Model.SP1Field`; test code does
not own a second spelling of the production characteristic. -/

/-! ## ALU and control flow (waves W1–W2) -/

/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (AddChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (AddiChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (SubChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (3 witness cells) -/
#guard_msgs in
#assert_exportable (AddwChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (3 witness cells) -/
#guard_msgs in
#assert_exportable (SubwChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (7 witness cells) -/
#guard_msgs in
#assert_exportable (UTypeChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (8 witness cells) -/
#guard_msgs in
#assert_exportable (JalChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (9 witness cells) -/
#guard_msgs in
#assert_exportable (JalrChip.circuit (p := SP1Prime))

/-! ## Memory (wave W3) — cleared wholesale by the `AddressOperation` conversion -/

/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (LoadByteChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (LoadHalfChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (LoadWordChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (LoadDoubleChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (LoadX0Chip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (StoreByteChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (StoreHalfChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (StoreWordChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (StoreDoubleChip.circuit (p := SP1Prime))

/-! ## Hint-driven ALU (wave W4) — flags through `FExpr.hintGet` -/

/-- info: exportable ✓ (19 witness cells) -/
#guard_msgs in
#assert_exportable (BitwiseChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (12 witness cells) -/
#guard_msgs in
#assert_exportable (LtChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (20 witness cells) -/
#guard_msgs in
#assert_exportable (BranchChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (54 witness cells) -/
#guard_msgs in
#assert_exportable (MulChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (33 witness cells) -/
#guard_msgs in
#assert_exportable (ShiftLeftChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (37 witness cells) -/
#guard_msgs in
#assert_exportable (ShiftRightChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (217 witness cells) -/
#guard_msgs in
#assert_exportable (DivRemChip.circuit (p := SP1Prime))

/-! ## Chips that witness nothing at all -/

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (AluX0Chip.circuit (p := SP1Prime))

end SP1Clean.ExportableTests
