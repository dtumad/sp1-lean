import SP1Clean.Native.Operations.InitialMemoryLookup
import SP1Clean.Model.SP1Field
import Clean.Circuit.WitnessExport

/-! # Initial-memory AIR regressions

These checks run the circuit's witness program and evaluate its actual flattened assertions and
fixed lookups. Interaction balance belongs to the ensemble tests. The negative cases distinguish
fixed-row authentication from address containment: either can fail while the other still holds.
-/

namespace SP1CleanTest.Core.InitialMemoryLookup

open Circuit SP1Clean.Model.Core SP1Clean.InitialMemoryLookup

private abbrev Fp := ZMod SP1Clean.SP1Prime

private def memory : ByteMemory := ⟨[(7, 42), (0, 13), (7, 9), (15, 255)]⟩

/-- info: exportable ✓ (64 witness cells) -/
#guard_msgs in
#assert_exportable (circuit (p := SP1Clean.SP1Prime) memory 16 (by norm_num))

/-- Evaluate flattened assertions and the concrete initial-memory lookup; balance is checked separately. -/
def localConstraints (memory : ByteMemory) (limit : ℕ) (env : Environment Fp)
    (operations : List (FlatOperation Fp)) : Bool :=
  operations.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup lookup =>
      if arity : lookup.table.arity = size MemoryIntervalRow then
        lookup.table.name == "sp1.native.initial_memory" && (memory.intervals limit).any fun interval =>
          toElements (interval.encode (p := SP1Clean.SP1Prime)) == arity ▸ lookup.entry.map env
      else false
    | .witness .. | .interact .. => true

private def accepts (input : Inputs Fp) : Bool :=
  let program := main memory 16 (varFromOffset Inputs 0)
  let env := (program.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  localConstraints memory 16 env (program.operations (size Inputs)).toFlat

/-- Every in-range byte, including default-zero gaps and both endpoints, constructs a valid row. -/
theorem constructedRows : (List.range 16).all (fun address =>
    ((populate? memory 16 address : Option (Inputs Fp)).map accepts).getD false) = true := by
  native_decide

/-- A forged byte, a genuine but non-containing interval, and its exclusive upper endpoint fail. -/
theorem rejectsForgedRows :
    [accepts (populate 7 ⟨7, 8, 99⟩), accepts (populate 6 ⟨7, 8, 42⟩),
      accepts (populate 8 ⟨7, 8, 42⟩)] = [false, false, false] := by
  native_decide

example : (populate? (p := SP1Clean.SP1Prime) memory 16 16).isSome = false := by native_decide

example : ((populate? (p := SP1Clean.SP1Prime) memory (2 ^ 48) (2 ^ 48 - 1)).map
    (fun input => input.interval.value.val)) = some 0 := by native_decide

end SP1CleanTest.Core.InitialMemoryLookup
