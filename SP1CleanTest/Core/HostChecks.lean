import SP1Clean.Proofs.Chips.HostCallChip.Populate
import SP1Clean.Model.SP1Field
import ToClean.Air.EnsembleExport

/-! # Executing native host-circuit regressions

Evaluate complete witness programs, local assertions, and the fixed syscall lookup. Byte and
Memory guarantees are checked directly; Program messages must be the fixture's canonical ECALL
at address `2^16`. Structural-channel messages are retained for each test's ledger assertions.
These fixture checks do not assert whole-machine balance or authentic boot-memory contents.
-/

namespace SP1CleanTest.Core.HostChecks

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core

private abbrev Fp := ZMod SP1Prime
abbrev Ledger := List (String × List Fp × Fp)

private instance byteDecidable (op : ByteOpcode) (a b c : Fp) : Decidable (op.constrain a b c) := by
  cases op <;> unfold ByteOpcode.constrain <;> infer_instance

private def byteValid (values : List Fp) : Bool :=
  match values with
  | [opcode, a, b, c] =>
    [ByteOpcode.AND, .OR, .XOR, .U8Range, .LTU, .MSB, .Range].any fun op =>
      opcode == (op.idx : Fp) && decide (op.constrain a b c)
  | _ => false

def evaluateProgram (program : Circuit Fp Unit) (inputs : List Fp)
    (corrupt : Option ℕ := none) : Bool × Ledger :=
  let honest := (program.proverEnvironment (ProverHint.empty Fp) inputs).toEnvironment
  let env : Environment Fp := { honest with get := fun i =>
    if corrupt == (some (i - inputs.length)) && inputs.length ≤ i then honest.get i + 1 else honest.get i }
  let operations := (program.operations inputs.length).toFlat
  let fixed := FiniteLookup.ofStatic (SyscallKind.fixedTable (p := SP1Prime))
  let valid := operations.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup lookup => lookup.table.name == fixed.table.name &&
      fixed.rows.any (fun row => row.toArray == (lookup.entry.map env).toArray)
    | .witness .. => true
    | .interact interaction =>
      if env interaction.mult == 0 then true
      else if interaction.channel.name == "SP1Byte" then byteValid (interaction.msg.map env).toList
      else if interaction.channel.name == "SP1Memory" then
        match (interaction.msg.map env).toList with
        | [_, low, _, _, _, a, b, c, d] =>
          low.val < 2 ^ 24 && [a, b, c, d].all (fun limb => limb.val < 65536)
        | _ => false
      else if interaction.channel.name == "SP1Program" then
        (interaction.msg.map env).toList == [0, 1, 0, 50, 5, 10, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0]
      else ["SP1State", "SP1Exit", "SP1Syscall", "SP1PublicValues", "sp1.native.host_call",
        "sp1.native.commit_state", "sp1.native.deferred_state"].contains interaction.channel.name
  (valid, (FlatOperation.interactions operations).filterMap fun interaction =>
    if env interaction.mult == 0 then none else
      some (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult))
end SP1CleanTest.Core.HostChecks
