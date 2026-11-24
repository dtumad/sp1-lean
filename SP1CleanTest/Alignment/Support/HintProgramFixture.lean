import SP1CleanTest.Alignment.Support.HostProgramFixture

/-! # Complete queue observations and overlapping padded reads

The first two hint reads reuse the same RAM span, so their memory records distinguish both
transfers. The nine-byte case also reads an empty hint at a distinct address and peeks the
exhausted queue three times. The three registered handler tables each need one padding row.
-/

namespace SP1CleanTest.Alignment.HintProgram

open Circuit SP1Clean SP1Clean.Semantics SP1Clean.Soundness
open SP1CleanTest.Alignment.InstalledAssembly HostProgram
open SP1Clean.Export.InstalledAssembly

private def bytes (length : ℕ) : Bytes :=
  (List.range length).map fun index => BitVec.ofNat 8 (19 * index + 3)

/-- The nine-byte case exercises three distinct calls in each native hint handler. -/
def actions (length : ℕ) : List Action :=
  let observe := [Action.addi 5 0 240, .ecall]
  let read (length : ℕ) := [Action.addi 5 0 241, .addi 11 0 (BitVec.ofNat 12 length), .ecall]
  let calls := if length = 9 then
    observe ++ read length ++ observe ++ read 8 ++ observe ++ [.addi 10 10 24] ++ read 0 ++ observe ++ observe ++ observe
  else observe ++ observe ++ read length ++ observe ++ observe ++ read 8 ++ observe
  calls ++ [.addi 5 0 0, .addi 10 0 0, .ecall]

/-- Complete finite instance; the second read overwrites an already authenticated RAM cell. -/
def prepare (length : ℕ) : Except String (Context × List Seed × SP1PublicIO Fp) := do
  unless length = 0 ∨ length = 9 ∨ length = 16 do throw "unsupported finite hint case"
  let program := actions length
  let incoming : ExecutionSnapshot := {
    sail := {
      registers := (((Target.configuredState 131072).regs.insert .x5 240).insert .x10 65536).insert .x11 17
      memory := (HostProgram.image program).initialMemory.writeBytes 65536 (List.replicate 32 255) }
    host := { io := { hints := [bytes length, bytes 8] ++ (if length = 9 then [[]] else []) } }, clock := 9 }
  HostProgram.prepare program incoming default

end SP1CleanTest.Alignment.HintProgram
