import SP1CleanTest.Alignment.Support.HostProgramFixture

/-! # Complete queue observations and overlapping padded reads

Two persistent hints are observed before and after consumption. Reads reuse the same RAM span,
so the final value cannot stand in for either earlier transfer. Empty, aligned and byte-tail hints
share this program and its production constructors; the final HINT_LEN observes an empty queue.
-/

namespace SP1CleanTest.Alignment.HintProgram

open Circuit SP1Clean SP1Clean.Model.Core SP1Clean.Soundness
open SP1CleanTest.Alignment.InstalledAssembly HostProgram

private def bytes (length : ℕ) : Bytes :=
  (List.range length).map fun index => BitVec.ofNat 8 (19 * index + 3)

/-- Four nonempty observations, two reads, one empty observation and a real HALT. -/
def actions (length : ℕ) : List Action :=
  let observe := [Action.addi 5 0 240, .ecall]
  let read (length : ℕ) := [Action.addi 5 0 241, .addi 11 0 (BitVec.ofNat 12 length), .ecall]
  observe ++ observe ++ read length ++ observe ++ observe ++ read 8 ++ observe ++
    [.addi 5 0 0, .addi 10 0 0, .ecall]

/-- Complete finite instance; the second read overwrites an already authenticated RAM cell. -/
def prepare (length : ℕ) : Except String (Context × List Seed × SP1PublicIO Fp) := do
  unless length = 0 ∨ length = 9 ∨ length = 16 do throw "unsupported finite hint case"
  let program := actions length
  let incoming : ExecutionSnapshot := {
    sail := {
      registers := (((Target.configuredState 131072).regs.insert .x5 240).insert .x10 65536).insert .x11 17
      memory := (HostProgram.image program).initialMemory.writeBytes 65536 (List.replicate 32 255) }
    host := { io := { hints := [bytes length, bytes 8] } }, clock := 9 }
  HostProgram.prepare program incoming default

end SP1CleanTest.Alignment.HintProgram
