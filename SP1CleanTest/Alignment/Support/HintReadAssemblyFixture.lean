module

public import SP1CleanTest.Alignment.Support.HostProgramFixture
public import SP1CleanTest.Core.HintReadFixtures

/-! # Complete active HINT_READ assembly fixture

The shared constructor records the complete source/target and every padded word. The sixteen-byte
case pads three RAM boundary/check rows to four; the twenty-four-byte case pads three nonfinal
word consumers. All scheduling and padding use Clean's built-in machinery.
-/

@[expose] public section

namespace SP1CleanTest.Alignment.HintReadAssembly
open Circuit SP1Clean SP1Clean.Model.Core SP1Clean.Soundness
open SP1CleanTest.Alignment.InstalledAssembly

private abbrev image := SP1CleanTest.Core.HintReadFixtures.image
private abbrev bytes := SP1CleanTest.Core.HintReadFixtures.bytes
private def source (length : ℕ) : ExecutionSnapshot where
  sail := {
    registers := (((Target.configuredState 131072).regs.insert .x5 241).insert .x10 65536).insert
      .x11 (BitVec.ofNat 64 length)
    memory := image.initialMemory.writeBytes 65536
      (List.replicate (8 * HintQueue.wordCount (bytes length)) 255) }
  host := { io := { hints := [bytes length] } }
  clock := 9

/-- Public endpoints of one continuing HINT_READ call at clock nine. -/
def header : SP1PublicIO Fp := boundaryInputs 9 131072 273 131076

/-- Construct all physical consumers from the shared semantic host-step constructor. -/
def prepare (length : ℕ) : Except String (Context × List Seed) := do
  let (context, consumers, _) ← HostProgram.prepare [.ecall] (source length) default
  return (context, consumers)

end SP1CleanTest.Alignment.HintReadAssembly
