import SP1CleanTest.Alignment.Support.HostProgramFixture
import SP1CleanTest.Alignment.Support.OrdinaryAssemblyFixture

/-! # Constrained ENTER replay, VERIFY, and HALT

The ROM includes a genuine EXIT_UNCONSTRAINED path. Released execution visits it and rolls it
back; the constrained trace observes ENTER's zero return and branches over it. The subsequent VERIFY and the earlier ENTER consume two rows of the same installed receiver.
-/

namespace SP1CleanTest.Alignment.EnterAssembly

open Circuit SP1Clean SP1Clean.Semantics SP1Clean.Soundness SP1Clean.TraceGen
open SP1CleanTest.Alignment.InstalledAssembly
open SP1Clean.Export.InstalledAssembly

/-- The constrained branch skips EXIT, then selects VERIFY followed by HALT. -/
def image : ProgramImage :=
  ⟨([0x73, 0x00028663, 0x00400293, 0x73, 0x01b00293, 0x73, 0x00000293, 0x73] : List (BitVec 32)).zipIdx.map
    (fun (word, index) => (BitVec.ofNat 64 (131072 + 4 * index), word)), 131072, []⟩

/-- Actual host steps surround the production branch event compiler. -/
def prepare : Except String (Context × List Seed × SP1PublicIO Fp) := do
  let some checked := image.check | throw "invalid ENTER image"
  let image := checked.val
  let program := image.toGuestProgram checked.property
  let policy : HostPolicy := ⟨⟨fun address => decide (131072 ≤ address ∧ address < 131104), 65536, 2 ^ 48⟩, SP1Prime⟩
  let incoming : ExecutionSnapshot := {
    sail := {
      registers := ((Target.configuredState 131072).regs.insert .x5 3).insert .x11 (BitVec.allOnes 64)
      memory := image.initialMemory }
    host := {}, clock := 9 }
  let first ← HostProgram.ecall { current := incoming } policy program
  let after : ExecutionSnapshot := { first.current with
    sail := retiredSnapshot first.current.sail first.current.sail.registers 131088
    clock := first.current.clock + 8 }
  let compiled ← OrdinaryAssembly.compile
    ⟨first.current, after, .BTYPE (12, .Regidx 0, .Regidx 5, .BEQ), 0x00028663⟩ first.frontier
  let branched : HostProgram.Construction := { first with
    current := after, frontier := compiled.nextFrontier
    touched := first.touched ++ compiled.plan.map (·.loc)
    consumers := first.consumers ++ [← OrdinaryAssembly.instructionSeed compiled.routed] }
  let selectVerify ← HostProgram.addi branched 5 0 27
  let verified ← HostProgram.ecall selectVerify policy program
  let selectHalt ← HostProgram.addi verified 5 0 0
  let final ← HostProgram.ecall selectHalt policy program
  HostProgram.finish image incoming default final

end SP1CleanTest.Alignment.EnterAssembly
