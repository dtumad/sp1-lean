module

public import SP1CleanTest.Alignment.Support.HostProgramFixture

/-! # Active HALT in the complete installed assembly

The shared semantic host step and finalizers authenticate all accessed registers. A real HALT
supplies the sole Exit receipt; the legacy continuing-padding component has no row.
-/

@[expose] public section

namespace SP1CleanTest.Alignment.HaltAssembly
open Circuit SP1Clean SP1Clean.Model.Core SP1Clean.Soundness
open SP1CleanTest.Alignment.InstalledAssembly

private def image := HostProgram.image [.ecall]
private def source (exit : ℕ) : ExecutionSnapshot where
  sail := {
    registers := (((Target.configuredState 131072).regs.insert .x5 0).insert
      .x10 (BitVec.ofNat 64 exit)).insert .x11 17
    memory := image.initialMemory }
  host := {}
  clock := 9

/-- HALT's canonical exit and terminal PC are public. -/
def header (exit : ℕ) : SP1PublicIO Fp :=
  { (boundaryInputs 9 131072 273 1) with exit_code := (exit : ℕ) }

/-- One actual semantic HALT with shared physical boundary construction. -/
def prepare (exit : ℕ) : Except String (Context × List Seed) := do
  let (context, consumers, _) ← HostProgram.prepare [.ecall] (source exit) default
  return (context, consumers)

end SP1CleanTest.Alignment.HaltAssembly
