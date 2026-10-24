module

public import SP1CleanTest.Alignment.Support.HostProgramFixture

/-! # Complete commitment programs

Repeated and full-bank declarations share the semantic host dispatcher, access compiler and
physical boundary construction with the other finite host programs. Statement words are chosen
independently of the mutable banks. This does not establish general compiler completeness.
-/

@[expose] public section

namespace SP1CleanTest.Alignment.CommitAssembly
open Circuit SP1Clean SP1Clean.Model.Core SP1Clean.Soundness
open SP1CleanTest.Alignment.InstalledAssembly HostProgram

/-- A repeated declaration exercises power-of-two padding and remains a continuing segment. -/
def repeated : List Action := [.ecall, .ecall, .ecall]

/-- Every slot in both banks, followed by a real HALT. Register aliases recur between calls. -/
def complete : List Action :=
  let bank := (List.range 8).flatMap fun slot =>
    if slot = 7 then [.ecall] else [.ecall, .addi 10 10 1]
  bank ++ [.addi 5 0 26, .addi 10 0 0] ++ bank ++
    [.addi 5 0 0, .addi 10 0 0, .ecall]

/-- Statement values are chosen independently of the mutable host's final recording arrays. -/
def statement (allSlots deferred : Bool) (slot : Fin 8) (value : BitVec 32) : CommitmentStatement :=
  let bank := if allSlots then Vector.replicate 8 value else (Vector.replicate 8 0).set slot value
  { committed := if allSlots || !deferred then bank else Vector.replicate 8 0
    deferred := if allSlots || deferred then bank else Vector.replicate 8 0
    commit := allSlots || !deferred, commitDeferred := allSlots || deferred }

/-- The shared semantic dispatcher and access compiler produce all consumer inputs. -/
def prepare (allSlots deferred : Bool) (slot : Fin 8 := 0) (value : BitVec 32 := 131075) (stop : Bool := false) :
    Except String (Context × List Seed × SP1PublicIO Fp) := do
  let actions := if allSlots then complete else repeated ++
    if stop then [.addi 5 0 0, .addi 10 0 0, .ecall] else []
  let incoming : ExecutionSnapshot := {
    sail := {
      registers := (((Target.configuredState 131072).regs.insert .x5 (if deferred then 26 else 16)).insert
        .x10 (BitVec.ofNat 64 slot.val)).insert .x11 (value.setWidth 64)
      memory := (HostProgram.image actions).initialMemory }
    host := {}, clock := 9 }
  HostProgram.prepare actions incoming (statement allSlots deferred slot value)

end SP1CleanTest.Alignment.CommitAssembly
