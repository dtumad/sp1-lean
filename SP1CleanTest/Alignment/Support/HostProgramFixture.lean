module

public import SP1CleanTest.Alignment.Support.BoundaryFixture
public import SP1Clean.Proofs.Chips.HostHintReadChip.Populate
public import SP1Clean.Proofs.Chips.HintReadWordChip.Populate
public import SP1Clean.Proofs.Chips.HostCallChip.Populate
public import SP1Clean.Model.Core.HostSnapshot
public import SP1Clean.Proofs.Chips.HostCommitChip.Populate
public import SP1Clean.Proofs.Chips.HostHaltChip.Formal
public import SP1Clean.Proofs.Chips.HostHintLengthChip.Populate
public import SP1Clean.Proofs.Completeness.InstructionEvent
public import SP1Clean.Proofs.Completeness.Providers
public import SP1Clean.FormalModel.TraceGen.Inputs
public import SP1Clean.Model.Semantics.SailArithmeticExecute

/-! # Shared host-program fixture construction

Successful semantic host steps and the existing Sail ADDI execute stage supply observations.
The production access compiler supplies ordinary timestamps, and the host RAM constructor uses
its documented event-clock role. Clean owns witness scheduling, fixed providers and padding.
This finite constructor does not replace the complete Sail execution relation or its open compiler.
-/

@[expose] public section

namespace SP1CleanTest.Alignment.HostProgram

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness
open SP1Clean.Semantics SP1Clean.TraceGen LeanRV64D.Defs
open SP1CleanTest.Alignment.InstalledAssembly

/-- Register setup and actual host calls in the finite programs. -/
inductive Action
  | addi (destination source : BitVec 5) (immediate : BitVec 12)
  | ecall

/-- Legal instruction encodings, independently decoded/executed in Rust. -/
def Action.encoding : Action → BitVec 32
  | .addi destination source immediate => BitVec.ofNat 32
      (immediate.toNat * 2 ^ 20 + source.toNat * 2 ^ 15 + destination.toNat * 2 ^ 7 + 0x13)
  | .ecall => 0x73

/-- A contiguous ROM whose extra unused words remain verifier-owned provider rows. -/
def image (actions : List Action) : ProgramImage :=
  ⟨actions.zipIdx.map (fun (action, index) =>
    (BitVec.ofNat 64 (131072 + 4 * index), action.encoding)), 131072, []⟩

private def word (value : ℕ) : Word Fp := Target.bitVecToWord (BitVec.ofNat 64 value)

structure Construction where
  current : ExecutionSnapshot
  frontier : AccessFrontier := AccessFrontier.initial
  consumers : List Seed := []
  committed : HostCommitChip.State Fp := HostCommitBoundary.initial
  deferred : HostCommitChip.State Fp := HostCommitBoundary.initial
  touched : List MemLoc := []
  store : HintQueue.Store := #[]
  queueHead : ℕ := 0
  queueClock : ℕ := 0

def instruction (current : ExecutionSnapshot) (frontier : AccessFrontier)
    (next : ExecutionSnapshot) : Except String (HostCallChip.Inputs Fp) := do
  let some pc := current.sail.registers.get? .PC | throw "absent PC"
  let some nextPc := next.sail.registers.get? .PC | throw "absent next PC"
  let some code := current.sail.skeleton.get_reg? 5 | throw "absent syscall code"
  let some arg1 := current.sail.skeleton.get_reg? 10 | throw "absent syscall index"
  let some arg2 := current.sail.skeleton.get_reg? 11 | throw "absent syscall word"
  let some result := next.sail.skeleton.get_reg? 5 | throw "absent syscall result"
  let clock := current.clock
  let committed := decide (code.toNat = 16)
  let deferred := decide (code.toNat = 26)
  return HostCallChip.populate
    { state := cpuStateCols clock pc.toNat
      op_a := 5, op_a_memory := registerAccessCols code.toNat (frontier (.reg 5)) (clock + 4), op_a_0 := 0
      op_b := 10, op_b_memory := registerAccessCols arg1.toNat (frontier (.reg 10)) (clock + 3)
      op_c := 11, op_c_memory := registerAccessCols arg2.toNat (frontier (.reg 11)) (clock + 2)
      next_pc := (cpuStateCols (p := SP1Prime) 0 nextPc.toNat).pc
      is_halt := if code = 0 then 1 else 0, op_a_value := word result.toNat
      syscall_id_bytes := U16toU8OperationSafe.populate (word code.toNat)
      is_enter_unconstrained := IsZeroOperation.populate ((code.toNat : Fp) - 3)
      is_hint_len := IsZeroOperation.populate ((code.toNat : Fp) - 240)
      is_halt_zero := IsZeroOperation.populate (code.toNat : Fp)
      is_commit := IsZeroOperation.populate ((code.toNat : Fp) - 16)
      is_commit_deferred := IsZeroOperation.populate ((code.toNat : Fp) - 26)
      digest_index_bits := Vector.ofFn fun index : Fin 8 =>
        if (committed || deferred) && index.val == arg1.toNat then 1 else 0
      digest_word := if committed then Vector.ofFn (fun index : Fin 4 =>
        (arg2.toNat / 256 ^ index.val % 256 : ℕ)) else 0
      op_b_cmp := ⟨U16CompareOperation.populate_bit (word arg1.toNat)[1] SyscallInstrsChip.fieldLimbBound⟩
      op_c_cmp := ⟨U16CompareOperation.populate_bit (word arg2.toNat)[1] SyscallInstrsChip.fieldLimbBound⟩
      is_real := 1 }
    0 0

def addi (construction : Construction) (destination source : BitVec 5)
    (immediate : BitVec 12) : Except String Construction := do
  let before := construction.current
  let some pc := before.sail.registers.get? .PC | throw "absent ADDI PC"
  let .ok _ executed := (Advance.execute_ITYPE' immediate (.Regidx source) (.Regidx destination) .ADDI).run
      before.sail.skeleton | throw "Sail ADDI execute stage failed"
  let after : ExecutionSnapshot := { before with
    sail := { before.sail with registers := executed.regs.insert .PC (pc + 4) }
    clock := before.clock + 8 }
  let decoded := LeanRV64D.Defs.instruction.ITYPE (immediate, .Regidx source, .Regidx destination, .ADDI)
  let some routeKey := Target.instructionRouteKey decoded | throw "ADDI route missing"
  let view : SP1TransitionView := {
    pc, word := (Action.addi destination source immediate).encoding, decoded
    routeKey, chipId := .addi
    accessPlan? := instructionAccessPlan? decoded before.sail.skeleton after.sail.skeleton }
  let some compiled := compileInstructionEvent? view construction.frontier before.clock
    | throw "ADDI event compiler failed"
  unless compiled.memoryBumps.isEmpty do throw "short fixture unexpectedly crossed a timestamp window"
  let some event := compiled.routed.forId? .addi | throw "ADDI routed to another family"
  return { construction with
    current := after, frontier := compiled.nextFrontier
    touched := construction.touched ++ [.reg source, .reg destination]
    consumers := construction.consumers ++ [⟨8, (toElements event.toAddiInputs).toList⟩] }

def ecall (construction : Construction) (policy : HostPolicy) (program : Target.GuestProgram) :
    Except String Construction := do
  let before := construction.current
  let some (after, event) := before.hostStep? policy program | throw "semantic host step failed"
  let row ← instruction before construction.frontier after
  let message := row.message 0
  let mut next : Construction := { construction with
    current := after
    frontier := advancePlan construction.frontier before.clock
      [⟨.opC, .reg 11, event.arg2, event.arg2⟩,
       ⟨.opB, .reg 10, event.arg1, event.arg1⟩,
       ⟨.opA, .reg 5, event.rawCode, event.result⟩]
    touched := construction.touched ++ [.reg 5, .reg 10, .reg 11]
    consumers := construction.consumers ++ [⟨58, (toElements row).toList⟩] }
  if event.rawCode = 0 then
    return { next with consumers := next.consumers ++ [⟨64, (toElements (HostHaltChip.populate message)).toList⟩] }
  if event.rawCode = 3 then
    return { next with consumers := next.consumers ++ [⟨65, (toElements message).toList⟩] }
  if event.rawCode = 240 ∨ event.rawCode = 241 then
    let some executed := before.host.run policy before.sail.readContext | throw "host dispatch disagreed"
    if event.rawCode = 240 then
      let handler := HostHintLengthChip.populate next.store next.queueHead next.queueClock before.clock executed
      return { next with
        queueClock := before.clock
        consumers := next.consumers ++ [⟨if next.queueHead = 0 then 83 else 82, (toElements handler).toList⟩] }
    let handler := HostHintReadChip.populate next.store next.queueHead next.queueClock before.clock executed
    let some node := HintQueue.node? next.store next.queueHead | throw "missing hint node"
    for index in List.range (HintQueue.wordCount node.bytes) do
      let address := event.arg1.toNat + 8 * index
      let location := MemLoc.ram (BitVec.ofNat 61 (address / 8))
      let prior := memoryRecord address (next.frontier location) (before.sail.memory.readWord address)
      let state := cpuStateCols (p := SP1Prime) before.clock event.pc.toNat
      let ram := HostRamAccessChip.populate prior state.clk_high state.clk_0_16 state.clk_16_24
        (word (after.sail.memory.readWord address).toNat)
      let last := decide (index + 1 = HintQueue.wordCount node.bytes)
      let transfer := HintReadWordChip.populate last ram (Address.ofNat next.queueHead) (Address.ofNat index)
      let oldFrontier := next.frontier
      next := { next with
        frontier := fun selected => if selected = location then before.clock + 1 else oldFrontier selected
        touched := next.touched ++ [location]
        consumers := next.consumers ++ [⟨if last then 85 else 84, (toElements transfer).toList⟩] }
    return { next with
      queueClock := before.clock, queueHead := node.tail
      consumers := next.consumers ++ [⟨63, (toElements handler).toList⟩] }
  let deferred := decide (event.rawCode = 26)
  unless event.rawCode = 16 || deferred do throw "fixture expected COMMIT or HALT"
  if bound : event.arg1.toNat < 8 then
    let slot : Fin 8 := ⟨event.arg1.toNat, bound⟩
    let previous := if deferred then next.deferred else next.committed
    let handler := HostCommitChip.populate deferred message previous
    next := { next with consumers := next.consumers ++
      [⟨(if deferred then 74 else 66) + slot.val,
        (toElements (M := HostCommitChip.RowInput) (handler, 1)).toList⟩] }
    return if deferred then { next with deferred := handler.next slot }
      else { next with committed := handler.next slot }
  else throw "commitment index outside the bank"

/-- Finish with shared physical memory boundaries, mutable bank terminals and one public Exit. -/
def finish (image : ProgramImage) (incoming : ExecutionSnapshot) (commitments : CommitmentStatement)
    (final : Construction) : Except String (Context × List Seed × SP1PublicIO Fp) := do
  let context : Context := {
    image, source := incoming, target := final.current.sail.memorySnapshot
    finalHints := HostHintQueue.State.encode final.queueClock final.queueHead final.store.size
    finalHost := final.current.host, commitments }
  let padding := if final.current.host.exitCode.isSome then [] else
    (emptyConsumers context).filter (fun seed => seed.table == 57)
  let consumers := final.consumers ++ (← memorySeeds context final.frontier final.touched) ++ padding ++
    [⟨88, (toElements final.committed).toList⟩, ⟨89, (toElements final.deferred).toList⟩]
  let boundary := boundaryInputs (p := SP1Prime) incoming.clock incoming.pc.toNat final.current.clock final.current.pc.toNat
  let header := { boundary with
    exit_code := (final.current.host.exitCode.getD 0).toNat
    committed_value_digest := CommitmentBoundary.committed commitments
    deferredProofsDigest := CommitmentBoundary.deferred commitments
    commitSyscall := if commitments.commit then 1 else 0
    commitDeferredSyscall := if commitments.commitDeferred then 1 else 0 }
  return (context, consumers, header)

/-- Build one finite program from its complete source and independently chosen statement. -/
def prepare (actions : List Action) (incoming : ExecutionSnapshot) (commitments : CommitmentStatement) :
    Except String (Context × List Seed × SP1PublicIO Fp) := do
  let some checked := (image actions).check | throw "invalid host program image"
  let image := checked.val
  let program := image.toGuestProgram checked.property
  let policy : HostPolicy := ⟨⟨fun address => decide (131072 ≤ address ∧ address < 131072 + 4 * actions.length),
    65536, 2 ^ 48⟩, SP1Prime⟩
  let queue := HintQueue.ofList incoming.host.io.hints
  let initial : Construction := {
    current := incoming, store := queue.1, queueHead := queue.2
    committed := HostCommitBoundary.start (HostCommitEnsemble.sourceValues false incoming.host)
    deferred := HostCommitBoundary.start (HostCommitEnsemble.sourceValues true incoming.host) }
  let final ← actions.foldlM (fun state action => match action with
    | .addi destination source immediate => addi state destination source immediate
    | .ecall => ecall state policy program) initial
  finish image incoming commitments final

end SP1CleanTest.Alignment.HostProgram
