import SP1CleanTest.Alignment.Support.BoundaryFixture
import SP1Clean.Proofs.Chips.HostHintReadChip.Populate
import SP1Clean.Proofs.Chips.HintReadWordChip.Populate
import SP1Clean.Proofs.Chips.HostCallChip.Populate
import SP1Clean.Semantics.Host.HostSnapshot
import SP1Clean.Proofs.Chips.HostCommitChip.Populate
import SP1Clean.Proofs.Chips.HostHaltChip.Formal
import SP1Clean.Proofs.Chips.HostHintLengthChip.Populate
import SP1Clean.Proofs.Completeness.MixedBumpInventory
import SP1Clean.Proofs.Completeness.MixedSyscallInstruction
import SP1Clean.Proofs.Completeness.Providers
import SP1Clean.FormalModel.TraceGen.Inputs
import SP1Clean.Semantics.Sail.SailArithmeticExecute

/-! # Shared host-program fixture construction

Successful semantic host steps and the existing Sail ADDI execute stage supply observations.
The production compiler supplies ordinary and ECALL rows, register refreshes, and State carries.
The host RAM constructor uses its event-clock role. Clean owns witness scheduling, fixed providers and padding.
This finite constructor does not replace the complete Sail execution relation or its open compiler.
-/

namespace SP1CleanTest.Alignment.HostProgram

open Circuit Air.Flat SP1Clean SP1Clean.Semantics SP1Clean.Soundness
open SP1Clean.Semantics SP1Clean.TraceGen LeanRV64D
open SP1CleanTest.Alignment.InstalledAssembly
open SP1Clean.Export.InstalledAssembly

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

/-- Physical refresh rows from the same instruction input as the production bump tables. -/
private def bumpSeeds (input : MixedBumpInput) : List Seed :=
  input.refreshes.map (fun bump => ⟨55, (toElements (memoryBumpCols (p := SP1Prime) bump)).toList⟩) ++
    input.stateBump?.toList.map (fun bump => ⟨56, (toElements (stateBumpCols (p := SP1Prime) bump)).toList⟩)

def addi (construction : Construction) (destination source : BitVec 5)
    (immediate : BitVec 12) : Except String Construction := do
  let before := construction.current
  let some pc := before.sail.registers.get? .PC | throw "absent ADDI PC"
  let .ok _ executed := (runSail (Advance.execute_ITYPE' immediate (.Regidx source) (.Regidx destination) .ADDI))
      before.sail.skeleton | throw "Sail ADDI execute stage failed"
  let after : ExecutionSnapshot := { before with
    sail := retiredSnapshot before.sail executed.regs (pc + 4)
    clock := before.clock + 8 }
  let decoded := LeanRV64D.instruction.ITYPE (immediate, .Regidx source, .Regidx destination, .ADDI)
  let some routeKey := Target.instructionRouteKey decoded | throw "ADDI route missing"
  let view : SP1TransitionView := {
    pc, word := (Action.addi destination source immediate).encoding, decoded
    routeKey, chipId := .addi
    accessPlan? := instructionAccessPlan? decoded before.sail.skeleton after.sail.skeleton }
  let some compiled := compileInstructionEvent? view construction.frontier before.clock
    | throw "ADDI event compiler failed"
  let some event := compiled.routed.forId? .addi | throw "ADDI routed to another family"
  return { construction with
    current := after, frontier := compiled.nextFrontier
    touched := construction.touched ++ [.reg source, .reg destination]
    consumers := construction.consumers ++ bumpSeeds (.ofOrdinary compiled) ++ [⟨8, (toElements event.toAddiInputs).toList⟩] }

def ecall (construction : Construction) (policy : HostPolicy) (program : Target.GuestProgram) :
    Except String Construction := do
  let before := construction.current
  let some (after, event) := before.hostStep? policy program | throw "semantic host step failed"
  let row := HostCallChip.populate (syscallInstruction (p := SP1Prime) construction.frontier event) 0 0
  let message := row.message 0
  let mut next : Construction := { construction with
    current := after
    frontier := (scheduleAccessPlan construction.frontier event.clock (syscallRegisterPlan event)).outgoing
    touched := construction.touched ++ [.reg 5, .reg 10, .reg 11]
    consumers := construction.consumers ++ bumpSeeds (.ofSyscall construction.frontier event.clock event) ++
      [⟨58, (toElements row).toList⟩] }
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
    image, source := incoming, target := final.current
    commitments }
  let padding := if (SP1StateBoundary.haltCode incoming final.current).isSome then [] else
    (emptyConsumers context).filter (fun seed => seed.table == 57)
  let consumers := final.consumers ++ (← memorySeeds context final.frontier final.touched) ++ padding ++
    [⟨88, (toElements final.committed).toList⟩, ⟨89, (toElements final.deferred).toList⟩]
  return (context, consumers, context.header)

/-- Begin replay with the source's actual immutable hint store and commitment banks. -/
def start (incoming : ExecutionSnapshot) : Construction :=
  let queue := HintQueue.ofList incoming.host.io.hints
  { current := incoming, store := queue.1, queueHead := queue.2
    committed := HostCommitBoundary.start (HostCommitEnsemble.sourceValues false incoming.host)
    deferred := HostCommitBoundary.start (HostCommitEnsemble.sourceValues true incoming.host) }

/-- Build one finite program from its complete source and independently chosen statement. -/
def prepare (actions : List Action) (incoming : ExecutionSnapshot) (commitments : CommitmentStatement) :
    Except String (Context × List Seed × SP1PublicIO Fp) := do
  let some checked := (image actions).check | throw "invalid host program image"
  let image := checked.val
  let program := image.toGuestProgram checked.property
  let policy : HostPolicy := ⟨⟨fun address => decide (131072 ≤ address ∧ address < 131072 + 4 * actions.length),
    65536, 2 ^ 48⟩, SP1Prime⟩
  let final ← actions.foldlM (fun state action => match action with
    | .addi destination source immediate => addi state destination source immediate
    | .ecall => ecall state policy program) (start incoming)
  finish image incoming commitments final

end SP1CleanTest.Alignment.HostProgram
