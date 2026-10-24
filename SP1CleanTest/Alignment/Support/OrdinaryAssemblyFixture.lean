module

public import SP1CleanTest.Alignment.Support.BoundaryFixture
public import SP1Clean.Proofs.Completeness.InstructionEvent
public import SP1Clean.Proofs.Completeness.Providers
public import SP1Clean.Proofs.Chips.LoadDoubleChip.Complete
public import SP1Clean.Proofs.Chips.StoreDoubleChip.Complete
public import SP1Clean.Proofs.Chips.BranchChip.Complete

/-! # Arithmetic, repeated RAM accesses and branches in one assembly

Literal finite source/target observations feed the production instruction-event compiler and
its access scheduler. Rust independently executes the encoded program. These fixtures do not
implement an interpreter or assert a general Sail retirement theorem. Sparse RAM is materialized
only at the observed cell for the existing access-plan projection, never as the full 48-bit map.
-/

@[expose] public section

namespace SP1CleanTest.Alignment.OrdinaryAssembly

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness
open SP1Clean.Semantics SP1Clean.TraceGen LeanRV64D.Defs
open SP1CleanTest.Alignment.InstalledAssembly

/-- One located decoded instruction and its finite outgoing observation. -/
structure Step where
  source : ExecutionSnapshot
  target : ExecutionSnapshot
  decoded : instruction
  word : BitVec 32

/-- ADDI, SD, LD, ADDI, SD, LD, taken BEQ, skipped ADDI, ADDI, untaken BEQ. -/
def image : ProgramImage :=
  ⟨([0x00410113, 0x0020b023, 0x0000b103, 0x00110113, 0x0020b023,
      0x0000b183, 0x00310463, 0x06310113, 0x00110113, 0x00310463] : List (BitVec 32)).zipIdx.map
    (fun (word, index) => (BitVec.ofNat 64 (131072 + 4 * index), word)), 131072, []⟩

/-- Source values are independent of the generated circuit rows. -/
def source : ExecutionSnapshot where
  sail := {
    registers := ((Target.configuredState 131072).regs.insert .x1 65536).insert .x2 3
    memory := image.initialMemory }
  host := {}
  clock := 9

private def next (source : ExecutionSnapshot) (pc : ℕ) : ExecutionSnapshot :=
  { source with
    sail.registers := source.sail.registers.insert .PC (BitVec.ofNat 64 pc)
    clock := source.clock + 8 }

private def store (source : ExecutionSnapshot) (value : BitVec 64) : ByteMemory :=
  source.sail.memory.writeBytes 65536 ((List.finRange 8).map fun i => value.extractLsb' (8 * i.val) 8)

/-- The nine executed transitions; the encoded but skipped instruction has no event. -/
def steps : List Step := Id.run do
  let a := { (next source 131076) with sail.registers :=
    (next source 131076).sail.registers.insert .x2 7 }
  let b := { (next a 131080) with sail.memory := store a 7 }
  let c := next b 131084
  let d := { (next c 131088) with sail.registers := (next c 131088).sail.registers.insert .x2 8 }
  let e := { (next d 131092) with sail.memory := store d 8 }
  let f := { (next e 131096) with sail.registers := (next e 131096).sail.registers.insert .x3 8 }
  let g := next f 131104
  let h := { (next g 131108) with sail.registers := (next g 131108).sail.registers.insert .x2 9 }
  let i := next h 131112
  return [
    ⟨source, a, .ITYPE (4, .Regidx 2, .Regidx 2, .ADDI), 0x00410113⟩,
    ⟨a, b, .STORE (0, .Regidx 2, .Regidx 1, 8), 0x0020b023⟩,
    ⟨b, c, .LOAD (0, .Regidx 1, .Regidx 2, false, 8), 0x0000b103⟩,
    ⟨c, d, .ITYPE (1, .Regidx 2, .Regidx 2, .ADDI), 0x00110113⟩,
    ⟨d, e, .STORE (0, .Regidx 2, .Regidx 1, 8), 0x0020b023⟩,
    ⟨e, f, .LOAD (0, .Regidx 1, .Regidx 3, false, 8), 0x0000b183⟩,
    ⟨f, g, .BTYPE (8, .Regidx 3, .Regidx 2, .BEQ), 0x00310463⟩,
    ⟨g, h, .ITYPE (1, .Regidx 2, .Regidx 2, .ADDI), 0x00110113⟩,
    ⟨h, i, .BTYPE (8, .Regidx 3, .Regidx 2, .BEQ), 0x00310463⟩]

private def observed (snapshot : SailSnapshot) : SailState :=
  { snapshot.skeleton with
    mem := (List.range 8).foldl
      (fun memory offset => memory.insert (65536 + offset) (snapshot.memory.read (65536 + offset))) ∅ }

/-- Convert one routed payload using its production input constructor. -/
def instructionSeed (routed : RoutedEvent) : Except String Seed := do
  let cells ← match routed with
    | ⟨.addi, event⟩ => pure (toElements (F := Fp) event.toAddiInputs).toList
    | ⟨.branch, event⟩ => pure (toElements (F := Fp) event.toBranchInputs).toList
    | ⟨.loadDouble, event⟩ => pure (toElements (F := Fp) event.toLoadDoubleInputs).toList
    | ⟨.storeDouble, event⟩ => pure (toElements (F := Fp) event.toStoreDoubleInputs).toList
    | _ => throw "ordinary fixture routed outside its four families"
  return ⟨7 + InstructionChipId.all.idxOf routed.id, cells⟩

/-- The canonical compiler owns routing and all displaced timestamps, including aliases. -/
def compile (step : Step) (frontier : AccessFrontier) : Except String CompiledInstructionEvent := do
  let some pc := step.source.sail.registers.get? .PC | throw "absent ordinary PC"
  let some routeKey := Target.instructionRouteKey step.decoded | throw "missing route key"
  let some chipId := Target.instructionRouteId step.decoded | throw "missing route"
  let view : SP1TransitionView := {
    pc, word := step.word, decoded := step.decoded, routeKey, chipId
    accessPlan? := instructionAccessPlan? step.decoded (observed step.source.sail) (observed step.target.sail) }
  let some compiled := compileInstructionEvent? view frontier step.source.clock | throw "ordinary compiler failed"
  unless compiled.memoryBumps.isEmpty do throw "short ordinary fixture crossed a timestamp window"
  return compiled

/-- Any contiguous local cut uses the same image and complete finite endpoints. -/
def prepare (start : ℕ := 0) (count : ℕ := 9) : Except String (Context × List Seed × SP1PublicIO Fp) := do
  let selected := (steps.drop start).take count
  let incoming := (steps[start]?).map Step.source |>.getD ((steps.getLast?).map Step.target |>.getD source)
  let outgoing := (selected.getLast?).map Step.target |>.getD incoming
  let mut frontier := AccessFrontier.initial
  let mut consumers : List Seed := []
  let mut touched : List MemLoc := []
  for step in selected do
    let compiled ← compile step frontier
    consumers := consumers ++ [← instructionSeed compiled.routed]
    frontier := compiled.nextFrontier
    touched := touched ++ compiled.plan.map (·.loc)
  let context : Context := {
    image, source := incoming, target := outgoing.sail.memorySnapshot
    finalHints := HostHintQueue.State.encode 0 0 0, finalHost := outgoing.host, commitments := default }
  if selected.isEmpty then
    return (context, emptyConsumers context,
      boundaryInputs incoming.clock incoming.pc.toNat outgoing.clock outgoing.pc.toNat)
  consumers := consumers ++ (← memorySeeds context frontier touched) ++
    (emptyConsumers context).filter (fun seed => seed.table == 57 || seed.table == 88 || seed.table == 89)
  return (context, consumers, boundaryInputs incoming.clock incoming.pc.toNat outgoing.clock outgoing.pc.toNat)

end SP1CleanTest.Alignment.OrdinaryAssembly
