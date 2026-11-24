import SP1Clean.Export.WriteReplayChannels
import SP1Clean.Export.WriteGuestLanes

/-! # Read the original CPU Memory chains from the realized Sail source -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Channels Semantics Soundness NativeCore WriteSourceRegistry WriteEffects
open TraceGen.MemoryHistoryAccess (heldAt ofRecords)
private abbrev F := ZMod SP1Prime
private abbrev Pair := MemoryRecordChain.Pair SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}

/-- The original histories for every bus location, as ordered predecessor/successor pairs. -/
abbrev MemoryPaths := MemLoc → List (MemoryRecordChain.Pair SP1Prime)

/-- Replay a physical location from its realized initial Sail register or RAM word. -/
def MemoryPaths.wordAt (paths : MemoryPaths) (s : ExecutionSnapshot) (loc : MemLoc) (clock : Nat) : Option (BitVec 64) :=
  (locContent s.sail.realize loc).map (fun seed => heldAt seed clock ((paths loc).map ofRecords))

/-- Read the exact little-endian guest byte from the aligned RAM word at the given clock. -/
def MemoryPaths.byteAt (paths : MemoryPaths) (s : ExecutionSnapshot) (clock address : Nat) : Option (BitVec 8) :=
  (paths.wordAt s (.ram (BitVec.ofNat 61 (address / 8))) clock).map (fun word => word.extractLsb' (8 * (address % 8)) 8)

/-- A complete per-location trace is either physically absent or is a strictly ordered walk
between the original frontiers, starting at the realized Sail word. -/
def FrontierPath (path : List Pair) (initial final : Option (MemoryMsg F)) (content : Option (BitVec 64)) : Prop :=
  (initial = none ∧ final = none ∧ path = []) ∨ ∃ first last, initial = some first ∧ final = some last ∧
    content = some first.value.toBitVec64 ∧ Walk.IsWalk id first last path ∧ (path.map (fun e => MemoryMsg.timeNat e.2)).Pairwise (· < ·)

/-- All selected paths exhaust the same original CPU, HINT_READ and refresh occurrences,
and serve every physical read from their shared, source-authenticated contents. -/
def RealizedMemoryReplay (w : EnsembleWitness (assembly image source target final)) (paths : MemoryPaths) : Prop :=
  let old := supervisor (observed w)
  let core := HostFinalMemory.coreWitness (HostObserved.baseWitness old)
  let boundary := HostFinalMemory.baseWitness (HostObserved.baseWitness old)
  ∃ aligned, List.Forall₂ AlignedFacts aligned ((LocalCore.executionRows core).map (ExecutionRow.facts boundary.data)) ∧
    ∀ loc, (paths loc).Perm (MemoryRecordChain.atLocation loc (replayEntries w aligned)) ∧
      FrontierPath (paths loc) (LocalCore.memoryInitialFrontier core loc) (LocalCore.memoryFinalFrontier core loc) (locContent source.sail.realize loc) ∧
      ∀ clock value, QueryAt (WriteSourceRegistry.raw old) loc clock value → paths.wordAt source loc clock = some value.toBitVec64

private theorem select_path {entries : List Pair} {initial final : Option (MemoryMsg F)} {content : Option (BitVec 64)}
    {query : Nat → Word F → Prop} (history : CutHistory entries initial final content query) :
    ∃ path, path.Perm entries ∧ FrontierPath path initial final content ∧
      ∀ clock value, query clock value → content.map (fun seed => heldAt seed clock (path.map ofRecords)) = some value.toBitVec64 := by
  rcases history with ⟨start,stop,rfl,absent⟩ | ⟨first,last,path,start,stop,seed,all,walk,order,serves⟩
  · exact ⟨[],List.Perm.refl _,Or.inl ⟨start,stop,rfl⟩,fun clock value found => (absent clock value found).elim⟩
  · refine ⟨path,all,Or.inr ⟨first,last,start,stop,seed,walk,order⟩,?_⟩
    intro clock value q
    rw [seed,Option.map_some,serves clock value q]

/-- Raw native acceptance selects a complete family of physical Memory histories once,
before any WRITE call, guest byte, or register is chosen. -/
theorem native_realized_memory (w : EnsembleWitness (assembly image source target final)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) : ∃ paths, RealizedMemoryReplay w paths := by
  obtain ⟨aligned,paired,all⟩ := native_cut_histories w ok fit raw
  choose paths spec using (fun loc => select_path (all loc))
  exact ⟨paths,aligned,paired,spec⟩

private theorem read_query {tables : WriteProbe.AccessInventory.Source → Table F} {read : WriteProbe.Read F}
    (seen : WriteProbe.ReadMeaning tables read) : QueryAt tables (keyLocation read.key) (Address.toNat read.clock) read.value := by
  obtain ⟨r,⟨id,original⟩,key,value,_,_,after,before⟩ := seen
  exact ⟨id,r,original,congrArg keyLocation key.symm,after,before,value.symm⟩

/-- Each original probe returns the value of its shared realized-source replay at its own
decoded location and exact incoming clock. This applies to both register and RAM reads. -/
theorem RealizedMemoryReplay.read {w : EnsembleWitness (assembly image source target final)} {paths : MemoryPaths}
    (replay : RealizedMemoryReplay w paths) {r : WriteProbe.Read F}
    (found : WriteProbe.ReadMeaning (rawSource ((appended image source target final).project (observed w))) r) :
    paths.wordAt source (keyLocation r.key) (Address.toNat r.clock) = some r.value.toBitVec64 := by
  obtain ⟨_,_,all⟩ := replay
  exact (all _).2.2 _ _ (read_query found)

private theorem ram_key (s : WriteBuffer.Step F) (step : s.Valid) (valid : WriteProbe.ValidKey (Address.toNat s.read.key)) :
    keyLocation s.read.key = .ram (BitVec.ofNat 61 (Address.toNat s.read.key / 8)) := by
  have aligned := step.2.2.2.1
  have lower : 2^16 ≤ Address.toNat s.read.key := by rcases valid with x12 | ram <;> omega
  have notReg : ¬(s.read.key[0].val < 32 ∧ s.read.key[1] = 0 ∧ s.read.key[2] = 0) := by
    rintro ⟨small,one,two⟩
    simp [Address.toNat,one,two] at lower
    omega
  exact ite_eq_right (α := MemLoc) notReg

/-- A source-backed byte from a real WRITE is exactly the byte in the replay at its
guest address and incoming CPU clock, including both ends of a partial aligned word. -/
theorem RealizedMemoryReplay.guest_byte {w : EnsembleWitness (native image source target)} {paths : MemoryPaths}
    (replay : RealizedMemoryReplay w paths) {d : Dispatch F} {i : Nat} {byte : BitVec 8} (guest : GuestByteAt w d i byte) :
    paths.byteAt source (Address.toNat d.request.header.clock) (d.request.header.address.toNat + i) = some byte := by
  obtain ⟨s,step,read,clock,lane,address,octet⟩ := guest
  have word := replay.read read
  obtain ⟨_,_,_,_,key,_⟩ := read
  rw [ram_key s step key,clock] at word
  have aligned := step.2.2.2.1
  have laneBound := lane.isLt
  have cell : (d.request.header.address.toNat + i) / 8 = Address.toNat s.read.key / 8 := by omega
  have index : (d.request.header.address.toNat + i) % 8 = lane.val := by omega
  rw [MemoryPaths.byteAt,cell,index,word,Option.map_some,octet]

end SP1Clean.Export.WriteObservationAssembly
