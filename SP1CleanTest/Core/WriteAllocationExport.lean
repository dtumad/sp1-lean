import SP1Clean.Proofs.Completeness.WriteAllocationBatch
import SP1Clean.Proofs.Completeness.WriteAllocationWordTables
import SP1Clean.Proofs.Completeness.Providers
import SP1Clean.Native.Operations.WriteStreamSource
import SP1CleanTest.Core.ComponentExport
import ToClean.Circuit.VerifierInteractions
import Clean.Air.WitnessGeneration

/-! # Production WRITE allocation tables under Clean's built-in scheduler

Three calls allocate a private guest buffer, return multiple public hook buffers, and return no
buffers. The boundary requests every immutable node and padded word independently from the
private candidate rows. Public hook metadata and aligned returned blocks use their real fixed
providers. Only the initial and final queue states span the complete sequence.
-/

namespace SP1CleanTest.Core.WriteAllocationExport
open Circuit Air.Flat SP1Clean Semantics Semantics.HintQueue WriteAllocation WriteEffects
open ComponentExport (Fp)

private def guest : Bytes := [16,32,48,64,80,96,112,128,144]
private def aligned : Bytes := [1,2,3,4,5,6,7,8]
private def returned : List Bytes := [[],aligned,[254,253,252]]
private def source : HostState := { replies := [⟨⟨15,[17]⟩,returned⟩,⟨⟨15,[]⟩,[]⟩] }
private def target : HostState := {}

/-- The actual previous store and head are threaded between all three calls. -/
private def calls : List (Batch × Nat × Nat × Store × Nat) :=
  let first := prepend #[] 0 [guest]
  let second := prepend first.1 first.2 returned
  [(.direct guest,1,257,#[],0),(.hook 0 1 returned,257,265,first.1,first.2),(.hook 1 0 [],265,273,second.1,second.2)]

private def opens : List (Open Fp) := calls.map (fun (b,prior,clk,store,head) => b.openRow prior clk store head)
private def paired : List (Step Fp × Bytes) := calls.flatMap fun (b,_,clk,store,head) =>
  (b.steps clk store head (fun _ => 1)).zip b.buffers.reverse
private def words : List (Words.Row Fp) := paired.flatMap fun (r,bytes) =>
  Words.walk r.contents bytes (fun _ => 1) (fun _ => 1)
private def finalStore : Store := (prepend (prepend #[] 0 [guest]).1 1 returned).1

private def verifier : Verifier.Program Fp HostHintQueue.State where
  Spec _ _ := True
  soundness := by intros; trivial
  main outgoing := do
    Verifier.push HostHintQueue.stateChannel (const (HostHintQueue.State.encode 1 0 0))
    Verifier.pull HostHintQueue.stateChannel outgoing
    for (b,_,clk,store,_) in calls do
      Verifier.push queueEffectChannel (const (b.ticket clk store.size))
    for (node,i) in finalStore.toList.zipIdx do
      Verifier.pull HostHintQueue.nodeChannel (const (NodeRecord.encode (i+1) node))
      for w in List.range (wordCount node.bytes) do
        Verifier.pull HostHintQueue.wordChannel (const (WordRecord.encode (i+1) node.bytes w))
    for i in List.range (blockCount guest) do
      let block : StreamBlock Fp :=
        ⟨14,Address.ofNat 1,0,Address.ofNat i,Words.extent guest i,(wordBytes guest i).map (fun b => (b.toNat : Fp))⟩
      Verifier.pull blockChannel (const block)

private def registry : List (RawChannel Fp) :=
  [queueEffectChannel.toRaw,HostHintQueue.stateChannel.toRaw,WriteAllocation.cursorChannel.toRaw,
   HostHintQueue.nodeChannel.toRaw,contentsChannel.toRaw,recordChannel.toRaw,Words.cursorChannel.toRaw,
   blockChannel.toRaw,HostHintQueue.wordChannel.toRaw,Channels.byteChannel.toRaw]

private def components : List (Component Fp) :=
  [openComponent,stepComponent,Words.seedComponent,Words.wordComponent,streamComponent source target,
   blockComponent source target,RangeChip.componentFor 16]

private structure PrivateInput where
  cells : Array Fp := #[]
  views : List HintTable := []

private def pack {I : TypeMap} [ProvableType I] (name : String) (rows : List (List UInt64 × I Fp))
    (previous : PrivateInput) : Except String PrivateInput := do
  let packed ← Witgen.HintIndex.prepareKeys (Input := I) rows
  let cells := previous.cells ++ (packed.inputs.map (·.toArray)).flatten
  return ⟨cells ++ (packed.index.map (·.toArray)).flatten, previous.views ++
    [⟨name,size I,previous.cells.size,packed.inputs.size⟩,⟨name ++ ".index",1,cells.size,packed.index.size⟩]⟩

private def prepare : Except String PrivateInput := do
  let first ← pack (I := ProvablePair Open field) (openCircuit (p := SP1Prime)).name
    (opens.map fun r => ([UInt64.ofNat (Address.toNat r.ticket.clock)],(r,1))) {}
  let second ← pack (I := ProvablePair Step field) (stepCircuit (p := SP1Prime)).name (paired.map fun (r,_) =>
    ([UInt64.ofNat (r.before.state.clk_high.val * 2^24 + r.before.state.clk_low.val),
      UInt64.ofNat (Address.toNat r.before.remaining)],(r,1))) first
  let third ← pack (I := ProvablePair Contents field) (Words.seedCircuit (p := SP1Prime)).name (paired.map fun (r,_) =>
    ([UInt64.ofNat (Address.toNat r.contents.pointer)],(r.contents,1))) second
  pack (I := ProvablePair Words.Row field) (Words.wordCircuit (p := SP1Prime)).name (words.map fun r =>
    ([UInt64.ofNat (Address.toNat r.prior.contents.pointer),UInt64.ofNat (Address.toNat r.prior.index)],(r,1))) third

private def ensemble (privateInput : PrivateInput) : Ensemble Fp HostHintQueue.State where
  tables := components
  unique_names := by decide
  channels := registry
  unique_channel_names := by decide
  verifier := verifier
  tables_channels := by
    intro t mem
    simp only [components,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals intro ch member
    · change ch ∈ [queueEffectChannel.toRaw,HostHintQueue.stateChannel.toRaw,WriteAllocation.cursorChannel.toRaw,
        WriteAllocation.cursorChannel.toRaw,HostHintQueue.stateChannel.toRaw] at member
      simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      tauto
    · change ch ∈ [Channels.byteChannel.toRaw,WriteAllocation.cursorChannel.toRaw,recordChannel.toRaw,
        recordChannel.toRaw,HostHintQueue.nodeChannel.toRaw,contentsChannel.toRaw,WriteAllocation.cursorChannel.toRaw] at member
      simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      tauto
    · change ch ∈ [contentsChannel.toRaw,Words.cursorChannel.toRaw] at member
      simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      tauto
    · change ch ∈ [Words.cursorChannel.toRaw,blockChannel.toRaw,blockChannel.toRaw,
        HostHintQueue.wordChannel.toRaw,Words.cursorChannel.toRaw] at member
      simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      tauto
    · change ch ∈ [recordChannel.toRaw] at member
      simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      tauto
    · change ch ∈ [blockChannel.toRaw] at member
      simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      tauto
    · change ch ∈ [Channels.byteChannel.toRaw] at member
      simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      tauto
  verifier_channels := by
    intro ch mem
    rw [Verifier.Program.mem_channels_iff,Operations.channels] at mem
    change ch ∈ _ at mem
    simp only [registry,List.mem_cons,List.not_mem_nil,or_false]
    change ch ∈ [HostHintQueue.stateChannel.toRaw,HostHintQueue.stateChannel.toRaw,
      queueEffectChannel.toRaw,queueEffectChannel.toRaw,queueEffectChannel.toRaw,
      HostHintQueue.nodeChannel.toRaw,HostHintQueue.wordChannel.toRaw,HostHintQueue.wordChannel.toRaw,
      HostHintQueue.nodeChannel.toRaw,HostHintQueue.wordChannel.toRaw,
      HostHintQueue.nodeChannel.toRaw,HostHintQueue.wordChannel.toRaw,HostHintQueue.wordChannel.toRaw,
      HostHintQueue.nodeChannel.toRaw,HostHintQueue.wordChannel.toRaw,blockChannel.toRaw,blockChannel.toRaw] at mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    tauto
  ProverInput := fields privateInput.cells.size
  hintTables := privateInput.views

/-- Execute and export the same production tables and named demand indices. -/
def fixture : Except String (String × Lean.Json) := do
  let input ← prepare
  let program := ensemble input
  let boundary := HostHintQueue.State.encode (p := SP1Prime) 273 4 4
  match WitnessGeneration.generate program 2048 boundary ⟨input.cells,rfl⟩ with
  | .error message => throw (toString message)
  | .ok witness =>
    unless WitnessGeneration.constraintsHold witness && WitnessGeneration.channelsBalanced witness do
      throw "native queue allocation fixture failed the physical constraints or complete ledger"
    let rust ← Backends.Plonky3.Print.ensembleToRust (ComponentExport.fixture program) 2048
    let json := Lean.Json.mkObj [("private",Lean.toJson (input.cells.map (·.val))),
      ("public",Lean.toJson ((toElements boundary).toArray.map (·.val))),
      ("heights",Lean.toJson (witness.tables.map (·.table.length))),("witness",ComponentExport.physicalReference witness)]
    return (rust,json)

end SP1CleanTest.Core.WriteAllocationExport
