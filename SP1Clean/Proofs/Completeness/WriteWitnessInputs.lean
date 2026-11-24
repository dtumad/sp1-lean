import SP1Clean.Proofs.Completeness.WriteWitnessPosition

/-! # Physical input batches of the chronological WRITE compiler

The same ordered WRITE entries feed all four allocation components. A node authorizes its
own contents seed and contributes each of its padded word positions to the word table.
-/

namespace SP1Clean.WriteEffects.Witness

open Semantics Machine FormalModel.Shard TraceGen WriteAllocation HintQueue
private abbrev F := ZMod SP1Prime

/-- Ordered, unpadded inputs consumed by the packet, dispatch and four allocator components. -/
structure Inputs where
  /-- Original register and guest-memory observations in WRITE order. -/
  packets : List WriteObservations.Packet
  /-- One dispatcher per observed WRITE. -/
  dispatches : List (Dispatch F)
  /-- One open row per allocating WRITE, including empty replies. -/
  openings : List (Open F)
  /-- All fresh nodes in their physical prepend order. -/
  nodes : List (Step F)
  /-- The seed emitted by every fresh physical node. -/
  contents : List (Contents F)
  /-- Every padded word of each seed in consecutive index order. -/
  words : List (Words.Row F)

/-- Materialize the table inputs from the already collected WRITE entries. -/
def inputs (entries : List Entry) : Inputs :=
  let batches := entries.filterMap Entry.allocation
  let nodes := batches.flatMap BatchRows.nodes
  ⟨entries.map Entry.packet,entries.map Entry.dispatch,batches.map BatchRows.opening,
    nodes.map NodeRows.step,nodes.map (fun n => n.step.contents),nodes.flatMap NodeRows.words⟩

/-- The node and seed inventories agree occurrence by occurrence, including duplicate contents. -/
theorem inputs_seeds (entries : List Entry) :
    (inputs entries).contents = (inputs entries).nodes.map Step.contents := by
  simp only [inputs,List.map_map,Function.comp_def]

/-- All local row contracts of one observed WRITE, including its optional allocation. -/
def Entry.Valid (e : Entry) : Prop :=
  e.dispatch.Valid ∧ ∀ batch ∈ e.allocation, batch.opening.Valid ∧
    ∀ node ∈ batch.nodes, node.step.Valid ∧ ∀ word ∈ node.words, word.Valid

private theorem valid_at {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {event : ExecutionEvent} {cut : Nat} (present : events[cut]? = some event) {entry : Entry}
    (emitted : position image source events readers event cut = some entry) : entry.Valid := by
  have actual := (native_position_active run readers present).1
  rw [emitted] at actual
  cases event with
  | ordinary => contradiction
  | syscall call =>
    have write : call.rawCode = SyscallKind.write.code := of_decide_eq_true actual.symm
    obtain ⟨_,_,cursor,after,_,_,same,_,_,_,_,_,owned,_,_,dispatch,allocates,active⟩ := native_position run readers present write
    cases Option.some.inj (emitted.symm.trans owned)
    refine ⟨dispatch, ?_⟩
    intro batch used
    change entry.allocation = some batch at used
    rw [allocates,Option.map_eq_some_iff] at used
    obtain ⟨sourceBatch,selected,rfl⟩ := used
    have certified := active sourceBatch selected
    exact ⟨certified.valid, sourceBatch.rows_valid _ _ cursor after.1 certified.publishes readers certified.capacity.1 certified.capacity.2⟩

/-- Local validity of every emitted physical row, with the exact seed authorization list.
The seed circuit accepts each authorized contents value directly. -/
structure Inputs.Valid (physical : Inputs) : Prop where
  /-- Valid compiled dispatchers at all actual write positions. -/
  dispatches : ∀ r ∈ physical.dispatches, r.Valid
  /-- All allocating calls provide checked queue transitions. -/
  openings : ∀ r ∈ physical.openings, r.Valid
  /-- All fresh nodes provide their own checked predecessor/successor rows. -/
  nodes : ∀ r ∈ physical.nodes, r.Valid
  /-- Each step authorizes its exact seed at the matching physical position. -/
  seeds : physical.contents = physical.nodes.map Step.contents
  /-- Every real and padded byte lane belongs to a valid compiled word row. -/
  words : ∀ r ∈ physical.words, r.Valid

private theorem inputs_valid (entries : List Entry) (checked : ∀ e ∈ entries, e.Valid) : (inputs entries).Valid := by
  have batches (b : BatchRows) (found : b ∈ entries.filterMap Entry.allocation) :
      b.opening.Valid ∧ ∀ node ∈ b.nodes, node.step.Valid ∧ ∀ word ∈ node.words, word.Valid := by
    obtain ⟨e,member,allocated⟩ := List.mem_filterMap.mp found
    exact (checked e member).2 b allocated
  have nodes (node : NodeRows) (found : node ∈ (entries.filterMap Entry.allocation).flatMap BatchRows.nodes) :
      node.step.Valid ∧ ∀ r ∈ node.words, r.Valid := by
    obtain ⟨b,member,used⟩ := List.mem_flatMap.mp found
    exact (batches b member).2 node used
  refine ⟨?_,?_,?_,inputs_seeds entries,?_⟩
  · intro r used
    obtain ⟨e,member,rfl⟩ := List.mem_map.mp used
    exact (checked e member).1
  · intro r used
    obtain ⟨b,member,rfl⟩ := List.mem_map.mp used
    exact (batches b member).1
  · intro r used
    obtain ⟨node,member,rfl⟩ := List.mem_map.mp used
    exact (nodes node member).1
  · intro r used
    obtain ⟨node,member,word⟩ := List.mem_flatMap.mp used
    exact (nodes node member).2 r word

/-- The allocating WRITEs in the original CPU tape, including hooks with no returned nodes. -/
def opensQueue : ExecutionEvent → Bool
  | .ordinary => false
  | .syscall call => WriteObservations.isWriteCall (.syscall call) && usesQueue call

private theorem opens_at {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {e : ExecutionEvent} {i : Nat} (present : events[i]? = some e) :
    ((position image source events readers e i).bind Entry.allocation).isSome = opensQueue e := by
  cases e with
  | ordinary =>
    have absent := (native_position_active run readers present).1
    cases built : position image source events readers .ordinary i <;> simp [built,WriteObservations.isWriteCall] at absent ⊢
    rfl
  | syscall call =>
    by_cases write : call.rawCode = SyscallKind.write.code
    · obtain ⟨_,_,_,_,_,_,entry,_,_,_,_,_,emitted,_,_,_,allocated,_⟩ := native_position run readers present write
      rw [emitted,Option.bind_some,allocated]
      cases route : WriteRoute.ofDescriptor call.arg1 <;>
        simp [opensQueue,WriteObservations.isWriteCall,usesQueue,write,route,batchFor,SyscallKind.code]
    · have absent := (native_position_active run readers present).1
      cases built : position image source events readers (.syscall call) i <;>
        simp [built,opensQueue,WriteObservations.isWriteCall,write] at absent ⊢

private theorem openings_length {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers) :
    let entries := events.zipIdx.filterMap (fun (e,i) => position image source events readers e i)
    (inputs entries).openings.length = events.countP opensQueue := by
  dsimp only
  simp only [inputs,List.length_map,List.filterMap_filterMap,List.length_filterMap_eq_countP]
  calc
    _ = events.zipIdx.countP (opensQueue ∘ Prod.fst) := by
      apply List.countP_congr
      intro ⟨e,i⟩ used
      rw [opens_at run readers (List.mk_mem_zipIdx_iff_getElem?.mp used)]
      rfl
    _ = _ := by rw [← List.countP_map,List.zipIdx_map_fst]

/-- Every native mixed execution constructs all ordered table inputs in one chronological
collection. All six projections use the same observations and the seed matches every node. -/
theorem native_inputs {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers) :
    ∃ entries, native? image source events readers = some entries ∧
      entries = events.zipIdx.filterMap (fun (e,i) => position image source events readers e i) ∧
      WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some (inputs entries).packets ∧
      dispatchTape? image source.host source.clock source.realize (ofList source.host.io.hints) events = some (inputs entries).dispatches ∧
      (inputs entries).dispatches.length = events.countP WriteObservations.isWriteCall ∧
      (inputs entries).openings.length = events.countP opensQueue ∧ (inputs entries).Valid := by
  obtain ⟨built,packets⟩ := native_collect run readers
  have dispatched := dispatch_projection image source.host readers source.clock source.realize (ofList source.host.io.hints) events
  rw [← native?,built,Option.map_some] at dispatched
  have count := WriteObservations.packets_length packets
  refine ⟨_,built,rfl,packets,dispatched,?_,openings_length run readers,inputs_valid _ ?_⟩
  · simpa only [inputs,List.length_map] using count
  intro entry used
  obtain ⟨⟨e,i⟩,indexed,found⟩ := List.mem_filterMap.mp used
  exact valid_at run readers (List.mk_mem_zipIdx_iff_getElem?.mp indexed) found

end SP1Clean.WriteEffects.Witness
