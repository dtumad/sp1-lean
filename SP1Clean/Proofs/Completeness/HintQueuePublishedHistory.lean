import SP1Clean.Proofs.Completeness.HintQueuePublicationRange
import SP1Clean.Semantics.Resources.HostReceiptResources

/-! # Exhaustive immutable publication history across a mixed execution

Consecutive allocation intervals meet exactly at the persistent frontier. The actual chronology collects every
fresh node and its padded words once, including buffers since popped from the public outgoing queue.
-/

namespace SP1Clean.WriteEffects.Witness
open Semantics Machine FormalModel.Shard TraceGen WriteAllocation HintQueue
private abbrev F := ZMod SP1Prime

private def sites : Option Entry → List NodeRows := fun e => (((e.bind Entry.allocation).map BatchRows.nodes).getD [])

private theorem sites_sum {α : Type} (xs : List α) (f : α → Option Entry) :
    xs.flatMap (fun x => sites (f x)) = (((xs.filterMap f).filterMap Entry.allocation).flatMap BatchRows.nodes) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons,ih,List.filterMap_cons]
    cases h : f x with
    | none => rfl
    | some e => cases a : e.allocation <;> simp [sites,a]

private theorem nonwrite_size {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {e : ExecutionEvent} {cut : Nat} (present : events[cut]? = some e) (safe : HostFrameSafe e) {before after : Store × Nat}
    (pre : storeAfter? (policy SP1Prime image) image.program source.realize (events.take cut) (ofList source.host.io.hints) = some before)
    (post : storeAfter? (policy SP1Prime image) image.program source.realize (events.take (cut+1)) (ofList source.host.io.hints) = some after) :
    after.1.size = before.1.size := by
  obtain ⟨current,_,_,path,got,_,size,_⟩ := admissibleExecution_hintInventory run cut
  obtain ⟨_,_,_,_,got',_,size',_⟩ := admissibleExecution_hintInventory run (cut+1)
  cases Option.some.inj (pre.symm.trans got)
  cases Option.some.inj (post.symm.trans got')
  obtain ⟨other,next,reached,step⟩ := run.1.2.step_at present
  have eq : current = other := Option.some.inj (path.replay.symm.trans reached)
  subst other
  obtain ⟨inside,found⟩ := List.getElem?_eq_some_iff.mp present
  obtain ⟨_,_,_,zero,_⟩ := HostReceiptProfile.step_cost step safe
  rw [List.take_succ_eq_append_getElem inside,found,path.resources_append [e]] at size'
  simp only [executionResources_cons step,executionResources_nil,ResourceUsage.combine,ResourceKind.cumulative,
    ite_true,ExecutionState.resources,ResourceUsage.zero,zero,Nat.add_zero] at size'
  exact size'.trans size.symm

private theorem step_publications {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {e : ExecutionEvent} {cut : Nat} (present : events[cut]? = some e) {before after final : Store × Nat}
    (pre : storeAfter? (policy SP1Prime image) image.program source.realize (events.take cut) (ofList source.host.io.hints) = some before)
    (post : storeAfter? (policy SP1Prime image) image.program source.realize (events.take (cut+1)) (ofList source.host.io.hints) = some after)
    (finish : storeAfter? (policy SP1Prime image) image.program source.realize events (ofList source.host.io.hints) = some final) :
    let physical := sites (position image source events readers e cut)
    after.1.size = before.1.size + physical.length ∧
      physical.map publication = (List.range' before.1.size physical.length).map (storedPublication readers final.1) := by
  dsimp only
  by_cases yes : WriteObservations.isWriteCall e
  · cases e with
    | ordinary => contradiction
    | syscall call =>
      have write : call.rawCode = SyscallKind.write.code := by simpa only [WriteObservations.isWriteCall,decide_eq_true_eq] using yes
      obtain ⟨current,_,cursor,after',len,buf,entry,reached,_,stored,afterStore,read,emitted,_,_,_,rows,allowed⟩ := native_position run readers present write
      cases Option.some.inj (pre.symm.trans stored)
      cases Option.some.inj (post.symm.trans afterStore)
      obtain ⟨current',_,l,b,c,d,same,_,sameRead,incoming,outgoing,rep,_,newStore,_⟩ := native_store_at run present write
      cases Option.some.inj (reached.symm.trans same)
      cases Option.some.inj (pre.symm.trans incoming)
      cases Option.some.inj (post.symm.trans outgoing)
      cases Option.some.inj (read.symm.trans sameRead)
      let route := WriteRoute.ofDescriptor call.arg1
      let bytes := WriteObservations.payload buf call.arg2.toNat len.toNat
      let prior := (events.take cut).foldl advanceQueueClock 0
      let earlier := WriteStreams.fromEndpoints source.host current.host
      let batch := batchFor route earlier current.host bytes
      change entry.allocation = batch.map _ at rows
      simp only [emitted,sites,Option.bind_some,rows]
      cases active : batch with
      | none =>
        have noBuffers : route.allocations current.host bytes = [] := by
          cases routeEq : route <;> simp [batch,batchFor,batchAt,routeEq,WriteRoute.allocations] at active ⊢
        change after = prepend before.1 before.2 (route.allocations current.host bytes) at newStore
        simp only [noBuffers,prepend] at newStore
        simp [newStore]
      | some b =>
        have good := allowed b active
        have suffix := batch_publications b prior current.clock before.1 before.2 current.host.io.hints rep good.capacity.1 good.capacity.2 readers final.1
        obtain ⟨_,_,_,_,actual,_,_,_,_,_,complete,extendsAfter,_⟩ := admissibleExecution_hintInventory run (cut+1)
        cases Option.some.inj (post.symm.trans actual)
        cases Option.some.inj (finish.symm.trans complete)
        have keep : Extends (prepend before.1 before.2 b.buffers).1 final.1 := good.stored ▸ extendsAfter
        simp only [Option.map_some,Option.getD_some,Batch.rows_length]
        exact ⟨congrArg (fun q : Store × Nat => q.1.size) good.stored |>.trans (prepend_size ..),suffix keep⟩
  · have empty := (native_position_active run readers present).1
    have no : position image source events readers e cut = none := by simpa [yes] using empty
    have safe : HostFrameSafe e := by
      cases e with
      | ordinary => trivial
      | syscall call => simpa [HostFrameSafe,WriteObservations.isWriteCall] using yes
    rw [no]
    exact ⟨nonwrite_size run present safe pre post,rfl⟩

/-- Chronological physical nodes and words, including their carried reader columns, are exactly the original
post-source pointer interval of the final store. This includes every allocation made before an intervening pop. -/
theorem native_publication_range {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries) {final : Store × Nat}
    (finish : storeAfter? (policy SP1Prime image) image.program source.realize events (ofList source.host.io.hints) = some final) :
    let initial := (ofList source.host.io.hints).1.size
    (((entries.filterMap Entry.allocation).flatMap BatchRows.nodes).map publication) =
      (List.range' initial (final.1.size - initial)).map (storedPublication readers final.1) := by
  intro initial
  let inspect := fun x : ExecutionEvent × Nat => position image source events readers x.1 x.2
  have earlier (i : Nat) (bound : i ≤ events.length) (q : Store × Nat)
      (pre : storeAfter? (policy SP1Prime image) image.program source.realize (events.take i) (ofList source.host.io.hints) = some q) :
      let got := (events.zipIdx.take i).flatMap (fun x => sites (inspect x))
      q.1.size = initial + got.length ∧ got.map publication =
        (List.range' initial got.length).map (storedPublication readers final.1) := by
    induction i generalizing q with
    | zero =>
      cases Option.some.inj pre
      simp [initial]
    | succ i ih =>
      have inside : i < events.length := by omega
      obtain ⟨_,before,_,_,reached,_⟩ := admissibleExecution_hintInventory run i
      obtain ⟨len,prior⟩ := ih (by omega) before reached
      obtain ⟨extra,put⟩ := step_publications run readers (List.getElem?_eq_getElem inside) reached pre finish
      have located : events.zipIdx[i]? = some (events[i],i) := by simp [List.getElem?_zipIdx,List.getElem?_eq_getElem inside]
      obtain ⟨here,index⟩ := List.getElem?_eq_some_iff.mp located
      rw [List.take_succ_eq_append_getElem here,index,List.flatMap_append]
      simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,List.map_append]
      refine ⟨?_,?_⟩
      · rw [extra,len,Nat.add_assoc]
      · rw [prior,put,len,← List.map_append,List.range'_append_1]
  obtain ⟨actual,emitted,ordered,_⟩ := native_inputs run readers
  cases Option.some.inj (collected.symm.trans emitted)
  obtain ⟨length,equal⟩ := earlier events.length (le_refl _) final (by simpa only [List.take_length] using finish)
  have whole : events.zipIdx.take events.length = events.zipIdx := List.take_of_length_le (by simp)
  rw [whole,sites_sum] at length equal
  rw [ordered,show final.1.size - initial = (((events.zipIdx.filterMap inspect).filterMap Entry.allocation).flatMap BatchRows.nodes).length by omega]
  exact equal

end SP1Clean.WriteEffects.Witness
