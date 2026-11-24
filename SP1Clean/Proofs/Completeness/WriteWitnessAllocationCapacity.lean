import SP1Clean.Proofs.Completeness.WriteWitnessInputs
import SP1Clean.Proofs.Completeness.HistoricalHintCapacity

/-! # Historical capacity of the allocation word table over the whole tape

Each allocating WRITE pays for its own exact padded words by the increase of its persistent
store. An ordinary event or queue pop cannot erase those words. Thus collecting every WRITE
at once fits the same historical bound as the final store, even when buffers repeat.
-/

namespace SP1Clean.WriteEffects.Witness
open Semantics Machine FormalModel.Shard TraceGen WriteAllocation HintQueue

private def total (r : BatchRows) := (r.nodes.flatMap NodeRows.words).length

private theorem total_rows (b : Batch) (prior clock : Nat) (before : Store × Nat) (readers : Readers) :
    total (b.rows prior clock before readers) = (b.buffers.map wordCount).sum := by
  let nodes := b.steps clock before.1 before.2 readers.nodes
  have same : (nodes.zip b.buffers.reverse).map Prod.snd = b.buffers.reverse :=
    List.map_snd_zip (by simp [nodes,Batch.steps,HintNodeAllocate.compilePrepend_length])
  have mapped : (b.rows prior clock before readers).nodes = (nodes.zip b.buffers.reverse).map (fun x => nodeRows readers x.1 x.2) := List.map_uncurry_zip_eq_zipWith.symm
  rw [total,mapped,List.length_flatMap,List.map_map]
  change ((nodes.zip b.buffers.reverse).map (fun x => (nodeRows readers x.1 x.2).words.length)).sum = _
  simp only [nodeRows,Words.walk_length]
  change ((nodes.zip b.buffers.reverse).map (wordCount ∘ Prod.snd)).sum = _
  rw [← List.map_map,same,List.map_reverse,List.sum_reverse]

private theorem advance_mono {before after : Store × Nat} {src dst : HostState} {e : ExecutionEvent}
    (advanced : advance? src dst before e = some after) : storedWordCount before.1 ≤ storedWordCount after.1 := by
  cases e with
  | ordinary => cases Option.some.inj advanced; rfl
  | syscall call =>
    unfold advance? at advanced
    obtain ⟨kind,_,applied⟩ := Option.bind_eq_some_iff.mp advanced
    cases mode : src.hintUpdate kind dst with
    | pop =>
      rw [mode] at applied
      obtain ⟨_,_,rfl⟩ := Option.map_eq_some_iff.mp applied
      rfl
    | prepend hints =>
      rw [mode] at applied
      cases Option.some.inj applied
      simp [storedWordCount,prepend_bytes]

private theorem word_growth {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {i : Nat} {e : ExecutionEvent} (present : events[i]? = some e) {before after : Store × Nat}
    (pre : storeAfter? (policy SP1Prime image) image.program source.realize (events.take i) (ofList source.host.io.hints) = some before)
    (post : storeAfter? (policy SP1Prime image) image.program source.realize (events.take (i+1)) (ofList source.host.io.hints) = some after) :
    storedWordCount before.1 + (((position image source events readers e i).bind Entry.allocation).map total).getD 0 ≤
      storedWordCount after.1 := by
  cases found : (position image source events readers e i).bind Entry.allocation with
  | none =>
    simp only [Option.map_none,Option.getD_none,Nat.add_zero]
    obtain ⟨current,cursor,_,path,built,_⟩ := admissibleExecution_hintInventory run i
    cases Option.some.inj (pre.symm.trans built)
    obtain ⟨inside,event⟩ := List.getElem?_eq_some_iff.mp present
    rw [List.take_succ_eq_append_getElem inside,event,storeAfter_append path,pre,Option.bind_some] at post
    change ((replayStep? _ _ current e).bind (fun next => (advance? current.host next.host before e).bind (fun a => some a))) = _ at post
    obtain ⟨_,_,left⟩ := Option.bind_eq_some_iff.mp post
    obtain ⟨q,actual,same⟩ := Option.bind_eq_some_iff.mp left
    cases Option.some.inj same
    exact advance_mono actual
  | some rows =>
    simp only [Option.map_some,Option.getD_some]
    obtain ⟨entry,emitted,alloc⟩ := Option.bind_eq_some_iff.mp found
    have active := (native_position_active run readers present).1
    rw [emitted] at active
    cases e with
    | ordinary => contradiction
    | syscall call =>
      have write : call.rawCode = SyscallKind.write.code := of_decide_eq_true active.symm
      obtain ⟨_,_,_,_,_,_,_,_,_,sameBefore,sameAfter,_,sameEntry,_,_,_,batchAt,eligible⟩ := native_position run readers present write
      cases Option.some.inj (pre.symm.trans sameBefore)
      cases Option.some.inj (post.symm.trans sameAfter)
      cases Option.some.inj (emitted.symm.trans sameEntry)
      rw [batchAt,Option.map_eq_some_iff] at alloc
      obtain ⟨b,selected,rfl⟩ := alloc
      rw [total_rows,(eligible b selected).stored]
      simp [storedWordCount,prepend_bytes]

private theorem sum_inputs {A : Type} (f : A → Option Entry) (xs : List A) :
    (inputs (xs.filterMap f)).words.length =
      (xs.map (fun x => (((f x).bind Entry.allocation).map total).getD 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases emitted : f x with
    | none => simpa [emitted] using ih
    | some ent =>
      cases alloc : ent.allocation with
      | none => simpa [inputs,emitted,alloc] using ih
      | some b => simpa [inputs,total,emitted,alloc,List.flatMap_append] using congrArg ((b.nodes.flatMap NodeRows.words).length + ·) ih

/-- Every collected allocation word is paid by the same final persistent store. A pop
retains its historical record and cannot erase a charge from earlier in the tape. -/
theorem words_le_stored {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries)
    {last : Store × Nat} (finalStore : storeAfter? (policy SP1Prime image) image.program source.realize events (ofList source.host.io.hints) = some last) :
    (inputs entries).words.length ≤ storedWordCount last.1 := by
  let f := fun x : ExecutionEvent × Nat => position image source events readers x.1 x.2
  let cost := fun x => (((f x).bind Entry.allocation).map total).getD 0
  have charge (i : Nat) (small : i ≤ events.length) (cur : Store × Nat)
      (reached : storeAfter? (policy SP1Prime image) image.program source.realize (events.take i)
        (ofList source.host.io.hints) = some cur) :
      ((events.zipIdx.take i).map cost).sum ≤ storedWordCount cur.1 := by
    induction i generalizing cur with
    | zero => simp
    | succ i ih =>
      have inside : i < events.length := by omega
      obtain ⟨_,before,_,_,pre,_⟩ := admissibleExecution_hintInventory run i
      have prior := ih (by omega) before pre
      have indexed : events.zipIdx[i]? = some (events[i],i) := by simp [List.getElem?_zipIdx,List.getElem?_eq_getElem inside]
      obtain ⟨within,atIndex⟩ := List.getElem?_eq_some_iff.mp indexed
      rw [List.take_succ_eq_append_getElem within,atIndex,List.map_append,List.sum_append]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
      have delta := word_growth run readers (List.getElem?_eq_getElem inside) pre reached
      exact (Nat.add_le_add_right prior _).trans delta
  have totalPaid := charge events.length (le_refl _) last (by simpa only [List.take_length] using finalStore)
  obtain ⟨actual,built,ordered,_⟩ := native_inputs run readers
  cases Option.some.inj (collected.symm.trans built)
  rw [ordered,sum_inputs]
  have full : events.zipIdx.take events.length = events.zipIdx := List.take_of_length_le (by simp)
  rw [full] at totalPaid
  exact totalPaid

/-- The original semantic boundary and cumulative writes pay for the complete word inputs of
the native collector, before their single demand padding. This applies unchanged to tighter
semantic resource presets on the same domain. -/
theorem word_charge {lim : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution lim SP1Prime image source target events) (limits : lim.LE (.native SP1Prime)) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries) :
    8 * (inputs entries).words.length + 125 ≤ lim.boundaryBytes + lim.writeBytes := by
  obtain ⟨final,built,_⟩ := storeAfter_of_path run.1.2 (ofList_wellFormed _) (ofList_represents _)
  have available := (historical_hint_budget run.1.2 built run.2.2.2.1 run.2.2.1).2
  have used := words_le_stored (run.mono limits) readers collected built
  omega

/-- At native limits all words of the shared collector together fit in 2^29 rows. -/
theorem native_word_capacity {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries) :
    (inputs entries).words.length ≤ 2^29 := by
  have charged := word_charge run (ResourceLimits.LE.refl _) readers collected
  change 8 * (inputs entries).words.length + 125 ≤ (SP1Prime-1) + (SP1Prime-1) at charged
  have bound : SP1Prime < 2^31 := by decide
  omega

private theorem nonempty_words_at {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {i : Nat} {e : ExecutionEvent} (present : events[i]? = some e) {batch : BatchRows}
    (found : (position image source events readers e i).bind Entry.allocation = some batch)
    {node : NodeRows} (member : node ∈ batch.nodes) : 0 < node.words.length := by
  obtain ⟨entry,emitted,alloc⟩ := Option.bind_eq_some_iff.mp found
  have active := (native_position_active run readers present).1
  rw [emitted] at active
  cases e with
  | ordinary => contradiction
  | syscall call =>
    have write : call.rawCode = SyscallKind.write.code := of_decide_eq_true active.symm
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,same,_,_,_,batches,_⟩ := native_position run readers present write
    cases Option.some.inj (emitted.symm.trans same)
    rw [batches,Option.map_eq_some_iff] at alloc
    obtain ⟨b,_,rfl⟩ := alloc
    obtain ⟨k,atRow⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨step,bytes,_,_,rfl⟩ := List.getElem?_zipWith_eq_some.mp atRow
    simp only [nodeRows,Words.walk_length]
    exact Nat.zero_lt_succ _

/-- Every physically collected node seeds at least one word, including the mandatory empty
word. The node and seed counts therefore fit the same historical bound as the word table. -/
theorem native_node_count {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries) :
    (inputs entries).nodes.length ≤ (inputs entries).words.length := by
  obtain ⟨actual,built,ordered,_⟩ := native_inputs run readers
  cases Option.some.inj (collected.symm.trans built)
  let nodes := (entries.filterMap Entry.allocation).flatMap BatchRows.nodes
  have live : ∀ n ∈ nodes, 0 < n.words.length := by
    intro n inside
    obtain ⟨batch,inQueue,member⟩ := List.mem_flatMap.mp inside
    obtain ⟨entry,inTape,alloc⟩ := List.mem_filterMap.mp inQueue
    rw [ordered] at inTape
    obtain ⟨⟨e,i⟩,indexed,observed⟩ := List.mem_filterMap.mp inTape
    exact nonempty_words_at run readers (List.mk_mem_zipIdx_iff_getElem?.mp indexed)
      (Option.bind_eq_some_iff.mpr ⟨entry,observed,alloc⟩) member
  have count (ns : List NodeRows) (hasWord : ∀ n ∈ ns, 0 < n.words.length) :
      ns.length ≤ (ns.flatMap NodeRows.words).length := by
    induction ns with
    | nil => rfl
    | cons h t ih =>
      have head := hasWord h List.mem_cons_self
      have tail := ih (fun n m => hasWord n (List.mem_cons_of_mem _ m))
      simp only [List.length_cons,List.flatMap_cons,List.length_append]
      omega
  simpa only [inputs,List.length_map,nodes] using count nodes live

end SP1Clean.WriteEffects.Witness
