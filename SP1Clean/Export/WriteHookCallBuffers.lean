import SP1Clean.Export.WriteAllocationCalls

/-! # Whole hook allocation batches matched to their actual dispatcher and public reply -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Semantics.HintQueue Soundness WriteAllocation WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot}

/-- Every actually allocating dispatcher owns a matching complete header-to-header node
walk, including the empty walk for a hook returning zero buffers. -/
theorem native_dispatch_batch (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (md : d ∈ allocatingDispatches (observed w)) :
    ∃ call ∈ (allocationInputs (observed w)).1, call.ticket = d.ticket d.flags ∧ ∃ rows,
      Walk.IsWalk (fun n : Step F => (n.before,n.after)) call.first call.last rows ∧
      rows.length = Address.toNat call.count ∧ ∀ n ∈ rows,n ∈ (allocationInputs (observed w)).2 := by
  obtain ⟨tickets,_⟩ := native_allocation_tickets w ok fit raw
  obtain ⟨call,mc,ticket⟩ := List.mem_map.mp (tickets.mem_iff.mp (List.mem_map_of_mem (f := fun d => d.ticket d.flags) md))
  obtain ⟨batches,paired,used⟩ := native_matched_allocations w ok fit raw
  have appears : call ∈ (((allocationInputs (observed w)).1).zip batches).map Prod.fst := by rw [List.map_fst_zip paired.length_eq.le]; exact mc
  obtain ⟨⟨call',batch⟩,both,e⟩ := List.mem_map.mp appears
  change call' = call at e
  subst call'
  obtain ⟨walk,count⟩ := (List.forall₂_iff_zip.mp paired).2 both
  exact ⟨call,mc,ticket,batch,walk,count,fun r m => used.mem_iff.mp (List.mem_flatten.mpr ⟨batch,(List.of_mem_zip both).2,m⟩)⟩

private theorem dispatch_hook_metadata {final : HostHintQueue.State F} (w : EnsembleWitness (assembly image source target final)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (md : d ∈ allocatingDispatches (observed w))
    (hook : d.flags.hook = 1) {record : Record F} (asked : record ∈ d.metadataReads) : record.Binds (.fromEndpoints source.host target.host) := by
  let seen := observed w
  have on := ((native_allocation_tickets w ok fit raw).2 d md).2
  obtain ⟨r,kept,same⟩ := List.mem_map.mp md
  obtain ⟨actual,gate⟩ := List.mem_filter.mp kept
  obtain ⟨row,member,found⟩ := List.mem_map.mp actual
  change r.1 = d at same
  subst d
  have enabled : r.2 = 1 := by
    have eq := of_decide_eq_true gate
    change r.2 * (r.1.flags.direct+r.1.flags.hook) = 1 at eq
    rwa [on,mul_one] at eq
  apply native_metadata_record w ok fit raw
  rw [allocation_metadata_ledger]
  let dslot : TableSlot (preprocessing image source target final).tables dispatchComponent := slot image source target final 8
  let t := dslot.table seen
  apply List.mem_flatMap.mpr
  refine ⟨t,List.mem_cons_of_mem _ List.mem_cons_self,List.mem_flatMap.mpr ⟨row,member,?_⟩⟩
  change _ ∈ (dslot.table seen).component.operations.interactionValuesWith recordChannel.toRaw (t.environment row)
  rw [dslot.table_component seen,dispatch_metadata_at]
  change recordChannel.pulledValue record ∈ (valueFromOffset (ProvablePair Dispatch field) 0 (t.environment row)).1.metadataReads.map _
  change valueFromOffset (ProvablePair Dispatch field) 0 (t.environment row) = r at found
  rw [found]
  apply List.mem_map.mpr
  exact ⟨record,asked,by rw [enabled,hook,one_mul]; rfl⟩

private theorem walk_sources {rows : List (Step F)} {start finish : WriteAllocation.Cursor F}
    (walk : Walk.IsWalk (fun n : Step F => (n.before,n.after)) start finish rows) (valid : ∀ n ∈ rows,n.Valid) :
    ∀ i : Fin rows.length, let r := rows[i.val]
      r.source = start.source ∧ Address.toNat r.index + (i.val+1) = Address.toNat start.remaining := by
  induction rows generalizing start with
  | nil => intro i; exact Fin.elim0 i
  | cons n ns ih =>
    obtain ⟨same,later⟩ := walk
    change n.before = start at same
    subst start
    have v := valid n List.mem_cons_self
    have one := v.2.2.2.2.2.2
    change Address.toNat n.remaining = Address.toNat n.index + Address.toNat (#v[1,0,0] : fields 3 F) at one
    rw [show Address.toNat (#v[1,0,0] : fields 3 F) = 1 by decide] at one
    rintro ⟨i,inside⟩
    cases i with
    | zero => exact ⟨rfl,one.symm⟩
    | succ i =>
      have hi : i < ns.length := Nat.lt_of_succ_lt_succ inside
      obtain ⟨origin,bound⟩ := ih later (fun r m => valid _ (List.mem_cons_of_mem _ m)) ⟨i,hi⟩
      change Address.toNat ns[i].index + (i+1) = Address.toNat n.index at bound
      exact ⟨origin,by change Address.toNat ns[i].index + (i+1+1) = Address.toNat n.remaining; omega⟩

/-- The endpoint reply assigned to an actual hook call has exactly its dispatched number
of buffers. The authenticated descriptor and input length come from that same reply. -/
theorem native_hook_reply (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (md : d ∈ allocatingDispatches (observed w))
    (hook : d.flags.hook = 1) :
    ∃ reply, (WriteStreams.fromEndpoints source.host target.host).hooks[Address.toNat d.previous.replies]? = some reply ∧
      reply.hints.length = Address.toNat d.returned ∧ reply.request.descriptor.toNat = d.request.route.val ∧
      reply.request.input.length = Address.toNat d.length := by
  let s := WriteStreams.fromEndpoints source.host target.host
  have count := (dispatch_hook_metadata w ok fit raw d md hook (record := d.metadata 3 d.returned)
    (by simp [Dispatch.metadataReads])).lookup
  have desc := (dispatch_hook_metadata w ok fit raw d md hook (record := d.metadata 2 #v[d.request.route,0,0])
    (by simp [Dispatch.metadataReads])).lookup
  have size := (dispatch_hook_metadata w ok fit raw d md hook (record := d.metadata 0 d.length)
    (by simp [Dispatch.metadataReads])).lookup
  have k3 : (d.metadata 3 d.returned).query? = some (.returnCount (Address.toNat d.previous.replies)) := by
    simp only [Dispatch.metadata,Record.query?,show (3 : F).val = 3 by decide]; rfl
  have k2 : (d.metadata 2 #v[d.request.route,0,0]).query? = some (.descriptor (Address.toNat d.previous.replies)) := by
    simp only [Dispatch.metadata,Record.query?,show (3 : F).val = 3 by decide,show (2 : F).val = 2 by decide]; rfl
  have k0 : (d.metadata 0 d.length).query? = some (.length (.request (Address.toNat d.previous.replies))) := by
    simp only [Dispatch.metadata,Record.query?,show (3 : F).val = 3 by decide,ZMod.val_zero]; rfl
  rw [k3,Option.bind_some] at count
  rw [k2,Option.bind_some] at desc
  rw [k0,Option.bind_some] at size
  obtain ⟨reply,found,number⟩ := Option.map_eq_some_iff.mp count
  change s.hooks[Address.toNat d.previous.replies]? = some reply at found
  change (s.hooks[Address.toNat d.previous.replies]?.map (·.request.descriptor.toNat)) = some _ at desc
  change ((s.hooks[Address.toNat d.previous.replies]?.map (·.request.input)).map List.length) = some _ at size
  rw [found,Option.map_some,Option.some.injEq] at desc
  rw [found,Option.map_some,Option.map_some,Option.some.injEq] at size
  exact ⟨reply,found,number,by simpa [Dispatch.metadata,Address.toNat,circuit_norm] using desc,size⟩

private theorem hook_count {d : Dispatch F} {c : Open F} (ticket : c.ticket = d.ticket d.flags)
    (hook : d.flags.hook = 1) (notDirect : d.flags.direct = 0) : c.count = d.returned := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [Open.count,ticket,Dispatch.ticket,hook,notDirect,threeLimbs,circuit_norm]

private theorem hook_node {d : Dispatch F} {c : Open F} {n : Step F}
    (ticket : c.ticket = d.ticket d.flags) (origin : n.source = c.source)
    (hook : d.flags.hook = 1) (notDirect : d.flags.direct = 0) :
    n.direct = 0 ∧ n.reply = d.previous.replies := by
  have direct := congrArg Source.direct origin
  change n.direct = c.ticket.direct at direct
  rw [ticket] at direct
  change n.direct = d.flags.direct at direct
  have node := direct.trans notDirect
  have owner := congrArg Source.owner origin
  rw [Open.source,ticket] at owner
  refine ⟨node,?_⟩
  apply Vector.ext
  intro i hi
  have eq := congrArg (fun v : fields 3 F => v[i]) owner
  interval_cases i <;> simpa [Step.source,node,Dispatch.ticket,Dispatch.owner,hook,notDirect,threeLimbs,circuit_norm] using eq

/-- One physical allocating header and its complete prepend walk bind the public hook's
returned buffers, in their original indexed order, to the actual persistent store. -/
def ReturnedBatchAt (w : EnsembleWitness (native image source target)) (store : Store) (d : Dispatch F) : Prop :=
    ∃ call ∈ (allocationInputs (observed w)).1, call.ticket = d.ticket d.flags ∧ ∃ reply rows,
      (WriteStreams.fromEndpoints source.host target.host).hooks[Address.toNat d.previous.replies]? = some reply ∧
      Walk.IsWalk (fun n : Step F => (n.before,n.after)) call.first call.last rows ∧
      rows.length = reply.hints.length ∧ ∀ i : Fin rows.length, let n := rows[i.val]
        n.direct = 0 ∧ n.reply = d.previous.replies ∧ Address.toNat n.index = rows.length-(i.val+1) ∧
        ∃ bytes, reply.hints[rows.length-(i.val+1)]? = some bytes ∧
          node? store (Address.toNat n.node.node.pointer) = some ⟨bytes,Address.toNat n.node.node.tail⟩

/-- The real dispatch ticket opens one complete batch for the indexed public hook reply.
Every returned hint is prepended in reverse order at its actual permanent identity, including
empty buffers. A reply with no hints has an actual matching header and an empty walk. -/
theorem native_hook_batch (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) {store : Store} (stored : PersistentQueue w store)
    (d : Dispatch F) (md : d ∈ allocatingDispatches (observed w)) (hook : d.flags.hook = 1) :
    ReturnedBatchAt w store d := by
  obtain ⟨reply,found,number,_,_⟩ := native_hook_reply w ok fit raw d md hook
  have gate := ((native_allocation_tickets w ok fit raw).2 d md).2
  rw [hook] at gate
  have notDirect : d.flags.direct = 0 := add_right_cancel (show d.flags.direct + 1 = 0+1 by simpa only [zero_add] using gate)
  obtain ⟨call,mc,ticket,rows,walk,size,phys⟩ := native_dispatch_batch w ok fit raw d md
  have count := hook_count ticket hook notDirect
  refine ⟨call,mc,ticket,reply,rows,found,walk,(size.trans (congrArg Address.toNat count)).trans number.symm,?_⟩
  intro i
  let r := rows[i.val]
  have mem := phys r (List.getElem_mem i.isLt)
  have v (n) (h : n ∈ rows) := (allocation_endpoints w ok fit raw).2 n (phys n h)
  obtain ⟨origin,position⟩ := walk_sources walk v i
  change r.source = call.source at origin
  change Address.toNat r.index + (i.val+1) = Address.toNat call.count at position
  obtain ⟨direct,owner⟩ := hook_node ticket origin hook notDirect
  have idx : Address.toNat r.index = rows.length-(i.val+1) := by omega
  obtain ⟨bytes,publicBytes,atNode⟩ := native_returned_buffer w ok fit raw stored r mem direct
  rw [owner,idx,StreamKey.contents,found,Option.bind_some] at publicBytes
  exact ⟨direct,owner,idx,bytes,publicBytes,atNode⟩

end SP1Clean.Export.WriteObservationAssembly
