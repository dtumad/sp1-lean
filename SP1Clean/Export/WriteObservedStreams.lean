import SP1Clean.Export.WriteAllocatedPayloads
import SP1Clean.Export.WritePublicSlices
import SP1Clean.Soundness.WriteStreamPrefixes

/-! # Complete guest-to-host byte attribution on one raw chronological WRITE tape -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Semantics.HintQueue Soundness WriteEffects
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot}

/-- Physical WRITE occurrences and their host observations, including empty input and
output buffers and hooks with no returned buffers. Byte and reply prefixes use the semantic
descriptor and original x12 length of every preceding instruction. -/
structure ObservedWriteTape (w : EnsembleWitness (native image source target)) (store : Store) (path : List (Dispatch F)) : Prop where
  /-- Every actual dispatcher appears exactly once. -/
  exhaustive : path.Perm (physicalDispatches (observed w))
  /-- The recovered sequence is sorted by the original CPU's incoming clock. -/
  chronological : (path.map (fun d => Address.toNat d.request.header.clock)).Pairwise (· < ·)
  /-- The original stream prefixes, consumed replies and appended journal bind both snapshots. -/
  endpoints : (WriteStreams.fromEndpoints source.host target.host).Binds source.host target.host
  /-- Consumed reply and all three output byte counts exhaust the public stream deltas. -/
  totals : dispatchCounts path = StreamCounts.ofStreams (.fromEndpoints source.host target.host)
  /-- Every call has the actual original CPU and x12 receipts. -/
  origin : ∀ d ∈ path, DispatchOrigin w d
  /-- The four counters at each call equal the exact semantic transcript prefix. -/
  positions : ∀ i : Fin path.length, StreamCounts.ofCursor path[i.val].previous = dispatchCounts (path.take i.val)
  /-- The stdout, stderr, public output or indexed hook-request slice is precisely the guest buffer. -/
  published : ∀ d ∈ path, PublicSliceAt w d
  /-- Each hook consumes and journals the same complete guest request and canonical descriptor. -/
  requests : ∀ d ∈ path, ∀ fd, d.route = .hook fd → HookRequestAt w d fd
  /-- Direct hints store the complete guest buffer in the common persistent store. -/
  direct : ∀ d ∈ path, d.route = .hint → DirectBufferAt w store d
  /-- Each consumed hook reply contributes exactly its returned buffers, in the released order. -/
  returned : ∀ d ∈ path, ∀ fd, d.route = .hook fd → ReturnedBatchAt w store d

private theorem final_counts (w : EnsembleWitness (native image source target)) (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp)
    (prior : fields 3 F) :
    let streams := WriteStreams.fromEndpoints source.host target.host
    StreamCounts.ofCursor ({finalCursor (p := SP1Prime) target.clock streams with clock := prior}) = StreamCounts.ofStreams streams := by
  let s := WriteStreams.fromEndpoints source.host target.host
  have checked : inventoryOK s = true := (native_stream_boundary w fit raw).2
  have fits (k : StreamKey) (b : Bytes) (found : k.contents s = some b) : b.length < 2^48 :=
    (Query.fits_of_inventory (q := .length k) checked (by simp only [Query.lookup,found,Option.map_some])).2.2.2
  change StreamCounts.mk (Address.toNat (Address.ofNat (p := SP1Prime) s.stdout.length)) (Address.toNat (Address.ofNat (p := SP1Prime) s.stderr.length))
    (Address.toNat (Address.ofNat (p := SP1Prime) s.publicOutput.length)) (Address.toNat (Address.ofNat (p := SP1Prime) s.hooks.length)) = _
  rw [Address.toNat_ofNat _ (fits .stdout _ rfl),Address.toNat_ofNat _ (fits .stderr _ rfl),
    Address.toNat_ofNat _ (fits .publicOutput _ rfl),Address.toNat_ofNat _ (hooks_lt_of_inventory checked)]
  rfl

/-- Raw native acceptance fixes a unique store and a single exhaustive chronological WRITE
tape that authenticates every selected guest-to-public byte and every direct or returned
hint. Exact natural totals exclude omitted and leftover output bytes and hook replies. -/
theorem native_observed_write_tape (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    ∃! store, PersistentQueue w store ∧ ∃ path, ObservedWriteTape w store path := by
  obtain ⟨store,⟨stored,path,all,⟨prior,walk⟩,sorted,_,calls⟩,_⟩ := native_allocated_payloads w ok fit raw
  have each (d) (m : d ∈ path) := (native_dispatch_origin w ok fit raw d (all.mem_iff.mp m))
  have valid (d) (m : d ∈ path) : d.Valid ∧ d.request.Valid :=
    ⟨(physical_dispatch_valid w ok fit raw d (all.mem_iff.mp m)).1,(each d m).1⟩
  have start : StreamCounts.ofCursor (initialCursor (p := SP1Prime) source.clock) = ⟨0,0,0,0⟩ := by
    change StreamCounts.ofCursor (initialCursor (p := SP1Prime) 0) = _
    decide
  obtain ⟨_,_,unique⟩ := native_persistent_queue_unique w ok fit raw
  refine ⟨store,⟨stored,path,all,sorted,(native_stream_boundary w fit raw).1,?_,each,?_,fun d md => native_public_slice w ok fit raw d (all.mem_iff.mp md),
    fun d md _ => native_hook_request w ok fit raw d (all.mem_iff.mp md),?_,?_⟩,
    fun other h => (unique _ h.1).trans (unique _ stored).symm⟩
  · have total := (dispatch_walk_counts walk valid).1
    rw [start,final_counts w fit raw prior] at total
    exact total.symm
  · intro i
    simpa only [start] using (dispatch_walk_counts walk valid).2 i
  · intro d md route
    obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp md
    have flags := (valid d md).1.route_flags (valid d md).2
    exact e ▸ (calls ⟨i,hi⟩).2.2.1 (by change path[i].flags.direct = 1; rw [e,flags,route]; rfl)
  · intro d md fd route
    obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp md
    have flags := (valid d md).1.route_flags (valid d md).2
    exact e ▸ (calls ⟨i,hi⟩).2.2.2 (by change path[i].flags.hook = 1; rw [e,flags,route]; simp [routeFlags,DispatchFlags.hook])

end SP1Clean.Export.WriteObservationAssembly
