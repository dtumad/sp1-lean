import SP1Clean.Export.WriteDirectCalls

/-! # The exact persistent node of each physical direct WRITE -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Semantics.HintQueue Soundness WriteAllocation WriteEffects
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot}

private theorem direct_fields {d : Dispatch F} {c : Open F} {n : Step F}
    (ticket : c.ticket = d.ticket d.flags) (origin : n.source = c.source)
    (direct : d.flags.direct = 1) (hook : d.flags.hook = 0) :
    n.direct = 1 ∧ n.node.node.pointer = d.pointer ∧ n.length = d.length := by
  have flag := congrArg Source.direct origin
  change n.direct = c.ticket.direct at flag
  rw [ticket] at flag
  have node := flag.trans direct
  refine ⟨node,?_,?_⟩
  · have ptr := congrArg Source.owner origin
    apply Vector.ext
    intro i hi
    have eq := congrArg (fun v : fields 3 F => v[i]) ptr
    interval_cases i <;> simpa [Step.source,Open.source,ticket,Dispatch.ticket,Dispatch.owner,node,direct,hook,threeLimbs,circuit_norm] using eq
  · have len := congrArg Source.directLength origin
    apply Vector.ext
    intro i hi
    have eq := congrArg (fun v : fields 3 F => v[i]) len
    interval_cases i <;> simpa [Step.source,Open.source,ticket,Dispatch.ticket,node,direct,scale,threeLimbs,circuit_norm] using eq

/-- The unique direct allocation step is a singleton with the dispatcher's pointer and
length. Its complete physical word walk, including the terminal row of an empty buffer,
fixes the natural byte length and tail of the actual shared-store node. -/
theorem native_direct_node (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) {store : Store} (stored : PersistentQueue w store)
    (d : Dispatch F) (md : d ∈ allocatingDispatches (observed w)) (direct : d.flags.direct = 1) :
    ∃ c ∈ (allocationInputs (observed w)).1, c.ticket = d.ticket d.flags ∧
      ∃ n ∈ (allocationInputs (observed w)).2, Walk.IsWalk (fun n : Step F => (n.before,n.after)) c.first c.last [n] ∧
        n.direct = 1 ∧ n.node.node.pointer = d.pointer ∧ n.length = d.length ∧
        ∃ node, node? store (Address.toNat d.pointer) = some node ∧
          node.bytes.length = Address.toNat d.length ∧ node.tail = Address.toNat n.node.node.tail := by
  obtain ⟨c,mc,ticket,rows,walk,count,present⟩ := native_dispatch_batch w ok fit raw d md
  have one : Address.toNat c.count = 1 := by simp [Open.count,ticket,Dispatch.ticket,direct,Address.toNat,circuit_norm,show (1 : F).val = 1 by decide]
  obtain ⟨n,rfl⟩ := List.length_eq_one_iff.mp (count.trans one)
  have gate := ((native_allocation_tickets w ok fit raw).2 d md).2
  have hook : d.flags.hook = 0 := add_left_cancel (show 1+d.flags.hook = 1+0 by simpa only [direct,add_zero] using gate)
  obtain ⟨flag,ptr,len⟩ := direct_fields ticket (congrArg WriteAllocation.Cursor.source walk.1) direct hook
  have mn := present n List.mem_cons_self
  obtain ⟨path,wordWalk,physical⟩ := node_word_walk w ok fit raw n mn
  have checks (r) (m : r ∈ path) := (native_word_endpoints w ok fit raw).2 r (physical r m)
  obtain ⟨_,last,mem,owner,_,ends⟩ := Words.walk_inventory n.contents path wordWalk checks
  have binding := stored.nodes n mn
  obtain ⟨node,found,tail,_⟩ := binding
  have length := stored_length ((allocation_endpoints w ok fit raw).2 n mn) (stored.nodes n mn)
    (checks last mem) (stored.words last (physical _ mem)) owner ends found
  exact ⟨c,mc,ticket,n,mn,walk,flag,ptr,len,node,ptr ▸ found,len ▸ length,tail.symm⟩

end SP1Clean.Export.WriteObservationAssembly
