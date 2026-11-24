import SP1Clean.Export.WriteAllocationStoreUnique
import SP1Clean.Proofs.Completeness.WriteBlockLedgers

/-! # Sources of grouped WRITE byte blocks in arbitrary accepted native witnesses -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteAllocation WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
attribute [local irreducible] base withSources preprocessing

private theorem registered : (blockChannel (p := SP1Prime)).toRaw ∈ channels := List.mem_of_getElem? (i := 14) rfl

/-- The physical stream block channel consists of the placement table, its public endpoint
provider, and the allocation-word table. All signed occurrences remain in their physical order. -/
theorem allocation_block_ledger (w : EnsembleWitness (preprocessing image source target final)) :
    let ch := (blockChannel (p := SP1Prime)).toRaw
    w.interactionsWith ch = [((slot image source target final 9).table w),((slot image source target final 12).table w),
      ((slot image source target final 18).table w)].flatMap (·.interactionsWith ch) := by
  let ch := (blockChannel (p := SP1Prime)).toRaw
  have support : selectedSlots source target ch = [9,12,18] := rfl
  simpa only [support,List.flatMap_cons,List.flatMap_nil,List.append_nil] using fresh_slots_ledger w ch registered
    (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))

/-- A concrete public block has one authentic owner, occupied position, extent and eight
actual byte lanes in the public WRITE streams. -/
def FixedBlock (s : WriteStreams) (b : StreamBlock F) : Prop :=
  inventoryOK s = true ∧ ∃ k bytes i, k.contents s = some bytes ∧ 8 * i < bytes.length ∧ b = encodeBlock k bytes i

/-- Block suppliers are either verifier-fixed endpoint rows or positive direct publications
by enabled physical allocation words. -/
def BlockOrigin (w : EnsembleWitness (preprocessing image source target final)) (b : StreamBlock F) : Prop :=
  FixedBlock (.fromEndpoints source.host target.host) b ∨ ∃ r ∈ allocationWords w,
    r.directGate = 1 ∧ r.blockReads ≠ 0 ∧ r.direct = b

private theorem pull_not_push (b : StreamBlock F) {gate : F} (bit : IsBool gate) :
    ¬(blockChannel.pulledIfValue gate b).Push := by
  intro push
  rcases bit with rfl | rfl
  · exact push.1 rfl
  · exact push.2 rfl rfl

private theorem gates {g : WriteEffects.Group F} (valid : g.Valid) : IsBool g.leftGate ∧ IsBool g.rightGate := by
  obtain ⟨_,_,ignored,left,right,_⟩ := valid
  by_cases zero : g.previous.sink = 0
  · simp [Group.leftGate,Group.rightGate,ignored,zero,IsBool]
  · simpa [Group.leftGate,Group.rightGate,ignored,zero] using And.intro left right

private theorem group_source (w : EnsembleWitness (preprocessing image source target final)) (ok : w.Constraints) :
    ((slot image source target final 9).table w).Authenticates blockChannel (BlockOrigin w) := by
  let t : TableSlot (preprocessing image source target final).tables groupComponent := slot image source target final 9
  change (t.table w).Authenticates blockChannel (BlockOrigin w)
  intro row mem i emitted push
  have h := t.table_constraints w ok row mem
  rw [t.table_component w] at h emitted
  let env := (t.table w).environment row
  let g := groupComponent.rowInput env
  have fact := guarded_group_valid (varFromOffset (ProvablePair WriteEffects.Group field) 0) _ _ ((Component.constraintsHold_iff _).mp h)
  rw [eval_varFromOffset_valueFromOffset] at fact
  change IsBool g.2 ∧ (g.2 = 1 → g.1.Valid) at fact
  have bits : IsBool (g.2*g.1.leftGate) ∧ IsBool (g.2*g.1.rightGate) := by
    rcases fact.1 with off | on
    · simp [off,IsBool]
    · simpa only [on,one_mul] using gates (fact.2 on)
  rw [groupInput_blocks] at emitted
  rcases List.mem_cons.mp emitted with rfl | right
  · exact (pull_not_push _ bits.1 push).elim
  · obtain rfl := List.mem_singleton.mp right
    exact (pull_not_push _ bits.2 push).elim

private theorem word_input (w : EnsembleWitness (preprocessing image source target final)) (ok : w.Constraints)
    (row) (mem : row ∈ ((slot image source target final 18).table w).table) :
    let t := (slot image source target final 18).table w
    let env := t.environment row
    let r := Words.wordComponent.rowInput env
    (IsBool r.2 ∧ (r.2 = 1 → r.1.Valid)) ∧
      t.component.operations.interactionValuesWith blockChannel.toRaw env = Words.blockTraffic r := by
  let h : TableSlot (preprocessing image source target final).tables Words.wordComponent := slot image source target final 18
  have v := h.table_constraints w ok row mem
  rw [h.table_component w] at v
  have check := (Component.constraintsHold_iff _).mp v
  have fact := Words.guarded_word_valid (varFromOffset (ProvablePair Words.Row field) 0) _ _ check
  rw [eval_varFromOffset_valueFromOffset] at fact
  refine ⟨fact,?_⟩
  change (h.table w).component.operations.interactionValuesWith blockChannel.toRaw ((h.table w).environment row) = _
  rw [h.table_component w]
  exact Words.wordInput_blocks _ v fact.1

private theorem word_gates {r : Words.Row F} (v : r.Valid) : IsBool r.hookGate ∧ IsBool r.directGate := by
  have occupied : IsBool r.payload.mask[0] := (v.2.1 (0 : Fin 8)).2.1
  rcases v.1 with h | h <;> rcases occupied with o | o <;>
    simp [Words.Row.hookGate,Words.Row.directGate,h,o,IsBool]

private theorem words_source (w : EnsembleWitness (preprocessing image source target final)) (ok : w.Constraints) :
    ((slot image source target final 18).table w).Authenticates blockChannel (BlockOrigin w) := by
  intro row mem i emitted push
  let t := (slot image source target final 18).table w
  let r := Words.wordComponent.rowInput (t.environment row)
  obtain ⟨⟨bit,honest⟩,ledger⟩ := word_input w ok row mem
  change IsBool r.2 at bit
  change r.2 = 1 → r.1.Valid at honest
  rw [ledger] at emitted
  change i ∈ Words.blockTraffic r at emitted
  rcases List.mem_cons.mp emitted with rfl | publish
  · have binary : IsBool (r.2*r.1.hookGate) := by
      rcases bit with off | on
      · simp [off,IsBool]
      · simpa only [on,one_mul] using (word_gates (honest on)).1
    exact (pull_not_push _ binary push).elim
  · obtain rfl := List.mem_singleton.mp publish
    have paid : r.2*(r.1.directGate*r.1.blockReads) ≠ 0 := push.1
    have on : r.2 = 1 := bit.resolve_left (left_ne_zero_of_mul paid)
    have positive := right_ne_zero_of_mul paid
    refine ⟨r.1.direct,rfl,Or.inr ⟨r.1,?_,(word_gates (honest on)).2.resolve_left (left_ne_zero_of_mul positive),
      right_ne_zero_of_mul positive,rfl⟩⟩
    apply List.mem_map.mpr
    refine ⟨r,List.mem_filter.mpr ⟨?_,decide_eq_true on⟩,rfl⟩
    exact List.mem_map_of_mem (f := fun row => valueFromOffset (ProvablePair Words.Row field) 0 (t.environment row)) mem

/-- Every unit pull on the complete physical block ledger is supplied by an authenticated
public block or a real occupied direct allocation word under its actual reader multiplicity. -/
theorem native_block_origin (w : EnsembleWitness (assembly image source target final)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (b : StreamBlock F)
    (read : blockChannel.pulledValue b ∈ (observed w).interactionsWith blockChannel.toRaw) : BlockOrigin (observed w) b := by
  let seen := observed w
  let ch := (blockChannel (p := SP1Prime)).toRaw
  have ok := (observed_constraints w).mp checked
  have balance := observed_balance w fit raw ch (protocol_installed image source target final _ registered) (of_decide_eq_true rfl)
  change BalancedInteractions (seen.interactionsWith ch) at balance
  rw [allocation_block_ledger] at balance read
  apply authenticated_pull_of_tables _ blockChannel (BlockOrigin seen) _ balance b read
  intro t mem
  rcases List.mem_cons.mp mem with rfl | rest
  · exact group_source seen ok
  rcases List.mem_cons.mp rest with rfl | last
  · let h := slot image source target final 12
    exact (block_authenticates source.host target.host (h.table seen) (h.table_component seen)
      (h.table_constraints seen ok)).mono (fun _ hb => Or.inl hb)
  · obtain rfl := List.mem_singleton.mp last
    exact words_source seen ok

/-- Every occupied hook-return word actively consumes its public tag-4 block on the
original allocation-word row. Disabled rows and the empty padding word produce zero demand. -/
theorem hook_block_pull (w : EnsembleWitness (preprocessing image source target final)) (ok : w.Constraints)
    (r : Words.Row F) (member : r ∈ allocationWords w) (hook : r.hookGate = 1) :
    blockChannel.pulledValue r.returned ∈ w.interactionsWith blockChannel.toRaw := by
  let t := (slot image source target final 18).table w
  obtain ⟨x,kept,same⟩ := List.mem_map.mp member
  obtain ⟨physical,on⟩ := List.mem_filter.mp kept
  obtain ⟨row,m,found⟩ := List.mem_map.mp physical
  let stored := Words.wordComponent.rowInput (t.environment row)
  change stored = x at found
  subst x
  change stored.1 = r at same
  subst r
  have enabled : stored.2 = 1 := of_decide_eq_true on
  rw [allocation_block_ledger]
  apply List.mem_flatMap.mpr
  refine ⟨t,by simp [t],List.mem_flatMap.mpr ⟨row,m,?_⟩⟩
  rw [(word_input w ok row m).2]
  apply List.mem_cons.mpr
  left
  change blockChannel.pulledValue stored.1.returned = blockChannel.pulledIfValue (stored.2 * stored.1.hookGate) stored.1.returned
  rw [enabled,hook,one_mul]
  rfl

private theorem tag_return {s : WriteStreams} {r : Words.Row F} (auth : FixedBlock s r.returned) :
    ∃ bytes, (StreamKey.returned (Address.toNat r.prior.contents.reply) (Address.toNat r.prior.contents.index)).contents s = some bytes ∧
      8 * Address.toNat r.prior.index < bytes.length ∧ r.payload.used.val = min 8 (bytes.length - 8 * Address.toNat r.prior.index) ∧
      ∀ j : Fin 8, r.payload.bytes[j].val = (bytes[Address.toNat r.prior.index * 8 + j.val]?.getD 0).toNat := by
  obtain ⟨ok,k,bytes,i,owner,active,same⟩ := auth
  have fields := encodeBlock_fields (p := SP1Prime) s ok owner active
  rw [← same] at fields
  obtain ⟨tag,reply,hint,idx,used,lanes⟩ := fields
  change (4 : F).val = k.coordinates.1 at tag
  rw [show (4 : F).val = 4 by decide] at tag
  cases k with
  | stdout | stderr | publicOutput | request _ => simp [StreamKey.coordinates] at tag
  | returned a b =>
    change Address.toNat r.prior.contents.reply = a at reply
    change Address.toNat r.prior.contents.index = b at hint
    change Address.toNat r.prior.index = i at idx
    subst a; subst b; subst i
    exact ⟨bytes,owner,active,used,lanes⟩

/-- In an arbitrary accepted witness an occupied hook-return word has the exact public reply,
returned-hint index, word index, occupied extent and all eight endpoint bytes. -/
theorem native_returned_bytes (w : EnsembleWitness (assembly image source target final)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (r : Words.Row F)
    (mem : r ∈ allocationWords (observed w)) (hook : r.hookGate = 1) :
    ∃ bytes, (StreamKey.returned (Address.toNat r.prior.contents.reply) (Address.toNat r.prior.contents.index)).contents
        (.fromEndpoints source.host target.host) = some bytes ∧
      8 * Address.toNat r.prior.index < bytes.length ∧ r.payload.used.val = min 8 (bytes.length - 8 * Address.toNat r.prior.index) ∧
      ∀ j : Fin 8, r.payload.bytes[j].val = (bytes[Address.toNat r.prior.index * 8 + j.val]?.getD 0).toNat := by
  rcases native_block_origin w checked fit raw r.returned
      (hook_block_pull _ ((observed_constraints w).mp checked) _ mem hook) with fixed | privateWord
  · exact tag_return fixed
  · obtain ⟨other,_,_,_,eq⟩ := privateWord
    have impossible : (14 : F) = 4 := congrArg StreamBlock.stream eq
    have bad := congrArg ZMod.val impossible
    rw [show (14 : F).val = 14 by decide,show (4 : F).val = 4 by decide] at bad
    contradiction

/-- The enabled physical grouped placements, including empty guest-word windows. -/
def allocationGroups (w : EnsembleWitness (preprocessing image source target final)) : List (WriteEffects.Group F) :=
  enabledInputs (guardedInputs WriteEffects.Group ((slot image source target final 9).table w))

/-- Each occupied grouped placement side pulls its genuine left or right destination block. -/
theorem group_block_pull (w : EnsembleWitness (preprocessing image source target final)) (g : WriteEffects.Group F)
    (mem : g ∈ allocationGroups w) (side : Bool) (gate : (if side then g.rightGate else g.leftGate) = 1) :
    blockChannel.pulledValue (g.block side) ∈ w.interactionsWith blockChannel.toRaw := by
  let h : TableSlot (preprocessing image source target final).tables groupComponent := slot image source target final 9
  let t := h.table w
  obtain ⟨x,kept,same⟩ := List.mem_map.mp mem
  obtain ⟨physical,on⟩ := List.mem_filter.mp kept
  obtain ⟨row,m,found⟩ := List.mem_map.mp physical
  let stored := groupComponent.rowInput (t.environment row)
  change stored = x at found
  subst x
  change stored.1 = g at same
  subst g
  have enabled : stored.2 = 1 := of_decide_eq_true on
  rw [allocation_block_ledger]
  apply List.mem_flatMap.mpr
  refine ⟨t,List.mem_cons_self,List.mem_flatMap.mpr ⟨row,m,?_⟩⟩
  change _ ∈ (h.table w).component.operations.interactionValuesWith blockChannel.toRaw (t.environment row)
  rw [h.table_component w,groupInput_blocks]
  change blockChannel.pulledValue (stored.1.block side) ∈ groupBlocks stored
  cases side with
  | false =>
    change stored.1.leftGate = 1 at gate
    apply List.mem_cons.mpr; left
    change blockChannel.pulledValue _ = blockChannel.pulledIfValue (stored.2*stored.1.leftGate) _
    rw [enabled,gate,one_mul]; rfl
  | true =>
    change stored.1.rightGate = 1 at gate
    apply List.mem_cons_of_mem
    apply List.mem_singleton.mpr
    change blockChannel.pulledValue _ = blockChannel.pulledIfValue (stored.2*stored.1.rightGate) _
    rw [enabled,gate,one_mul]; rfl

private theorem fixed_not_direct {s : WriteStreams} {b : StreamBlock F} (fixed : FixedBlock s b) :
    b.stream ≠ 14 := by
  obtain ⟨ok,k,bytes,i,owner,occupied,rfl⟩ := fixed
  have tag := (encodeBlock_fields (p := SP1Prime) s ok owner occupied).1
  intro direct
  rw [direct,show (14 : F).val = 14 by decide] at tag
  cases k <;> simp [StreamKey.coordinates] at tag

/-- A direct grouped guest placement is funded by the real active, occupied allocation
word with its exact fresh pointer, index, extent and eight byte fields. -/
theorem native_direct_group (w : EnsembleWitness (assembly image source target final)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (g : WriteEffects.Group F) (mem : g ∈ allocationGroups (observed w))
    (side : Bool) (gate : (if side then g.rightGate else g.leftGate) = 1) (direct : g.previous.sink = 14) :
    ∃ r ∈ allocationWords (observed w), r.directGate = 1 ∧ r.blockReads ≠ 0 ∧ r.direct = g.block side := by
  rcases native_block_origin w checked fit raw (g.block side) (group_block_pull _ _ mem side gate) with fixed | actual
  · exact (fixed_not_direct fixed direct).elim
  · exact actual

end SP1Clean.Export.WriteObservationAssembly
