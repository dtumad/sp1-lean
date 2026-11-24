import SP1Clean.Native.Operations.WriteAllocationPayload
import SP1Clean.Native.Operations.WriteBlockSource
import SP1Clean.Native.Operations.AddressSum

/-! # Mandatory padded words for freshly allocated WRITE hint nodes

An authorization opens one word walk. A hook consumes public tag-4 bytes when its next
word contains data. A direct node supplies tag-14 bytes at the grouped guest placements'
actual multiplicity. Both publish the identical immutable padded word to future readers.
-/

namespace SP1Clean.WriteAllocation.Words
open Circuit WriteEffects Semantics.HintQueue

variable {p : Nat} [Fact p.Prime]

/-- Open one new immutable node, including an empty allocation. -/
def seedMain (c : Var Contents (ZMod p)) : Circuit (ZMod p) Unit := do
  contentsChannel.pull c
  cursorChannel.push (start c)

/-- One consumed allocation authorizes precisely its first padded word. -/
def seedCircuit : GeneralFormalCircuit (ZMod p) Contents unit where
  name := "sp1.native.write_allocation_word_start"
  main := seedMain
  Spec _ _ _ := True
  ProverAssumptions _ _ _ := True
  channelsWithRequirements := [cursorChannel.toRaw]
  soundness := by circuit_proof_start [seedMain,contentsChannel,cursorChannel]
  completeness := by circuit_proof_start [seedMain,contentsChannel,cursorChannel]

variable [Fact (2^17 < p)]

/-- Occupied hook words consume exactly one verifier-fixed returned block. -/
def Row.hookGate {F : Type} [One F] [Sub F] [Mul F] (r : Row F) : F :=
  ((1 : F) - r.prior.contents.direct)*r.payload.mask[0]

/-- An occupied direct word can supply any number of reads of that same fresh pointer. -/
def Row.directGate {F : Type} [Mul F] (r : Row F) : F := r.prior.contents.direct*r.payload.mask[0]

/-- Word construction, source selection and nonwrapping progress through the byte length. -/
def Row.Valid (r : Row (ZMod p)) : Prop :=
  IsBool r.prior.contents.direct ∧ r.payload.Valid ∧
  AddressSum.Spec ⟨r.predecessor,#v[1,0,0],r.prior.contents.pointer⟩ ∧
  AddressSum.Spec ⟨r.prior.index,#v[1,0,0],r.nextIndex⟩ ∧
  AddressSum.Spec ⟨r.left,#v[r.payload.used,0,0],r.prior.remaining⟩ ∧
  (r.payload.last=1 → r.left = #v[0,0,0])

/-- Arithmetic and the complete five-site private word ledger. -/
def wordMain (r : Var Row (ZMod p)) : Circuit (ZMod p) Unit := do
  let supply <== r.directGate * r.blockReads
  assertBool r.prior.contents.direct
  assertion payloadCircuit r.payload
  assertion AddressSum.circuit ⟨r.predecessor,#v[1,0,0],r.prior.contents.pointer⟩
  assertion AddressSum.circuit ⟨r.prior.index,#v[1,0,0],r.nextIndex⟩
  assertion AddressSum.circuit ⟨r.left,#v[r.payload.used,0,0],r.prior.remaining⟩
  forEach (Vector.ofFn fun i : Fin 3 => i) fun i => assertZero (r.payload.last*r.left[i])
  cursorChannel.pull r.prior
  blockChannel.pullIf r.hookGate r.returned
  blockChannel.emit supply r.direct
  HostHintQueue.wordChannel.emit r.wordReads r.word
  cursorChannel.pushIf r.payload.more r.next

/-- Component metadata from the actual lowered row. -/
instance wordElaborated : ElaboratedCircuit (ZMod p) Row unit wordMain := by elaborate_circuit

omit [Fact (2^17 < p)] in
private theorem end_iff (r : Row (ZMod p)) (more : IsBool r.payload.more) :
    (∀ i : Fin 3, r.payload.last*r.left[i]=0) ↔ (r.payload.last=1 → r.left = #v[0,0,0]) := by
  rcases more with done|cont
  · have last : r.payload.last=1 := by simp [Payload.last,done]
    simp only [last,one_mul,true_implies]
    constructor
    · intro empty
      apply Vector.ext
      intro i bound
      have h := empty ⟨i,bound⟩
      rcases (show i=0 ∨ i=1 ∨ i=2 by omega) with rfl|rfl|rfl <;> exact h
    · rintro eq i
      rw [eq]
      fin_cases i <;> rfl
  · simp [Payload.last,cont]

private theorem receipt_valid {r : Row (ZMod p)} (h : r.Valid) : r.word.Valid := by
  obtain ⟨_,payload,pointer,index,_,_⟩ := h
  have unit : Address.toNat (#v[1,0,0] : fields 3 (ZMod p))=1 := by simp [Address.toNat,circuit_norm,ZMod.val_one]
  have positive := pointer.2.2.2
  change Address.toNat r.prior.contents.pointer = Address.toNat r.predecessor + Address.toNat (#v[1,0,0] : fields 3 (ZMod p)) at positive
  rw [unit] at positive
  have marker : IsBool r.payload.more := (payload 7).2.1
  exact ⟨pointer.2.2.1,by change 0 < Address.toNat r.prior.contents.pointer; omega,index.1,payload.packed,by rcases marker with a|a <;> simp [Row.word,Payload.last,a]⟩

omit [Fact (2^17 < p)] in
private theorem of_constraints (r : Row (ZMod p)) (direct : IsBool r.prior.contents.direct)
    (payload : r.payload.Valid) (pointer : AddressSum.Spec ⟨r.predecessor,#v[1,0,0],r.prior.contents.pointer⟩)
    (index : AddressSum.Spec ⟨r.prior.index,#v[1,0,0],r.nextIndex⟩)
    (remaining : AddressSum.Spec ⟨r.left,#v[r.payload.used,0,0],r.prior.remaining⟩)
    (stop : ∀ i : Fin 3, r.payload.last*r.left[i]=0) : r.Valid :=
  ⟨direct,payload,pointer,index,remaining,(end_iff r (payload 7).2.1).mp stop⟩

omit [Fact (2^17 < p)] in
private theorem hookBool (direct occupied : ZMod p) (d : IsBool direct) (o : IsBool occupied) :
    IsBool ((1 - direct)*occupied) := by
  rcases d with rfl|rfl <;> rcases o with rfl|rfl <;> simp [IsBool]

/-- A row must authenticate precisely the same bytes at the supplied/guest block and persistent queue word. -/
def wordCircuit : GeneralFormalCircuit (ZMod p) Row unit where
  name := "sp1.native.write_allocation_word"
  main := wordMain
  elaborated := wordElaborated
  computableWitnesses := by computable_witnesses [Row.directGate,Row.hookGate,Payload.last,Payload.more,Payload.used]
  Spec r _ _ := r.Valid
  ProverAssumptions r _ _ := r.Valid
  channelsWithRequirements := [blockChannel.toRaw,HostHintQueue.wordChannel.toRaw,cursorChannel.toRaw]
  soundness := by
    circuit_proof_start [wordMain,payloadCircuit,AddressSum.circuit,Payload.used,Payload.last,Payload.more,
      Row.hookGate,Row.directGate,Row.word,Word.ofBytes,cursorChannel,blockChannel,HostHintQueue.wordChannel]
    obtain ⟨_,direct,payload,pointer,index,remaining,stop⟩ := h_holds
    have valid := of_constraints
      ⟨⟨⟨input_prior_contents_direct,input_prior_contents_pointer,input_prior_contents_reply,input_prior_contents_index,
        input_prior_contents_length⟩,input_prior_index,input_prior_remaining⟩,input_predecessor,input_nextIndex,input_left,
        ⟨input_payload_bytes,input_payload_mask⟩,input_blockReads,input_wordReads⟩ direct payload pointer index remaining (fun i => stop i)
    exact ⟨valid,hookBool _ _ direct (payload 0).2.1,fun _ => receipt_valid valid⟩
  completeness := by
    circuit_proof_start [wordMain,payloadCircuit,AddressSum.circuit,Payload.used,Payload.last,Payload.more,
      Row.hookGate,Row.directGate,Row.word,Word.ofBytes,cursorChannel,blockChannel,HostHintQueue.wordChannel]
    obtain ⟨d,b,pos,idx,remaining,last⟩ := h_assumptions
    exact ⟨h_env,d,b,pos,idx,remaining,(fun i => (end_iff _ (b 7).2.1).mpr last i)⟩

end SP1Clean.WriteAllocation.Words
