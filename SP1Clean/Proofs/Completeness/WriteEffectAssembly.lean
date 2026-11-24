import SP1Clean.Proofs.Completeness.WriteEffectTables
import SP1Clean.Proofs.Completeness.WriteCollectedEffects
import ToClean.Air.GuardedLedger

/-! # Physical WRITE effect handoffs on a single chronological collection

The buffer, classifier, word decoder, dispatcher and placement tables use the same packet observations. Each joined channel
retains its complete signed physical ledger. Its occurrence count is exactly twice the padded common demand height.
-/

namespace SP1Clean.WriteEffects.Witness
open Air.Flat Circuit Semantics Machine FormalModel.Shard TraceGen WriteAllocation
private abbrev F := ZMod SP1Prime

/-- The full two-table interaction ledger for an effect receipt, at its canonical demand height. -/
structure EffectJoin (channel : RawChannel F) (sender receiver : Table F) (height : Nat) : Prop where
  /-- Both tables retain one occurrence per occupied or padded row. -/
  count : (sender.interactionsWith channel ++ receiver.interactionsWith channel).length = 2 * height
  /-- Every complete serialized payload has zero signed sum. -/
  signed : LogUpBalanced (sender.interactionsWith channel ++ receiver.interactionsWith channel)
  /-- The native field count fits before using signed balance for physical matching. -/
  fits : (Balance.logUp (F := F)).fits (sender.interactionsWith channel ++ receiver.interactionsWith channel).length = true
  /-- Every active pull matches an active push on the original channel. -/
  matched : BalancedInteractions (sender.interactionsWith channel ++ receiver.interactionsWith channel)

private theorem join {A B : Type} [Zero A] [Zero B] {M : TypeMap} [ProvableType M]
    (ch : Channel F M) (as : List A) (bs : List B) (send : A → M F) (recv : B → M F)
    {left right : Table F} {height : Nat}
    (puts : left.interactionsWith ch.toRaw = (WitnessGeneration.guardedRows as).map (fun r => ch.pushedIfValue r.2 (send r.1)))
    (gets : right.interactionsWith ch.toRaw = (WitnessGeneration.guardedRows bs).map (fun r => ch.pulledIfValue r.2 (recv r.1)))
    (same : as.map send = bs.map recv) (size : WitnessGeneration.demandHeight as.length = height)
    (small : 2 * height < SP1Prime) : EffectJoin ch.toRaw left right height := by
  have equalSize : as.length = bs.length := by simpa only [List.length_map] using congrArg List.length same
  have count : (left.interactionsWith ch.toRaw ++ right.interactionsWith ch.toRaw).length = 2 * height := by
    rw [puts,gets]
    simp only [List.length_append,List.length_map,WitnessGeneration.guardedRows_length,← equalSize,size,two_mul]
  have signed : LogUpBalanced (left.interactionsWith ch.toRaw ++ right.interactionsWith ch.toRaw) := by
    intro msg
    rw [puts,gets,balanceOf_append,WitnessGeneration.guarded_push_sum ch as send,WitnessGeneration.guarded_pull_sum ch bs recv,same,← balanceOf_append]
    exact ch.logUp_unit_of_perm (List.Perm.refl _) msg
  have fit : (Balance.logUp (F := F)).fits (left.interactionsWith ch.toRaw ++ right.interactionsWith ch.toRaw).length = true := by
    simpa only [Balance.logUp,decide_eq_true_eq,ComputableRingChar.char_eq,ZMod.ringChar_zmod_n,count] using small
  exact ⟨count,signed,fit,Balance.logUp.balancedInteractions_of_balanced _ fit signed⟩

/-- All witness input lists are fixed by the original collector and the two verifier-supplied endpoints. -/
structure EffectFits (events : List ExecutionEvent) (entries : List Entry) (streams : WriteStreams) : Prop where
  /-- The original full headers occupy these span rows. -/
  spans : WitnessGeneration.demandHeight ((WriteBuffer.packetRows (p := SP1Prime) events (inputs entries).packets).map WriteBuffer.PacketRows.span).length ≤ UInt64.size
  /-- The original observed aligned reads occupy these physical word rows. -/
  words : WitnessGeneration.demandHeight ((WriteBuffer.packetRows (p := SP1Prime) events (inputs entries).packets).flatMap WriteBuffer.PacketRows.steps).length ≤ UInt64.size
  /-- One classifying request per dispatched call. -/
  requests : WitnessGeneration.demandHeight ((inputs entries).dispatches.map Dispatch.request).length ≤ UInt64.size
  /-- One eight-lane decoder per aligned word. -/
  decoders : WitnessGeneration.demandHeight (entries.flatMap Entry.decoderRows).length ≤ UInt64.size
  /-- One dispatcher, even on an empty packet. -/
  dispatches : WitnessGeneration.demandHeight (inputs entries).dispatches.length ≤ UInt64.size
  /-- One destination group per decoded aligned word. -/
  groups : WitnessGeneration.demandHeight (entries.flatMap (Entry.placementGroups streams)).length ≤ UInt64.size

/-- Constraints, channel guarantees, exact height and physical identity of an emitted effect component. -/
def EffectTableChecked (t : Table F) (component : Component F) (height : Nat) : Prop :=
  t.component = component ∧ t.Constraints ∧ t.Guarantees ∧ t.length = height

private theorem request_checked (rows : List (Request F)) (data : ProverData F) (fit)
    (honest : ∀ r ∈ rows, (Request.Valid) r) :
    EffectTableChecked (requestTable rows data fit) requestComponent (WitnessGeneration.demandHeight rows.length) := by
  let padded := WitnessGeneration.guardedRows (F := F) rows
  have size : padded.length = WitnessGeneration.demandHeight rows.length := WitnessGeneration.guardedRows_length rows
  have good := Table.ofInputs_valid (requestComponent (p := SP1Prime)) padded data (size.trans_le fit) (fun _ => trivial)
    (WitnessGeneration.guardedRows_all (Request.Valid) honest)
  exact ⟨rfl,good.1,good.2,(Table.ofInputs_length (requestComponent (p := SP1Prime)) padded data (size.trans_le fit) (fun _ => trivial)).trans size⟩

private theorem octet_checked (rows : List (WordRow F)) (data : ProverData F) (fit)
    (honest : ∀ r ∈ rows, (fun r : WordRow F => r.read.value.isU64 ∧ r.low = (U16toU8OperationSafe.populate r.read.value).low_bytes) r) :
    EffectTableChecked (octetTable rows data fit) wordComponent (WitnessGeneration.demandHeight rows.length) := by
  let padded := WitnessGeneration.guardedRows (F := F) rows
  have size : padded.length = WitnessGeneration.demandHeight rows.length := WitnessGeneration.guardedRows_length rows
  have good := Table.ofInputs_valid (wordComponent (p := SP1Prime)) padded data (size.trans_le fit) (fun _ => trivial)
    (WitnessGeneration.guardedRows_all (fun r : WordRow F => r.read.value.isU64 ∧ r.low = (U16toU8OperationSafe.populate r.read.value).low_bytes) honest)
  exact ⟨rfl,good.1,good.2,(Table.ofInputs_length (wordComponent (p := SP1Prime)) padded data (size.trans_le fit) (fun _ => trivial)).trans size⟩

private theorem dispatch_checked (rows : List (Dispatch F)) (data : ProverData F) (fit)
    (honest : ∀ r ∈ rows, (Dispatch.Valid) r) :
    EffectTableChecked (dispatchTable rows data fit) dispatchComponent (WitnessGeneration.demandHeight rows.length) := by
  let padded := WitnessGeneration.guardedRows (F := F) rows
  have size : padded.length = WitnessGeneration.demandHeight rows.length := WitnessGeneration.guardedRows_length rows
  have good := Table.ofInputs_valid (dispatchComponent (p := SP1Prime)) padded data (size.trans_le fit) (fun _ => trivial)
    (WitnessGeneration.guardedRows_all (Dispatch.Valid) honest)
  exact ⟨rfl,good.1,good.2,(Table.ofInputs_length (dispatchComponent (p := SP1Prime)) padded data (size.trans_le fit) (fun _ => trivial)).trans size⟩

/-- The three generated effect tables and their four complete native joins. The left and right endpoints are the
same span, aligned word, and grouped placement tables used by the other native constructions. -/
def EffectFits.Realized {events : List ExecutionEvent} {entries : List Entry} {streams : WriteStreams}
    (bounds : EffectFits events entries streams) (data : ProverData F) : Prop :=
  let batch := WriteBuffer.packetRows (p := SP1Prime) events (inputs entries).packets
  let spans := WriteBuffer.spanTable (batch.map WriteBuffer.PacketRows.span) data bounds.spans
  let words := WriteBuffer.wordTable (batch.flatMap WriteBuffer.PacketRows.steps) data bounds.words
  let requests := requestTable ((inputs entries).dispatches.map Dispatch.request) data bounds.requests
  let decoders := octetTable (entries.flatMap Entry.decoderRows) data bounds.decoders
  let dispatches := dispatchTable (inputs entries).dispatches data bounds.dispatches
  let groups := groupTable (entries.flatMap (Entry.placementGroups streams)) data bounds.groups
  let calls := WitnessGeneration.demandHeight (inputs entries).packets.length
  let guestWords := WitnessGeneration.demandHeight (WriteObservations.wordProbes (inputs entries).packets)
  EffectTableChecked requests requestComponent calls ∧ EffectTableChecked decoders wordComponent guestWords ∧ EffectTableChecked dispatches dispatchComponent calls ∧
    EffectJoin WriteBuffer.effectHeaderChannel.toRaw spans requests calls ∧
    EffectJoin WriteBuffer.wordChannel.toRaw words decoders guestWords ∧
    EffectJoin requestChannel.toRaw requests dispatches calls ∧ EffectJoin octetsChannel.toRaw decoders groups guestWords

/-- Given the original run, its successful chronological collection generates all three native
effect tables. Each of the four handoffs meets the field count bound on the full native preset. -/
theorem native_effect_tables {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (emitted : native? image source events readers = some entries) (data : ProverData F) :
    let streams := WriteStreams.fromEndpoints source.host target.host
    ∃ bounds : EffectFits events entries streams, bounds.Realized data := by
  intro streams
  obtain ⟨actual,built,_,observed,_,_,_,honest⟩ := native_inputs run readers
  cases Option.some.inj (emitted.symm.trans built)
  let batch := WriteBuffer.packetRows (p := SP1Prime) events (inputs entries).packets
  let spans := batch.map WriteBuffer.PacketRows.span
  let words := batch.flatMap WriteBuffer.PacketRows.steps
  let requests := (inputs entries).dispatches.map Dispatch.request
  let decoders := entries.flatMap Entry.decoderRows
  let dispatches := (inputs entries).dispatches
  let groups := entries.flatMap (Entry.placementGroups streams)
  let callCount := (inputs entries).packets.length
  let wordCount := WriteObservations.wordProbes (inputs entries).packets
  obtain ⟨hh,ww,oo,reqValid⟩ := effect_projections (native_collected_effects run readers emitted) streams
  have headers : spans.map WriteBuffer.Span.header = requests.map Request.header := by
    simpa only [spans,batch,requests,inputs,List.map_map,Function.comp_def] using hh
  have reads : words.map WriteBuffer.Step.read = decoders.map WordRow.read := ww
  have octets : decoders.map (WordRow.octets (256 : F)⁻¹) = groups.map Group.octets := oo
  obtain ⟨packets,got,count,callsFit,wordsFit⟩ := admissible_placement_heights run (.refl _)
  cases Option.some.inj (observed.symm.trans got)
  have spanCount : spans.length = callCount := by
    simpa only [spans,batch,List.length_map,WriteBuffer.packetRows_length observed,callCount] using count.symm
  have readCount : words.length = wordCount := WriteBuffer.packetRows_words observed
  have requestCount : requests.length = callCount := by simp only [requests,inputs,List.length_map,callCount]
  have decoderCount : decoders.length = wordCount := by
    have eqs := congrArg List.length reads
    simpa only [List.length_map,readCount] using eqs.symm
  have dispatchCount : dispatches.length = callCount := by simp only [dispatches,callCount,inputs,List.length_map]
  have groupCount : groups.length = wordCount := placementGroups_length streams entries
  have hc : WitnessGeneration.demandHeight callCount ≤ UInt64.size := callsFit.trans (by decide)
  have hw : WitnessGeneration.demandHeight wordCount ≤ UInt64.size := wordsFit.trans (by decide)
  let bounds : EffectFits events entries streams := ⟨spanCount ▸ hc,readCount ▸ hw,requestCount ▸ hc,
    decoderCount ▸ hw,dispatchCount ▸ hc,groupCount ▸ hw⟩
  have requestHonest : ∀ r ∈ requests, r.Valid := by
    intro r mem
    obtain ⟨d,original,rfl⟩ := List.mem_map.mp mem
    obtain ⟨e,used,rfl⟩ := List.mem_map.mp original
    exact reqValid _ used
  let wordHonest := fun (r : WordRow F) => r.read.value.isU64 ∧ r.low = (U16toU8OperationSafe.populate r.read.value).low_bytes
  have decoderHonest : ∀ r ∈ decoders, wordHonest r := by
    intro r mem
    obtain ⟨e,_,used⟩ := List.mem_flatMap.mp mem
    exact e.decoderRows_honest data (.empty _) _ used
  have capC : 2 * WitnessGeneration.demandHeight callCount < SP1Prime :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 callsFit) (by decide)
  have capW : 2 * WitnessGeneration.demandHeight wordCount < SP1Prime :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 wordsFit) (by decide)
  refine ⟨bounds,?_,?_,?_,?_,?_,?_,?_⟩
  · have good := request_checked requests data bounds.requests requestHonest
    rw [requestCount] at good
    exact good
  · have good := octet_checked decoders data bounds.decoders decoderHonest
    rw [decoderCount] at good
    exact good
  · have good := dispatch_checked dispatches data bounds.dispatches honest.dispatches
    rw [dispatchCount] at good
    exact good
  · apply join WriteBuffer.effectHeaderChannel spans requests WriteBuffer.Span.header Request.header ?_ (requestTable_headers requests data bounds.requests) headers (congrArg _ spanCount) capC
    simpa only [← List.map_eq_flatMap] using WriteBuffer.spanTable_effect_headers spans data bounds.spans
  · apply join WriteBuffer.wordChannel words decoders WriteBuffer.Step.read WordRow.read ?_ (octetTable_words decoders data bounds.decoders) reads (congrArg _ readCount) capW
    simpa only [← List.map_eq_flatMap] using WriteBuffer.wordTable_values words data bounds.words
  · exact join requestChannel requests dispatches id Dispatch.request (requestTable_requests requests data bounds.requests) (dispatchTable_requests dispatches data bounds.dispatches)
      (List.map_id _) (congrArg _ requestCount) capC
  · exact join octetsChannel decoders groups (WordRow.octets (256 : F)⁻¹) Group.octets (octetTable_octets decoders data bounds.decoders) (groupTable_octets groups data bounds.groups)
      octets (congrArg _ decoderCount) capW

/-- A full native execution supplies its own collector result and all observer tables on that single result. -/
theorem native_collector_effect_tables {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers) (data : ProverData F) :
    ∃ entries, native? image source events readers = some entries ∧
      ∃ bounds : EffectFits events entries (.fromEndpoints source.host target.host), bounds.Realized data := by
  obtain ⟨entries,emitted,_⟩ := native_inputs run readers
  exact ⟨entries,emitted,native_effect_tables run readers emitted data⟩

end SP1Clean.WriteEffects.Witness
