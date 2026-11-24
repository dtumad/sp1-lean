import SP1Clean.Proofs.Completeness.WriteAllocationTableHandoff
import SP1Clean.Proofs.Completeness.WriteWitnessPosition
import SP1Clean.Proofs.Completeness.HistoricalHintCapacity

/-! # Physical allocation tables for the actual mixed WRITE collector

The four tables use the node and word positions emitted at a genuine queue cut. The post-call
persistent store pays for their active words, including retired nodes and the padding word of
every aligned or empty buffer.
-/

namespace SP1Clean.WriteAllocation
open Circuit Air.Flat Semantics HintQueue Machine TraceGen FormalModel.Shard

private abbrev F := ZMod SP1Prime

/-- Real component constraints, guarantees and the three internal protocol balances of four
once-padded WRITE allocation tables. -/
def PhysicalTables (openings : List (Open F)) (nodes : List (Step F)) (seeds : List (Contents F))
    (words : List (Words.Row F)) (data : ProverData F) : Prop :=
  ∃ hc hn hs hw,
    let call := openTable openings data hc
    let steps := stepTable nodes data hn
    let starts := Words.seedTable seeds data hs
    let body := Words.wordTable words data hw
    call.Constraints ∧ call.Guarantees ∧ steps.Constraints ∧ steps.Guarantees ∧
    starts.Constraints ∧ starts.Guarantees ∧ body.Constraints ∧ body.Guarantees ∧
    LogUpBalanced (call.interactionsWith cursorChannel.toRaw ++ steps.interactionsWith cursorChannel.toRaw) ∧
    LogUpBalanced (steps.interactionsWith contentsChannel.toRaw ++ starts.interactionsWith contentsChannel.toRaw) ∧
    LogUpBalanced (starts.interactionsWith Words.cursorChannel.toRaw ++ body.interactionsWith Words.cursorChannel.toRaw)

/-- Specialize the physical construction to one collected allocation batch. -/
def BatchRows.Tables (r : BatchRows) (data : ProverData F) : Prop :=
  let nodes := r.nodes.map NodeRows.step
  PhysicalTables [r.opening] nodes (nodes.map Step.contents) (r.nodes.flatMap NodeRows.words) data

/-- A generated allocation opening and all its actual node/seed/word rows have valid physical
tables and closed private ledgers. The total word bound is on the immutable post-call store. -/
theorem Batch.rows_tables (batch : Batch) (previous clock : Nat) (before after : Store × Nat)
    (readers : Readers) (data : ProverData F) (issued : batch.Publishes clock before after.1)
    (valid : (batch.openRow previous clock before.1 before.2).Valid)
    (first : (batch.openRow previous clock before.1 before.2).first = batch.cursorAt clock before.2 before.1.size 0)
    (last : (batch.openRow previous clock before.1 before.2).last =
      batch.cursorAt clock before.2 before.1.size batch.buffers.length)
    (stored : after = prepend before.1 before.2 batch.buffers)
    (sizes : ∀ b ∈ batch.buffers, b.length < 2^48) (space : before.1.size + batch.buffers.length < 2^48)
    (paid : storedWordCount after.1 ≤ 2^29) : (batch.rows previous clock before readers).Tables data := by
  let rows := batch.rows previous clock before readers
  let steps := batch.steps clock before.1 before.2 readers.nodes
  let pairs := steps.zip batch.buffers.reverse
  let build := fun x : Step F × Bytes => nodeRows readers x.1 x.2
  have mapped : rows.nodes = pairs.map build := List.map_uncurry_zip_eq_zipWith.symm
  have eqSteps : rows.nodes.map NodeRows.step = steps := by
    rw [mapped,List.map_map]
    exact List.map_fst_zip (by simp [steps,Batch.steps_length])
  have payloads : pairs.map Prod.snd = batch.buffers.reverse :=
    List.map_snd_zip (by simp [steps,Batch.steps_length])
  have facts (x : Step F × Bytes) (mem : x ∈ pairs) :
      x.1.Valid ∧ x.1.contents.length = Address.ofNat x.2.length ∧ x.2 ∈ batch.buffers := by
    obtain ⟨i,atRow⟩ := List.mem_iff_getElem?.mp mem
    obtain ⟨step,bytes⟩ := List.getElem?_zip_eq_some.mp atRow
    have inside : i < batch.buffers.length := by simpa using (List.getElem?_eq_some_iff.mp bytes).1
    obtain ⟨node,found,ok,_,_,_,len,_⟩ := issued readers.nodes ⟨i,inside⟩
    have eq : node = x.1 := Option.some.inj (found.symm.trans step)
    have same := List.getElem?_eq_getElem (l := batch.buffers.reverse) (by simpa : i < batch.buffers.reverse.length)
    have payload := Option.some.inj (same.symm.trans bytes)
    exact ⟨eq ▸ ok,eq ▸ payload ▸ len,List.mem_reverse.mp (List.mem_of_getElem? bytes)⟩
  have sizesAgree : (rows.nodes.flatMap NodeRows.words).length = (batch.buffers.map wordCount).sum := by
    rw [mapped,List.length_flatMap,List.map_map]
    change (pairs.map (fun x => (nodeRows readers x.1 x.2).words.length)).sum = _
    simp only [nodeRows,Words.walk_length]
    change (pairs.map (wordCount ∘ Prod.snd)).sum = _
    rw [← List.map_map (f := Prod.snd) (g := wordCount),payloads,List.map_reverse,List.sum_reverse]
  have bound : (batch.buffers.map wordCount).sum ≤ 2^29 := by
    simp only [stored,storedWordCount,prepend_bytes,List.map_append,List.map_reverse,List.sum_append,List.sum_reverse] at paid
    omega
  have hc : WitnessGeneration.demandHeight [rows.opening].length ≤ UInt64.size := (by decide : WitnessGeneration.demandHeight 1 ≤ UInt64.size)
  have hn : WitnessGeneration.demandHeight (rows.nodes.map NodeRows.step).length ≤ UInt64.size := by
    apply (WitnessGeneration.demandHeight_le_pow (exponent := 48) ?_).trans (by decide)
    rw [eqSteps,Batch.steps_length]
    omega
  have hs : WitnessGeneration.demandHeight ((rows.nodes.map NodeRows.step).map Step.contents).length ≤ UInt64.size := by
    simpa only [List.length_map] using hn
  have hw : WitnessGeneration.demandHeight (rows.nodes.flatMap NodeRows.words).length ≤ UInt64.size :=
    (WitnessGeneration.demandHeight_le_pow (sizesAgree ▸ bound)).trans (by decide)
  have openOK := openTable_valid [rows.opening] (fun r mem => List.mem_singleton.mp mem ▸ valid) data hc
  have nodeOK := stepTable_valid (rows.nodes.map NodeRows.step) (by
    rw [mapped,List.map_map]; intro r m; obtain ⟨x,mem,rfl⟩ := List.mem_map.mp m; exact (facts x mem).1) data hn
  have seedOK := Words.seedTable_valid _ data hs
  have wordOK : (Words.wordTable (rows.nodes.flatMap NodeRows.words) data hw).Constraints ∧
      (Words.wordTable (rows.nodes.flatMap NodeRows.words) data hw).Guarantees := by
    apply Table.ofInputs_valid
    apply WitnessGeneration.guardedRows_all Words.Row.Valid
    intro r mem
    obtain ⟨node,atNode,inNode⟩ := List.mem_flatMap.mp mem
    exact (batch.rows_valid previous clock before after.1 issued readers space sizes node atNode).2 r inNode
  refine ⟨hc,hn,hs,hw,openOK.1,openOK.2,nodeOK.1,nodeOK.2,seedOK.1,seedOK.2,wordOK.1,wordOK.2,?_,
    contents_balanced _ data hn hs,?_⟩
  · have chain := batch.steps_walk clock before after.1 issued readers.nodes
    rw [← first,← last] at chain
    change Soundness.Walk.IsWalk _ rows.opening.first rows.opening.last steps at chain
    rw [← eqSteps] at chain
    have raw := batch_cursor [rows] BatchRows.opening (fun a => a.nodes.map NodeRows.step)
      (fun a member => List.mem_singleton.mp member ▸ chain) data hc (by simpa only [List.flatMap_singleton] using hn)
    simpa only [List.map_cons,List.map_nil,List.flatMap_singleton,rows] using raw
  · let br := fun (x : Step F × Bytes) (i : Nat) => readers.blocks (Words.populate x.1.contents x.2 i 0 0).direct
    let wr := fun (x : Step F × Bytes) (i : Nat) => readers.words (Words.populate x.1.contents x.2 i 0 0).word
    have seedEq : (rows.nodes.map NodeRows.step).map Step.contents = pairs.map (fun x => x.1.contents) := by
      rw [mapped,List.map_map,List.map_map]
      rfl
    have wordEq : rows.nodes.flatMap NodeRows.words =
        pairs.flatMap (fun x => Words.walk x.1.contents x.2 (br x) (wr x)) := by rw [mapped,List.flatMap_map]; rfl
    change LogUpBalanced ((Words.seedTable ((rows.nodes.map NodeRows.step).map Step.contents) data hs).interactionsWith _ ++
      (Words.wordTable (rows.nodes.flatMap NodeRows.words) data hw).interactionsWith _)
    have raw := Words.batch_cursor pairs (fun x => x.1.contents) Prod.snd br wr (fun x mem => (facts x mem).2.1) data
      (seedEq ▸ hs) (wordEq ▸ hw)
    simpa only [← seedEq,← wordEq] using raw

end SP1Clean.WriteAllocation
namespace SP1Clean.WriteEffects.Witness
open Semantics Machine FormalModel.Shard TraceGen WriteAllocation HintQueue
private abbrev F := ZMod SP1Prime

private theorem tables_at {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    (data : ProverData F) {event : ExecutionEvent} {cut : Nat} (present : events[cut]? = some event)
    {entry : Entry} (emitted : position image source events readers event cut = some entry) :
    ∀ rows ∈ entry.allocation, rows.Tables data := by
  have active := (native_position_active run readers present).1
  rw [emitted] at active
  cases event with
  | ordinary => contradiction
  | syscall call =>
    have write : call.rawCode = SyscallKind.write.code := of_decide_eq_true active.symm
    obtain ⟨current,_,cursor,after,length,buffer,_,reached,_,beforeStore,afterStore,read,found,_,_,_,allocates,ready⟩ :=
      native_position run readers present write
    cases Option.some.inj (emitted.symm.trans found)
    intro rows occurs
    change entry.allocation = some rows at occurs
    rw [allocates,Option.map_eq_some_iff] at occurs
    obtain ⟨batch,selected,rfl⟩ := occurs
    have certified := ready batch selected
    obtain ⟨_,actual,_,_,observed,_,_,_,_,_,_,_,_,budget,_⟩ := admissibleExecution_historicalHintCapacity run (cut+1)
    cases Option.some.inj (afterStore.symm.trans observed)
    have width : SP1Prime < 2^31 := by decide
    have paid : storedWordCount after.1 ≤ 2^29 := by omega
    obtain ⟨_,_,_,_,_,_,atStart,_,sameRead,sameStore,_,_,_,_,eligible⟩ := native_store_at run present write
    cases Option.some.inj (reached.symm.trans atStart)
    cases Option.some.inj (read.symm.trans sameRead)
    cases Option.some.inj (beforeStore.symm.trans sameStore)
    obtain ⟨_,_,_,first,last,_⟩ := eligible batch selected
    exact batch.rows_tables _ _ cursor after readers data certified.publishes certified.valid first last certified.stored
      certified.capacity.2 certified.capacity.1 paid

/-- The single mixed replay supplies valid physical allocation tables for each allocating
WRITE in order, with all three local balance identities. Its native resource profile pays for
the complete padded word walk, including every empty node. -/
theorem native_allocation_tables {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers) (data : ProverData F) :
    ∃ entries, native? image source events readers = some entries ∧
      ∀ entry ∈ entries, ∀ rows ∈ entry.allocation, rows.Tables data := by
  obtain ⟨built,_⟩ := native_collect run readers
  refine ⟨_,built,?_⟩
  intro entry used
  obtain ⟨⟨event,cut⟩,indexed,found⟩ := List.mem_filterMap.mp used
  exact tables_at run readers data (List.mk_mem_zipIdx_iff_getElem?.mp indexed) found

end SP1Clean.WriteEffects.Witness
