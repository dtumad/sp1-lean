import SP1Clean.Proofs.Completeness.WriteWitnessAllocationTables
import SP1Clean.Proofs.Completeness.WriteWitnessAllocationCapacity

/-! # Four globally padded allocation tables of a native mixed shard

The chronological collector is run once. Each of its four physical input lists is padded
once. Cursor closures add over every opening and node, including repeated payloads. The final
store bounds the complete node, seed and word heights independently of how often it was popped.
-/

namespace SP1Clean.WriteEffects.Witness
open Circuit Air.Flat Semantics Machine TraceGen FormalModel.Shard WriteAllocation

private abbrev F := ZMod SP1Prime

private theorem open_sum (rows : List (Open F)) (data : ProverData F) (fit) (msg : Array F) :
    balanceOf ((openTable rows data fit).interactionsWith WriteAllocation.cursorChannel.toRaw) msg =
      balanceOf (rows.flatMap (fun r => openCursors (r,1))) msg := by
  rw [openTable_cursors,WitnessGeneration.guardedRows_balanceOf]
  simp only [openCursors,balanceOf_cons]
  simp [Channel.pulledIfValue,Channel.pushedIfValue,Interaction.signedMult,balanceOf]
  exact ite_self 0

private theorem node_sum (rows : List (Step F)) (data : ProverData F) (fit) (msg : Array F) :
    balanceOf ((stepTable rows data fit).interactionsWith WriteAllocation.cursorChannel.toRaw) msg =
      balanceOf (rows.flatMap (fun r => stepCursors (r,1))) msg := by
  rw [stepTable_cursors,WitnessGeneration.guardedRows_balanceOf]
  simp only [stepCursors,balanceOf_cons]
  simp [Channel.pulledIfValue,Channel.pushedIfValue,Interaction.signedMult,balanceOf]
  exact ite_self 0

private theorem seed_sum (rows : List (Contents F)) (data : ProverData F) (fit) (msg : Array F) :
    balanceOf ((Words.seedTable rows data fit).interactionsWith Words.cursorChannel.toRaw) msg =
      balanceOf (rows.flatMap (fun r => Words.seedCursors (r,1))) msg := by
  rw [Words.seedTable_cursors,WitnessGeneration.guardedRows_balanceOf]
  simp only [Words.seedCursors,balanceOf_cons]
  simp [Channel.pushedIfValue,Interaction.signedMult,balanceOf]
  exact ite_self 0

private theorem word_sum (rows : List (Words.Row F)) (data : ProverData F) (fit) (msg : Array F) :
    balanceOf ((Words.wordTable rows data fit).interactionsWith Words.cursorChannel.toRaw) msg =
      balanceOf (rows.flatMap (fun r => Words.wordCursors (r,1))) msg := by
  rw [Words.wordTable_cursors,WitnessGeneration.guardedRows_balanceOf]
  simp only [Words.wordCursors,balanceOf_cons]
  simp [Channel.pulledIfValue,Channel.pushedIfValue,Interaction.signedMult,balanceOf]

private theorem batch_sums (r : BatchRows) (data : ProverData F) (valid : r.Tables data) (msg : Array F) :
    balanceOf (openCursors (r.opening,1)) msg + balanceOf (r.nodes.flatMap (fun n => stepCursors (n.step,1))) msg = 0 ∧
    balanceOf (r.nodes.flatMap (fun n => Words.seedCursors (n.step.contents,1))) msg +
      balanceOf (r.nodes.flatMap (fun n => n.words.flatMap (fun w => Words.wordCursors (w,1)))) msg = 0 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,node,_,word⟩ := valid
  have left := node msg
  have right := word msg
  rw [balanceOf_append,open_sum,node_sum] at left
  rw [balanceOf_append,seed_sum,word_sum] at right
  simpa only [List.flatMap_singleton,List.flatMap_map,List.flatMap_assoc,Function.comp_def] using And.intro left right

private theorem sum_batches (xs : List BatchRows) (left right : BatchRows → List (Interaction F)) (msg : Array F)
    (each : ∀ r ∈ xs, balanceOf (left r) msg + balanceOf (right r) msg = 0) :
    balanceOf (xs.flatMap left) msg + balanceOf (xs.flatMap right) msg = 0 := by
  induction xs with
  | nil => simp [balanceOf]
  | cons x xs ih =>
    have head := each x List.mem_cons_self
    have tail := ih (fun r mem => each r (List.mem_cons_of_mem _ mem))
    simp only [List.flatMap_cons,balanceOf_append]
    linear_combination head + tail

private theorem handoff (nodes : List (Step F)) (seeds : List (Contents F))
    (same : seeds = nodes.map Step.contents) (data : ProverData F) (hn hs) :
    LogUpBalanced ((stepTable nodes data hn).interactionsWith contentsChannel.toRaw ++
      (Words.seedTable seeds data hs).interactionsWith contentsChannel.toRaw) := by
  subst seeds
  exact contents_balanced nodes data hn hs

private theorem assemble (entries : List Entry) (data : ProverData F) (valid : (inputs entries).Valid)
    (localTables : ∀ b ∈ entries.filterMap Entry.allocation, b.Tables data)
    (hc : WitnessGeneration.demandHeight (inputs entries).openings.length ≤ UInt64.size)
    (hn : WitnessGeneration.demandHeight (inputs entries).nodes.length ≤ UInt64.size)
    (hw : WitnessGeneration.demandHeight (inputs entries).words.length ≤ UInt64.size) :
    let r := inputs entries
    PhysicalTables r.openings r.nodes r.contents r.words data := by
  let r := inputs entries
  have hs : WitnessGeneration.demandHeight r.contents.length ≤ UInt64.size := by
    simpa only [r,valid.seeds,List.length_map] using hn
  have wordOK : (Words.wordTable r.words data hw).Constraints ∧ (Words.wordTable r.words data hw).Guarantees := by
    apply Table.ofInputs_valid
    exact WitnessGeneration.guardedRows_all Words.Row.Valid valid.words
  have callOK := openTable_valid _ valid.openings data hc
  have nodeOK := stepTable_valid _ valid.nodes data hn
  have seedOK := Words.seedTable_valid r.contents data hs
  refine ⟨hc,hn,hs,hw,callOK.1,callOK.2,nodeOK.1,nodeOK.2,seedOK.1,seedOK.2,wordOK.1,wordOK.2,?_,
    handoff r.nodes r.contents valid.seeds data hn hs,?_⟩
  · intro msg
    rw [balanceOf_append,open_sum,node_sum]
    have all := sum_batches (entries.filterMap Entry.allocation) _ _ msg (fun b mem => (batch_sums b data (localTables b mem) msg).1)
    simpa only [inputs,List.flatMap_map,List.flatMap_assoc,Function.comp_def] using all
  · intro msg
    rw [balanceOf_append,seed_sum,word_sum]
    have all := sum_batches (entries.filterMap Entry.allocation) _ _ msg (fun b mem => (batch_sums b data (localTables b mem) msg).2)
    simpa only [inputs,List.flatMap_map,List.flatMap_assoc,Function.comp_def] using all

/-- Every admitted native tape constructs four globally padded allocation tables satisfying
all constraints and guarantees and closing all three private transfer channels. Actual word
demand, and hence the node and seed demands, has a power-of-two ceiling of 2^29. -/
theorem native_allocation_assembly {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers) (data : ProverData F) :
    ∃ entries, native? image source events readers = some entries ∧
      let r := inputs entries
      PhysicalTables r.openings r.nodes r.contents r.words data ∧
        WitnessGeneration.demandHeight r.nodes.length ≤ 2^29 ∧ WitnessGeneration.demandHeight r.contents.length ≤ 2^29 ∧
        WitnessGeneration.demandHeight r.words.length ≤ 2^29 := by
  obtain ⟨entries,built,_,_,_,_,opens,valid⟩ := native_inputs run readers
  obtain ⟨other,found,perEntry⟩ := native_allocation_tables run readers data
  cases Option.some.inj (built.symm.trans found)
  have paid := native_word_capacity run readers built
  have bodies := WitnessGeneration.demandHeight_le_pow paid
  have nodes := WitnessGeneration.demandHeight_le_pow ((native_node_count run readers built).trans paid)
  have seeds : WitnessGeneration.demandHeight (inputs entries).contents.length ≤ 2^29 := by
    rw [valid.seeds,List.length_map]
    exact nodes
  have ticks := run.2.2.1 .events
  rw [run.1.2.resources_events] at ticks
  have hc : WitnessGeneration.demandHeight (inputs entries).openings.length ≤ UInt64.size := by
    apply (WitnessGeneration.demandHeight_le_pow (exponent := 21) ?_).trans (by decide)
    rw [opens]
    exact (List.countP_le_length ..).trans ticks
  refine ⟨entries,built,assemble entries data valid ?_ hc (nodes.trans (by decide)) (bodies.trans (by decide)),nodes,seeds,bodies⟩
  intro batch used
  obtain ⟨entry,atEntry,allocated⟩ := List.mem_filterMap.mp used
  exact perEntry entry atEntry batch allocated

end SP1Clean.WriteEffects.Witness
