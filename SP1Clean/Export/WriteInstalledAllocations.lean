import ToClean.Air.AppendedAuthentication
import SP1Clean.Export.WriteObservationBuild
import SP1Clean.Proofs.Completeness.WriteWitnessAllocationCounts

/-! # Physical closure of the four native WRITE allocation tables

The first fifteen observer components and the original supervisor are silent on the three
private allocation channels. Canonical rebinding therefore preserves the exact chronological
ledgers of the four constructed tables, including every inactive padding occurrence.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics Machine FormalModel.Shard WriteSourceRegistry WriteAllocation WriteEffects.Witness

private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}

attribute [local irreducible] base preprocessing withSources assembly

/-- The three internal protocols of the allocation call, node, contents seed and padded words. -/
def allocationProtocols : List (RawChannel F) := [cursorChannel.toRaw,contentsChannel.toRaw,Words.cursorChannel.toRaw]

/-- Physical tables in their installed order, with each family padded exactly once per shard. -/
def allocationTables (r : WriteEffects.Witness.Inputs) (data : ProverData F)
    (hc : WitnessGeneration.demandHeight r.openings.length ≤ UInt64.size)
    (hn : WitnessGeneration.demandHeight r.nodes.length ≤ UInt64.size)
    (hs : WitnessGeneration.demandHeight r.contents.length ≤ UInt64.size)
    (hw : WitnessGeneration.demandHeight r.words.length ≤ UInt64.size) : List (Table F) :=
  [openTable r.openings data hc,stepTable r.nodes data hn,Words.seedTable r.contents data hs,Words.wordTable r.words data hw]

private theorem earlier_silent (earlier : List (Table F)) (registered : earlier.map Table.component = (tables source target).take 15)
    (ch : RawChannel F) (member : ch ∈ allocationProtocols) : earlier.flatMap (·.interactionsWith ch) = [] := by
  have absent : ch.name ∉ ((tables source target).take 15).flatMap (fun c => c.circuit.channels.map RawChannel.name) := by
    simp only [allocationProtocols,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> exact of_decide_eq_true rfl
  apply List.flatMap_eq_nil_iff.mpr
  intro t used
  apply t.interactionsWith_nil_of_channel_not_mem
  exact fun here => absent (List.mem_flatMap.mpr ⟨t.component, registered ▸ List.mem_map_of_mem used, List.mem_map_of_mem here⟩)

private theorem quiet (t : Table F) (ch : RawChannel F) (absent : ch.name ∉ t.component.circuit.channels.map RawChannel.name) :
    t.interactionsWith ch = [] :=
  t.interactionsWith_nil_of_channel_not_mem (fun mem => absent (List.mem_map_of_mem mem))

/-- The same native execution that generates the four tables pays Clean's occurrence bound
and supplies all active matches on their three full ensemble ledgers. Earlier generators may
be installed afterwards. Their registration determines complete silence on these channels. -/
theorem native_installed_allocation_matches {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers) (data : ProverData F) :
    ∃ entries, native? image source events readers = some entries ∧
      ∃ hc hn hs hw, let block := allocationTables (inputs entries) data hc hn hs hw
      ∀ (baseWitness : EnsembleWitness (base image source target final)) (earlier : List (Table F))
        (registered : earlier.map Table.component = (tables source target).take 15),
        let full := withPublicChecks (build baseWitness (earlier ++ block) (by
          rw [List.map_append,registered,show block.map Table.component = (tables source target).drop 15 from rfl,List.take_append_drop]))
        ∀ ch ∈ allocationProtocols, (Balance.logUp (F := F)).fits (full.interactionsWith ch).length = true ∧
          BalancedInteractions (full.interactionsWith ch) := by
  obtain ⟨entries,built,hc,hn,hs,hw,paid⟩ := native_private_matches run readers data
  refine ⟨entries,built,hc,hn,hs,hw,?_⟩
  dsimp only
  intro baseWitness earlier registered ch member
  have fresh : ch ∈ channels := by
    simp only [allocationProtocols,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [channels]
  have silent : ch.name ∉ [(WriteEffects.cursorChannel (p := SP1Prime)).name,(WriteEffects.closeChannel (p := SP1Prime)).name] := by
    simp only [allocationProtocols,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  rw [withPublicChecks_ledger _ ch (protocol_installed image source target final ch fresh) silent,
    build_ledger, (installSources baseWitness).interactionsWith_nil_of_not_registered _ (protocol_fresh image source target final ch fresh),
    List.nil_append,List.flatMap_append,earlier_silent earlier registered ch member,List.nil_append]
  let r := inputs entries
  let call := openTable r.openings data hc
  let node := stepTable r.nodes data hn
  let seed := Words.seedTable r.contents data hs
  let word := Words.wordTable r.words data hw
  let block := [call,node,seed,word]
  change (Balance.logUp (F := F)).fits (block.flatMap (·.interactionsWith ch)).length = true ∧ BalancedInteractions (block.flatMap (·.interactionsWith ch))
  simp only [allocationProtocols,List.mem_cons,List.not_mem_nil,or_false] at member
  dsimp only at paid
  rcases member with rfl | rfl | rfl
  · simp only [block,List.flatMap_cons,List.flatMap_nil, quiet seed cursorChannel.toRaw (of_decide_eq_true rfl),
      quiet word cursorChannel.toRaw (of_decide_eq_true rfl),List.append_nil]
    exact paid _ (List.Mem.head _)
  · simp only [block,List.flatMap_cons,List.flatMap_nil, quiet call contentsChannel.toRaw (of_decide_eq_true rfl),
      quiet word contentsChannel.toRaw (of_decide_eq_true rfl),List.nil_append,List.append_nil]
    exact paid _ (List.Mem.tail _ (List.Mem.head _))
  · simp only [block,List.flatMap_cons,List.flatMap_nil, quiet call Words.cursorChannel.toRaw (of_decide_eq_true rfl),
      quiet node Words.cursorChannel.toRaw (of_decide_eq_true rfl),List.nil_append,List.append_nil]
    exact paid _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

end SP1Clean.Export.WriteObservationAssembly
