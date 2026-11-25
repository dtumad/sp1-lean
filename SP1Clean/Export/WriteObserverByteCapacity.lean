import SP1Clean.Export.WriteObserverByteReaders
import SP1Clean.Export.WriteObserverRows
import SP1Clean.Proofs.Completeness.HintQueuePublishedHistory
import SP1Clean.Proofs.Completeness.HintQueueSnapshot
import ToClean.Air.DemandHeightInterval

/-! # Exact Byte demand of the mixed native observer

The span and dispatcher share a call height. The buffer word and octet decoder share an
aligned-read height. The allocation step uses the padded number of fresh nodes, including
nodes subsequently consumed by the same execution.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics Machine TraceGen FormalModel.Shard WriteAllocation WriteEffects.Witness WitnessGeneration
private abbrev F := ZMod SP1Prime

/-- Physical Byte occurrences computed from the chronological observer inputs. -/
def observerByteSites (entries : List Entry) : Nat :=
  14 * demandHeight (inputs entries).packets.length +
    7 * demandHeight (WriteObservations.wordProbes (inputs entries).packets) +
    3 * demandHeight (inputs entries).nodes.length

/-- The actual generated rows attain the count, including the complete zero-weight padding
of each demand bucket. Unused fixed tables contribute zero at every physical height. -/
theorem compiled_observer_byte_count (image : ProgramImage) {source target : ExecutionSnapshot}
    (final : HostHintQueue.State F) {events : List ExecutionEvent} {entries : List Entry}
    (cap : EffectFits events entries (.fromEndpoints source.host target.host)) (s : SixTables entries source.host target.host)
    (metadata : Table F) (data : ProverData F) (realized : cap.Realized data)
    (front hints plans : List (Table F)) {a b c : Nat}
    (heights : front.map Table.length = [a, b, c, demandHeight (inputs entries).packets.length,
      demandHeight (WriteObservations.wordProbes (inputs entries).packets)])
    (queue : hints.length = 2) (last : plans.length = 2)
    (registered : (front ++ fundedSuffix s data (effectMiddle cap data metadata) hints plans).map Table.component = tables source target) :
    ((front ++ fundedSuffix s data (effectMiddle cap data metadata) hints plans).flatMap
      (·.interactionsWith Channels.byteChannel.toRaw)).length = observerByteSites entries := by
  rw [generated_byte_count image final _ registered]
  obtain ⟨_,octets,dispatch,_⟩ := realized
  obtain ⟨h₁,h₂,rfl⟩ := List.length_eq_two.mp queue
  obtain ⟨p₁,p₂,rfl⟩ := List.length_eq_two.mp last
  have nodeHeight : (s.nodes data).length = demandHeight (inputs entries).nodes.length :=
    (Table.ofInputs_length (WriteAllocation.stepComponent (p := SP1Prime)) (guardedRows (inputs entries).nodes)
      data ((guardedRows_length _).trans_le s.nodeFit) (fun _ => trivial)).trans (guardedRows_length _)
  simp only [observerByteWidths, fundedSuffix, effectMiddle, List.map_append, heights, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, Nat.mul_zero, Nat.add_zero, Nat.zero_add, octets.2.2.2, dispatch.2.2.2,
    nodeHeight, observerByteSites]
  omega

/-- The number of emitted allocation steps is the cumulative allocation resource, even
when subsequent HINT_READ calls pop nodes before the final snapshot. -/
theorem observer_allocation_count {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries) :
    (inputs entries).nodes.length = executionResources (policy SP1Prime image) image.program source.realize events .allocatedHints := by
  obtain ⟨cursor, _, done, size, _⟩ := admissibleExecution_hintSnapshot run
  have count := congrArg List.length (native_publication_range run readers collected done)
  simpa only [inputs, List.length_map, List.length_range', HintQueue.ofList_size, size, Nat.add_sub_cancel_left] using count

/-- Preset reservation from real event, tick, byte, allocation and historical queue ceilings.
Each of the three independent demands is rounded with the installed scheduler. -/
def observerByteBudget (limits : ResourceLimits) : Nat :=
  let calls := min limits.events (limits.ticks / 264)
  let words := (limits.readBytes + 14 * calls) / 8
  let nodes := min limits.allocatedHints ((limits.boundaryBytes + limits.writeBytes - 125) / 8)
  14 * demandHeight calls + 7 * demandHeight words + 3 * demandHeight nodes

/-- The semantic resource contract implies the observer reservation for every collected tape. -/
theorem observerByteSites_le_budget {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent} (run : AdmissibleExecution limits SP1Prime image source target events)
    (limitsFit : limits.LE (.native SP1Prime)) (readers : Readers) {entries : List Entry}
    (collected : native? image source events readers = some entries) : observerByteSites entries ≤ observerByteBudget limits := by
  let native := run.mono limitsFit
  obtain ⟨actual, built, _, observed, _⟩ := native_inputs native readers
  cases Option.some.inj (collected.symm.trans built)
  obtain ⟨bytes, ticks, words⟩ := WriteObservations.packets_cost run.1.2 observed
  have tickLimit := run.2.2.1 .ticks
  rw [run.1.2.resources_ticks] at tickLimit
  have readLimit : WriteObservations.requestedBytes (inputs entries).packets ≤ limits.readBytes := bytes.le.trans (run.2.2.1 .readBytes)
  have eventLimit := (WriteObservations.packets_length observed).le.trans (List.countP_le_length.trans run.work.1)
  have calls : (inputs entries).packets.length ≤ min limits.events (limits.ticks / 264) := by
    apply le_min eventLimit
    exact (Nat.le_div_iff_mul_le (by decide)).mpr ((Nat.mul_comm ..) ▸ ticks.trans tickLimit)
  have guest : WriteObservations.wordProbes (inputs entries).packets ≤
      (limits.readBytes + 14 * min limits.events (limits.ticks / 264)) / 8 := by omega
  have allocated := (observer_allocation_count native readers collected).le.trans (run.2.2.1 .allocatedHints)
  have stored := native_node_count native readers collected
  have charged := word_charge run limitsFit readers collected
  have nodes : (inputs entries).nodes.length ≤ min limits.allocatedHints ((limits.boundaryBytes + limits.writeBytes - 125) / 8) :=
    le_min allocated (by omega)
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 14 (demandHeight_mono calls))
    (Nat.mul_le_mul_left 7 (demandHeight_mono guest))) (Nat.mul_le_mul_left 3 (demandHeight_mono nodes))

end SP1Clean.Export.WriteObservationAssembly
