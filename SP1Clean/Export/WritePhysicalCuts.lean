import SP1Clean.Export.WriteMemoryRecordChain
import SP1Clean.Proofs.Completeness.MemoryVersionHistory

/-! # Read-back values at cuts of the genuine physical Memory chain

The interval on a published predecessor ends at the owner's incoming CPU cut, refresh or
finalizer. At the exact time of a read-back or refresh the old and new words agree. Hence
the inclusive read-back convention computes the same word as chronological Memory replay.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Channels Semantics Soundness HostHintReadCPU NativeCore TimedGrounding WriteProbe WriteProbe.AccessInventory
open TraceGen (MemoryHistoryAccess)
open TraceGen.MemoryHistoryAccess (ofRecords heldAt)

private abbrev Fp := ZMod SP1Prime
private abbrev Pair := MemoryRecordChain.Pair SP1Prime

private theorem first_le_sources (first last : MemoryMsg Fp) (path : List Pair) (walk : Walk.IsWalk id first last path)
    (strict : ∀ e ∈ path, MemoryMsg.timeNat e.1 < MemoryMsg.timeNat e.2) :
    ∀ e ∈ path, MemoryMsg.timeNat first ≤ MemoryMsg.timeNat e.1 := by
  induction path generalizing first with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨rfl, rest⟩ := walk
    intro e member
    rcases List.mem_cons.mp member with rfl | inside
    · rfl
    · exact (strict head (List.mem_cons_self ..)).le.trans
        (ih _ rest (fun other h => strict other (List.mem_cons_of_mem _ h)) e inside)

private theorem heldAt_start (first last : MemoryMsg Fp) (path : List Pair) (walk : Walk.IsWalk id first last path)
    (strict : ∀ e ∈ path, MemoryMsg.timeNat e.1 < MemoryMsg.timeNat e.2) (time : ℕ) (early : time ≤ MemoryMsg.timeNat first) :
    heldAt first.value.toBitVec64 time (path.map ofRecords) = first.value.toBitVec64 := by
  cases path with
  | nil => rfl
  | cons e rest =>
    have earlier := early.trans_lt (walk.1 ▸ strict e (List.mem_cons_self ..))
    simpa only [List.map_cons, heldAt, ofRecords] using ite_eq_left (α := BitVec 64) earlier

private theorem heldAt_edge (first last : MemoryMsg Fp) (path : List Pair) (walk : Walk.IsWalk id first last path)
    (strict : ∀ e ∈ path, MemoryMsg.timeNat e.1 < MemoryMsg.timeNat e.2) (edge : Pair) (inside : edge ∈ path)
    (time : ℕ) (after : MemoryMsg.timeNat edge.1 ≤ time) (before : time ≤ MemoryMsg.timeNat edge.2)
    (exactTime : time = MemoryMsg.timeNat edge.2 → edge.2.value = edge.1.value) :
    heldAt first.value.toBitVec64 time (path.map ofRecords) = edge.1.value.toBitVec64 := by
  induction path generalizing first with
  | nil => contradiction
  | cons head rest ih =>
    obtain ⟨rfl, tail⟩ := walk
    simp only [id_eq] at tail
    have later e (member : e ∈ rest) := strict e (List.mem_cons_of_mem _ member)
    change (if time < MemoryMsg.timeNat head.2 then head.1.value.toBitVec64 else
      heldAt head.2.value.toBitVec64 time (rest.map ofRecords)) = _
    rcases List.mem_cons.mp inside with rfl | remaining
    · rcases before.lt_or_eq with lt | eq
      · rw [ite_eq_left lt]
      · rw [ite_eq_right (by omega), heldAt_start _ _ _ tail later time before, exactTime eq]
    · have lower := first_le_sources _ _ _ tail later edge remaining
      rw [ite_eq_right (by omega)]
      exact ih _ tail later remaining

private theorem heldAt_suffix (first last : MemoryMsg Fp) (path : List Pair) (walk : Walk.IsWalk id first last path)
    (strict : ∀ e ∈ path, MemoryMsg.timeNat e.1 < MemoryMsg.timeNat e.2) (time : ℕ) (after : MemoryMsg.timeNat last ≤ time) :
    heldAt first.value.toBitVec64 time (path.map ofRecords) = last.value.toBitVec64 := by
  induction path generalizing first with
  | nil => rw [show first = last from walk]; rfl
  | cons head rest ih =>
    have bound := (walk_rank_bound id MemoryMsg.timeNat walk (fun e member => (strict e member).le)).2 head (List.mem_cons_self ..)
    simp only [id_eq] at bound
    change (if time < MemoryMsg.timeNat head.2 then _ else _) = _
    rw [ite_eq_right (by omega)]
    exact ih _ walk.2 (fun e member => strict e (List.mem_cons_of_mem _ member))

private theorem touch_end {time : ℕ} {t : Touch SP1Prime} (valid : TouchOK time t.1 t.2) :
    time ≤ MemoryMsg.timeNat t.2 ∧ (time = MemoryMsg.timeNat t.2 → t.2.value = t.1.1.value) := by
  refine ⟨valid.push_lo, fun same => ?_⟩
  rcases valid.push_kind with read | write
  · exact read.1
  · have positive : 0 < writeOffset (MemoryMsg.locOf t.2) := by cases MemoryMsg.locOf t.2 <;> simp
    omega

/-- Every actual ordinary or host Memory predecessor is paired with a physical successor
on its owning row at the checked incoming clock. -/
theorem paired_predecessor (data : ProverData Fp) (cpu : List (ExecutionRow SP1Prime))
    (words : List (HintReadCoverage.Row (p := SP1Prime))) (aligned : List (RowFacts SP1Prime))
    (paired : List.Forall₂ AlignedFacts aligned (cpu.map (ExecutionRow.facts data)))
    (access : ∀ row ∈ words, HostRamTouches.AccessFacts (HintReadCoverage.rowInput row).ram)
    (refresh : List Pair) {event : ExecutionRow SP1Prime} (member : event ∈ cpu)
    {prior : MemoryMsg Fp} {time : ℕ} (pulled : (prior, time) ∈ (eventFacts data words event).memPulls) :
    let entries := MemoryRecordChain.pairs aligned ((cpu.flatMap (wordsAt data words)).map touch) refresh
    let clock := StateMsg.timeNat (event.edge data).1
    ∃ next, (prior, next) ∈ entries ∧ MemoryMsg.locOf prior = MemoryMsg.locOf next ∧
      clock ≤ MemoryMsg.timeNat next ∧ (clock = MemoryMsg.timeNat next → next.value = prior.value) := by
  intro entries clock
  rcases List.mem_append.mp pulled with original | host
  · obtain ⟨r, included, fits⟩ := forall₂_exists_left paired (event.facts data) (List.mem_map_of_mem member)
    have priorMem : prior ∈ r.memPulls.map Prod.fst := fits.memory.pulls.mem_iff.mpr (List.mem_map_of_mem (f := Prod.fst) original)
    have all : (rowTouches r).map Prod.fst = r.memPulls := List.map_fst_zip fits.touches.length_eq.le
    rw [← all, List.map_map] at priorMem
    obtain ⟨t, active, same⟩ := List.mem_map.mp priorMem
    change t.1.1 = prior at same
    subst prior
    have localOK := (List.forall₂_iff_zip.mp fits.touches).2 active
    have valid := localOK
    rw [fits.statePull] at valid
    have state : (event.edge data).1 = (event.facts data).statePull := congrArg Prod.fst (event.edge_eq_facts data)
    rw [← state] at valid
    refine ⟨t.2, List.mem_append_left _ (List.mem_map.mpr ⟨t, List.mem_append_left _ (List.mem_flatMap.mpr ⟨r, included, active⟩), rfl⟩),
      localOK.loc_eq.symm, touch_end valid⟩
  · obtain ⟨row, selected, same⟩ := List.mem_map.mp host
    have priorEq := congrArg Prod.fst same
    change (touch row).1.1 = prior at priorEq
    subst prior
    have facts := access row (List.mem_filter.mp selected).1
    have atClock := congrArg (fun key : Fp × Fp => clkNat key.1 key.2) (of_decide_eq_true (List.mem_filter.mp selected).2)
    change wordTime row = clock at atClock
    have valid : TouchOK clock (touch row).1 (touch row).2 := atClock ▸ facts.touch
    exact ⟨(touch row).2, List.mem_append_left _ (List.mem_map.mpr ⟨touch row, List.mem_append_right _
      (List.mem_map_of_mem (f := touch) (List.mem_flatMap.mpr ⟨event, member, selected⟩)), rfl⟩),
      facts.touch.loc_eq.symm, touch_end valid⟩

/-- Decode an observed three-field address with the original typed Memory decoder. -/
def keyLocation (key : fields 3 Fp) : MemLoc :=
  MemoryMsg.locOf (p := SP1Prime) ⟨0, 0, key[0], key[1], key[2], 0⟩

/-- A record with a unique location is its actual terminal frontier entry. -/
theorem head_at_unique (rows : List (MemoryMsg Fp)) (unique : (rows.map MemoryMsg.locOf).Nodup)
    {record : MemoryMsg Fp} (present : record ∈ rows) :
    (rows.filter (fun m => decide (MemoryMsg.locOf m = MemoryMsg.locOf record))).head? = some record := by
  let selected := rows.filter (fun m => decide (MemoryMsg.locOf m = MemoryMsg.locOf record))
  have found : record ∈ selected := List.mem_filter.mpr ⟨present, by simp⟩
  have count : selected.length ≤ 1 := pairwise_distinct_filter_length_le_one MemoryMsg.locOf rows _ (List.pairwise_map.mp unique)
  change selected.head? = some record
  generalize selected = result at found count ⊢
  cases result with
  | nil => simp_all
  | cons first tail =>
    cases tail with
    | nil => simpa using (List.mem_singleton.mp found).symm
    | cons second rest => simp at count

/-- The word at every queried clock is obtained from the same chronological replay
at the location, starting from the realized Sail source. A location with no physical
records has no authenticated query. -/
def CutHistory (entries : List Pair) (initial final : Option (MemoryMsg Fp)) (content : Option (BitVec 64))
    (query : ℕ → Word Fp → Prop) : Prop :=
  (initial = none ∧ final = none ∧ entries = [] ∧ ∀ time value, ¬query time value) ∨
    ∃ first last path, initial = some first ∧ final = some last ∧ content = some first.value.toBitVec64 ∧
      path.Perm entries ∧ Walk.IsWalk id first last path ∧ (path.map (fun e => MemoryMsg.timeNat e.2)).Pairwise (· < ·) ∧
      ∀ time value, query time value → heldAt first.value.toBitVec64 time (path.map ofRecords) = value.toBitVec64

private def HasProvider (entries : List Pair) (final : Option (MemoryMsg Fp)) (time : ℕ) (value : Word Fp) :=
  (∃ e ∈ entries, e.1.value = value ∧ MemoryMsg.timeNat e.1 ≤ time ∧ time ≤ MemoryMsg.timeNat e.2 ∧
    (time = MemoryMsg.timeNat e.2 → e.2.value = e.1.value)) ∨
  ∃ last, final = some last ∧ last.value = value ∧ MemoryMsg.timeNat last ≤ time

private theorem replay_of_chain {entries : List Pair} {initial final : Option (MemoryMsg Fp)} {content : Option (BitVec 64)}
    {query : ℕ → Word Fp → Prop} (history : MemoryRecordChain.History entries initial final)
    (authentic : ∀ first, initial = some first → content = some first.value.toBitVec64)
    (provider : ∀ time value, query time value → HasProvider entries final time value) : CutHistory entries initial final content query := by
  rcases history with ⟨noStart, noFinal, empty⟩ | ⟨first, last, path, start, finish, exhaustive, walk, ordered, strict⟩
  · refine Or.inl ⟨noStart, noFinal, empty, fun time value seen => ?_⟩
    rcases provider time value seen with ⟨e, inside, _⟩ | ⟨e, present, _⟩
    · simp [empty] at inside
    · simp [noFinal] at present
  refine Or.inr ⟨first, last, path, start, finish, authentic _ start, exhaustive, walk, ordered, fun time value seen => ?_⟩
  rcases provider time value seen with ⟨e, member, rfl, after, before, equal⟩ | ⟨record, endpoint, rfl, after⟩
  · exact heldAt_edge first last path walk strict e (exhaustive.mem_iff.mpr member) time after before equal
  · obtain rfl := Option.some.inj (finish.symm.trans endpoint)
    exact heldAt_suffix first _ path walk strict time after

variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State Fp}

private theorem physical_provider (core : EnsembleWitness (LocalCore.ensemble (p := SP1Prime) image source))
    (data : ProverData Fp) (words : List (HintReadCoverage.Row (p := SP1Prime))) (aligned : List (RowFacts SP1Prime))
    (paired : List.Forall₂ AlignedFacts aligned ((LocalCore.executionRows core).map (ExecutionRow.facts data)))
    (wordAccess : ∀ row ∈ words, HostRamTouches.AccessFacts (HintReadCoverage.rowInput row).ram)
    (finalUnique : ((FinalMemoryEnsemble.records (LocalCore.finalWitness core)).map MemoryMsg.locOf).Nodup)
    (record : Readback Fp) (clock : ℕ) (after : clkNat record.previousHigh record.previousLow ≤ clock)
    (before : clock ≤ clkNat record.currentHigh record.currentLow)
    (attached : (∃ event ∈ LocalCore.executionRows core, ∃ prior time, (prior, time) ∈ (eventFacts core.data words event).memPulls ∧
      record = AccessSupply.atClock (cpuClock core.data event) prior) ∨
      (∃ prior next, (prior, next) ∈ LocalCore.memoryRefreshes core ∧ record = AccessSupply.atClock (next.clk_high, next.clk_low) prior) ∨
      ∃ prior ∈ FinalMemoryEnsemble.records (LocalCore.finalWitness core), record = finalReadback prior) :
    let loc := keyLocation record.key
    let extra := ((LocalCore.executionRows core).flatMap (wordsAt data words)).map touch
    HasProvider (MemoryRecordChain.atLocation loc (MemoryRecordChain.pairs aligned extra (LocalCore.memoryRefreshes core)))
      (LocalCore.memoryFinalFrontier core loc) clock record.value := by
  rcases attached with ⟨event, member, prior, time, pulled, rfl⟩ | ⟨prior, next, member, rfl⟩ | ⟨prior, member, rfl⟩
  · rw [eventFacts_setData event core.data data words] at pulled
    obtain ⟨next, included, loc, upper, right⟩ := paired_predecessor data _ words aligned paired wordAccess _ member pulled
    change clock ≤ StateMsg.timeNat (event.edge core.data).1 at before
    rw [event.edge_setData core.data data] at before
    exact Or.inl ⟨(prior, next), List.mem_filter.mpr ⟨included, decide_eq_true loc.symm⟩, rfl, after,
      before.trans upper, fun same => right (Nat.le_antisymm upper (same ▸ before))⟩
  · have kept := LocalCore.memoryRefreshes_preserve core (prior, next) member
    exact Or.inl ⟨(prior, next), List.mem_filter.mpr ⟨List.mem_append_right _ member, decide_eq_true (congrArg Prod.fst kept).symm⟩,
      rfl, after, before, fun _ => (congrArg Prod.snd kept).symm⟩
  · exact Or.inr ⟨prior, head_at_unique _ finalUnique member, rfl, after⟩

/-- A positive original physical source covers this address, clock and word. -/
def QueryAt (tables : Source → Table Fp) (loc : MemLoc) (time : ℕ) (value : Word Fp) : Prop :=
  ∃ id record, Origin tables id record ∧ keyLocation record.key = loc ∧ clkNat record.previousHigh record.previousLow ≤ time ∧
    time ≤ clkNat record.currentHigh record.currentLow ∧ record.value = value

/-- Every authenticated WRITE read is the value held at its clock on the exhaustive
per-location Memory replay. The replay, its endpoints and the realized Sail seed are
fixed before the source table, word and observation clock are selected. -/
theorem physical_cut_values (valid : image.Valid) (witness : EnsembleWitness (HostObserved.ensemble image source target final))
    (checked : witness.Constraints) (packet : Table Fp) (installed : packet.component = WritePacket.component)
    (packetChecked : packet.Constraints) (balanced : BalancedInteractions
      (witness.interactionsWith HostCallChip.channel.toRaw ++ packet.interactionsWith HostCallChip.channel.toRaw))
    (cursor : witness.BalancedChannel HintReadWordChip.stateChannel.toRaw)
    (wordData : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees HostHintQueue.wordChannel.toRaw)
    (bytes : ∀ last, (raw witness (.host (.word last))).ChannelGuarantees byteChannel.toRaw)
    (ordering : LocalCore.OrderingChannels (HostFinalMemory.coreWitness (HostObserved.baseWitness witness)))
    (memory : witness.BalancedChannel memoryChannel.toRaw) (program : witness.BalancedChannel programChannel.toRaw)
    (boundaries : ∀ channel ∈ (OrderedBoundary.channel SnapshotMemoryEnsemble.channelName).toRaw ::
      (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw :: SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot,
      witness.BalancedChannel channel) :
    let core := HostFinalMemory.coreWitness (HostObserved.baseWitness witness)
    let boundary := HostFinalMemory.baseWitness (HostObserved.baseWitness witness)
    let cpu := LocalCore.executionRows core
    let words := TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view (HostHintReadLocal.wordTables (hostWitness witness))
    let additional := (cpu.flatMap (wordsAt boundary.data words)).map touch
    ∃ aligned, List.Forall₂ AlignedFacts aligned (cpu.map (ExecutionRow.facts boundary.data)) ∧
      ∀ loc, CutHistory (MemoryRecordChain.atLocation loc (MemoryRecordChain.pairs aligned additional (LocalCore.memoryRefreshes core)))
        (LocalCore.memoryInitialFrontier core loc) (LocalCore.memoryFinalFrontier core loc)
        (locContent source.sail.realize loc) (QueryAt (raw witness) loc) := by
  intro core boundary cpu words additional
  have hostChecked := HostHintQueueBoundary.projected_constraints _ (HostFinalMemory.baseWitness_constraints _ (HostObserved.baseWitness_constraints witness checked))
  have physical : core.Constraints := by exact HostLocalCore.localWitness_constraints _ hostChecked
  have membership (ch) (member : ch ∈ SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot) : core.BalancedChannel ch := by
    change BalancedInteractions ((HostFinalMemory.coreWitness (HostObserved.baseWitness witness)).interactionsWith ch)
    rw [core_membership_ledger witness ch member]
    exact boundaries ch (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  have finalOrder : (hostWitness witness).BalancedChannel (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw := by
    change BalancedInteractions ((hostWitness witness).interactionsWith _)
    rw [host_core_ledger witness _ (by simp [LocalCore.baseEnsemble])]
    exact boundaries _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have finalUnique := (HostLocalCore.final_records_canonical_nodup (hostWitness witness)
    (HostHintReadLocal.source_boundary_silent source _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) hostChecked ordering.byte finalOrder).2
  obtain ⟨aligned, paired, histories⟩ := physical_record_chains valid witness checked packet installed packetChecked balanced cursor wordData bytes ordering memory program boundaries
  refine ⟨aligned, paired, fun loc => replay_of_chain (histories loc) (fun _ held =>
    (LocalCore.memoryInitialFrontier_content_of_channels core physical ordering.sourceChecks ordering.byte membership held).2.2) ?_⟩
  rintro clock value ⟨id, record, origin, rfl, after, before, rfl⟩
  exact physical_provider core boundary.data words aligned paired (word_access witness checked bytes) finalUnique record clock after before
    (source_attribution witness checked packet installed packetChecked balanced cursor wordData bytes id record origin)

end SP1Clean.Export.WriteSourceRegistry
