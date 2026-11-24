import SP1Clean.Export.WritePhysicalCuts

/-! # Physical receipt coverage at incoming CPU cuts

The first later access to a location either belongs to a CPU row or is a refresh.
A CPU cut immediately preceding a write lies at or before that owner's incoming clock
by the eight-tick instruction phase. After the last access its original finalizer publishes.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Channels Semantics Soundness HostHintReadCPU NativeCore TimedGrounding WriteProbe WriteProbe.AccessInventory

private abbrev Fp := ZMod SP1Prime
private abbrev Pair := MemoryRecordChain.Pair SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State Fp}

private theorem first_later (first last : MemoryMsg Fp) (path : List Pair) (walk : Walk.IsWalk id first last path)
    (clock : ℕ) (after : MemoryMsg.timeNat first ≤ clock) :
    (∃ e ∈ path, MemoryMsg.timeNat e.1 ≤ clock ∧ clock < MemoryMsg.timeNat e.2) ∨ MemoryMsg.timeNat last ≤ clock := by
  induction path generalizing first with
  | nil => exact Or.inr ((show first = last from walk) ▸ after)
  | cons e rest ih =>
    by_cases before : clock < MemoryMsg.timeNat e.2
    · exact Or.inl ⟨e, List.mem_cons_self .., walk.1 ▸ after, before⟩
    rcases ih _ walk.2 (Nat.le_of_not_gt before) with ⟨edge, inside, lo, hi⟩ | suffix
    · exact Or.inl ⟨edge, List.mem_cons_of_mem _ inside, lo, hi⟩
    · exact Or.inr suffix

private theorem upper_of_window {cut owner endTime : ℕ} (cutPhase : activeClockPhase cut) (ownerPhase : activeClockPhase owner)
    (inside : cut < endTime) (endWindow : endTime ≤ owner + 4) : cut ≤ owner := by
  unfold activeClockPhase at cutPhase ownerPhase
  omega

private theorem cpu_phase (core : EnsembleWitness (LocalCore.ensemble (p := SP1Prime) image source))
    (checked : core.Constraints) (ordering : LocalCore.OrderingChannels core) (data : ProverData Fp)
    {event : ExecutionRow SP1Prime} (present : event ∈ LocalCore.executionRows core) :
    activeClockPhase (StateMsg.timeNat (event.edge data).1) ∧ StateMsg.timeNat (event.edge data).1 < 2 ^ 48 := by
  have high := (LocalCore.executionRows_good_of_orderingChannels core checked ordering present).1.1
  have clock := LocalCore.executionRows_clock_of_orderingChannels core checked ordering present
  rw [← event.edge_setData core.data data]
  refine ⟨clock.2.2.1, ?_⟩
  have low := clock.2.2.2
  unfold StateMsg.timeNat clkNat
  omega

/-- An original positive receipt over this decoded location at the specified physical cut. -/
def FundedAt (tables : Source → Table Fp) (loc : MemLoc) (time : ℕ) (r : Readback Fp) : Prop :=
  (1, r) ∈ records tables ∧ keyLocation r.key = loc ∧
    clkNat r.previousHigh r.previousLow ≤ time ∧ time ≤ clkNat r.currentHigh r.currentLow

private theorem cpu_receipt (w : EnsembleWitness (HostObserved.ensemble image source target final)) (checked : w.Constraints)
    (data : ProverData Fp) (cut : ℕ) (phase : activeClockPhase cut)
    {event : ExecutionRow SP1Prime} (member : event ∈ LocalCore.executionRows (HostFinalMemory.coreWitness (HostObserved.baseWitness w)))
    (ownerPhase : activeClockPhase (StateMsg.timeNat (event.edge data).1))
    (t : Touch SP1Prime) (valid : TouchOK (StateMsg.timeNat (event.edge data).1) t.1 t.2)
    (window : MemoryMsg.timeNat t.1.1 ≤ cut ∧ cut < MemoryMsg.timeNat t.2)
    (pulled : ∃ time, (t.1.1, time) ∈ (eventFacts data (TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view
      (HostHintReadLocal.wordTables (hostWitness w))) event).memPulls) :
    FundedAt (raw w) (MemoryMsg.locOf t.2) cut (AccessSupply.atClock (cpuClock data event) t.1.1) := by
  obtain ⟨time, member'⟩ := pulled
  exact ⟨event_predecessor w checked member data member', valid.loc_eq.symm, window.1, upper_of_window phase ownerPhase window.2 valid.push_hi⟩

private theorem edge_receipt (w : EnsembleWitness (HostObserved.ensemble image source target final)) (checked : w.Constraints)
    (ordering : LocalCore.OrderingChannels (HostFinalMemory.coreWitness (HostObserved.baseWitness w)))
    (data : ProverData Fp) (aligned : List (RowFacts SP1Prime))
    (paired : List.Forall₂ AlignedFacts aligned ((LocalCore.executionRows (HostFinalMemory.coreWitness (HostObserved.baseWitness w))).map (ExecutionRow.facts data)))
    (bytes : ∀ last, (raw w (.host (.word last))).ChannelGuarantees byteChannel.toRaw) (cut : ℕ) (phase : activeClockPhase cut)
    (edge : Pair) (window : MemoryMsg.timeNat edge.1 ≤ cut ∧ cut < MemoryMsg.timeNat edge.2) :
    let core := HostFinalMemory.coreWitness (HostObserved.baseWitness w)
    let cpu := LocalCore.executionRows core
    let words := TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view (HostHintReadLocal.wordTables (hostWitness w))
    edge ∈ MemoryRecordChain.pairs aligned ((cpu.flatMap (wordsAt data words)).map touch) (LocalCore.memoryRefreshes core) →
      ∃ r, FundedAt (raw w) (MemoryMsg.locOf edge.2) cut r ∧ r.value = edge.1.value := by
  intro core cpu words active
  have physical : core.Constraints := by exact HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.projected_constraints _
    (HostFinalMemory.baseWitness_constraints _ (HostObserved.baseWitness_constraints w checked)))
  have phaseOf {event : ExecutionRow SP1Prime} (member : event ∈ cpu) := (cpu_phase core physical ordering data member).1
  rcases List.mem_append.mp active with touched | refresh
  · obtain ⟨t, selected, rfl⟩ := List.mem_map.mp touched
    rcases List.mem_append.mp selected with instruction | host
    · obtain ⟨r, included, seen⟩ := List.mem_flatMap.mp instruction
      obtain ⟨_, present, fits⟩ := forall₂_exists_right paired r included
      obtain ⟨event, member, rfl⟩ := List.mem_map.mp present
      have valid := (List.forall₂_iff_zip.mp fits.touches).2 seen
      have state : (event.edge data).1 = (event.facts data).statePull := congrArg Prod.fst (event.edge_eq_facts data)
      rw [fits.statePull, ← state] at valid
      have prior := fits.memory.pulls.mem_iff.mp (List.mem_map_of_mem (f := Prod.fst) (List.of_mem_zip seen).1)
      obtain ⟨entry, before, eq⟩ := List.mem_map.mp prior
      have pull : (t.1.1, entry.2) ∈ (eventFacts data words event).memPulls := by
        have e : (t.1.1, entry.2) = entry := Prod.ext eq.symm rfl
        rw [e]
        exact List.mem_append_left _ before
      exact ⟨_, cpu_receipt w checked data cut phase member (phaseOf member) t valid window ⟨_, pull⟩, rfl⟩
    · obtain ⟨word, inside, rfl⟩ := List.mem_map.mp host
      obtain ⟨event, member, owner⟩ := List.mem_flatMap.mp inside
      have access := word_access w checked bytes word (List.mem_filter.mp owner).1
      have atClock := congrArg (fun k : Fp × Fp => clkNat k.1 k.2) (of_decide_eq_true (List.mem_filter.mp owner).2)
      change wordTime word = StateMsg.timeNat (event.edge data).1 at atClock
      have valid : TouchOK (StateMsg.timeNat (event.edge data).1) (touch word).1 (touch word).2 := atClock ▸ access.touch
      exact ⟨_, cpu_receipt w checked data cut phase member (phaseOf member) _ valid window
        ⟨_, List.mem_append_right _ (List.mem_map_of_mem (f := fun row => (touch row).1) owner)⟩, rfl⟩
  · have loc := congrArg Prod.fst (LocalCore.memoryRefreshes_preserve core edge refresh)
    exact ⟨_, ⟨refresh_predecessor w refresh, loc, window.1, window.2.le⟩, rfl⟩

/-- Every location with a physical frontier funds every genuine incoming CPU cut.
The selected unit receipt is present in the complete original table inventory and
its value agrees with the common, Sail-seeded replay for all observations at this location. -/
theorem physical_coverage_at_cuts (valid : image.Valid) (witness : EnsembleWitness (HostObserved.ensemble image source target final))
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
        (LocalCore.memoryInitialFrontier core loc) (LocalCore.memoryFinalFrontier core loc) (locContent source.sail.realize loc) (QueryAt (raw witness) loc) ∧
        ∀ first, LocalCore.memoryInitialFrontier core loc = some first → ∀ event ∈ cpu,
          let time := StateMsg.timeNat (event.edge boundary.data).1
          ∃ r, FundedAt (raw witness) loc time r ∧ r ∈ Counted.live (records (raw witness)) ∧ QueryAt (raw witness) loc time r.value := by
  intro core boundary cpu words additional
  have physical : core.Constraints := by exact HostLocalCore.localWitness_constraints _ (HostHintQueueBoundary.projected_constraints _
    (HostFinalMemory.baseWitness_constraints _ (HostObserved.baseWitness_constraints witness checked)))
  have membership (ch) (member : ch ∈ SnapshotMemoryEnsemble.membershipChannels source.sail.memorySnapshot) : core.BalancedChannel ch := by
    change BalancedInteractions ((HostFinalMemory.coreWitness (HostObserved.baseWitness witness)).interactionsWith ch)
    rw [core_membership_ledger witness ch member]
    exact boundaries ch (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  obtain ⟨aligned, paired, all⟩ := physical_cut_values valid witness checked packet installed packetChecked balanced cursor wordData bytes ordering memory program boundaries
  refine ⟨aligned, paired, fun loc => ⟨all loc, fun first present event active => ?_⟩⟩
  let cut := StateMsg.timeNat (event.edge boundary.data).1
  have tick := cpu_phase core physical ordering boundary.data active
  have zero := (LocalCore.memoryInitialFrontier_content_of_channels core physical ordering.sourceChecks ordering.byte membership present).2.1.2.2.1
  have funded : ∃ r, FundedAt (raw witness) loc cut r := by
    rcases all loc with ⟨empty, _⟩ | ⟨seed, last, path, start, finish, _, perm, walk, _, _⟩
    · exact (Option.some_ne_none first (present.symm.trans empty)).elim
    obtain rfl := Option.some.inj (start.symm.trans present)
    rcases first_later _ _ path walk cut (by rw [zero]; exact Nat.zero_le _) with ⟨edge, inside, lower, upper⟩ | terminal
    · obtain ⟨seen, same⟩ := List.mem_filter.mp (perm.mem_iff.mp inside)
      obtain ⟨r, ok, _⟩ := edge_receipt witness checked ordering boundary.data aligned paired bytes cut tick.1 edge ⟨lower, upper⟩ seen
      exact ⟨r, (of_decide_eq_true same) ▸ ok⟩
    · obtain ⟨seen, same⟩ := List.mem_filter.mp (List.mem_of_head? finish)
      have upper := (finalReadback_clocks last).2
      refine ⟨finalReadback last, final_predecessor witness seen, of_decide_eq_true same, terminal, ?_⟩
      rw [upper]
      exact Nat.le_pred_of_lt tick.2
  obtain ⟨r, funds⟩ := funded
  obtain ⟨id, origin⟩ := origin_of_record (raw witness) (raw_registered witness) funds.1 one_ne_zero
  exact ⟨r, funds, List.mem_map.mpr ⟨(1, r), List.mem_filter.mpr ⟨funds.1, by simp⟩, rfl⟩,
    id, r, origin, funds.2.1, funds.2.2.1, funds.2.2.2, rfl⟩

end SP1Clean.Export.WriteSourceRegistry
