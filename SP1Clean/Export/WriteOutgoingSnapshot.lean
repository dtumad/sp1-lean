import SP1Clean.Export.HintSnapshotCapacity
import SP1Clean.Proofs.Completeness.WriteAllocationStore

/-! # Outgoing hint tables at the last actual queue access

The reader starts at the head returned by replay, even if that head was reached by
popping allocated nodes. The singleton uses the last actual access clock and the
entire historical store size. Both real and inactive word rows enter the field bound.
-/

namespace SP1Clean.Export.InstalledAssembly

open Air.Flat Circuit Semantics Semantics.HintQueue Machine FormalModel.Shard
private abbrev F := ZMod SP1Prime

/-- The replayed outgoing queue determines both installed tables and the complete number
of physical walk interactions. The preset pays for all padded reader rows and the checked. -/
theorem compiled_outgoing_snapshot {ctx : Context} {events : List ExecutionEvent}
    (run : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) (data : ProverData F) :
    let native := run.mono (preset.trans fixedProviderPreset_le_native)
    ∃ cursor, storeAfter? (policy SP1Prime ctx.image) ctx.image.program ctx.source.realize events (ofList ctx.source.host.io.hints) = some cursor ∧
      let hints := ctx.target.host.io.hints
      let reader := HostHintSnapshot.tableFor cursor.1 cursor.2 hints (admissible_hint_snapshot_fits native) data
      let state := HostHintQueue.State.encode (p := SP1Prime) (events.foldl WriteAllocation.advanceQueueClock 0) cursor.2 cursor.1.size
      let terminal := HostHintSnapshot.Seal.tableFor hints state data
      let ledger := reader.interactionsWith HostHintSnapshot.channel.toRaw ++ terminal.interactionsWith HostHintSnapshot.channel.toRaw
      reader.Constraints ∧ reader.Guarantees ∧ terminal.Constraints ∧ terminal.Guarantees ∧
        ledger.length = 2 * (HostHintSnapshot.inventory (p := SP1Prime) hints).height + 2 ∧
        LogUpBalanced ledger ∧ (Balance.logUp (F := F)).fits ledger.length = true ∧ BalancedInteractions ledger := by
  intro native
  obtain ⟨cursor,replay,good,guar,sealed⟩ := admissible_hint_snapshot_tables native data
  refine ⟨cursor,replay,?_⟩
  intro hints reader state terminal ledger
  let last := events.foldl WriteAllocation.advanceQueueClock 0
  have clock : (BitVec.ofNat 48 last).toNat = last := by
    exact Nat.mod_eq_of_lt (WriteAllocation.final_queue_clock_fits native)
  have checked := sealed (BitVec.ofNat 48 last)
  dsimp only at checked
  rw [clock] at checked
  have size := hint_snapshot_occurrences hints reader terminal rfl rfl HostHintSnapshot.channel.toRaw
  have different (ch : RawChannel F) (names : ch.name ≠ (HostHintSnapshot.channel (p := SP1Prime)).name) : ch ≠ HostHintSnapshot.channel.toRaw := ne_of_apply_ne RawChannel.name names
  have count : ledger.length = 2 * (HostHintSnapshot.inventory (p := SP1Prime) hints).height + 2 := by
    have node := different HostHintQueue.nodeChannel.toRaw (by decide)
    have word := different HostHintQueue.wordChannel.toRaw (by decide)
    have queue := different HostHintQueue.stateChannel.toRaw (by decide)
    simpa only [ite_true,ite_eq_right node,ite_eq_right word,ite_eq_right queue,Nat.one_mul,Nat.zero_mul,Nat.add_zero] using size
  have height := fixedProviderPreset_hint_snapshot_height ctx run preset
  have below : ledger.length < SP1Prime := by
    rw [count]
    exact (Nat.add_le_add_right (Nat.mul_le_mul_left 2 height) 2).trans_lt (by decide)
  have fit : (Balance.logUp (F := F)).fits ledger.length = true := by
    simpa only [Balance.logUp,decide_eq_true_eq,ComputableRingChar.char_eq,ZMod.ringChar_zmod_n] using below
  exact ⟨good,guar,checked.1,checked.2.1,count,checked.2.2,fit,Balance.logUp.balancedInteractions_of_balanced _ fit checked.2.2⟩

end SP1Clean.Export.InstalledAssembly
