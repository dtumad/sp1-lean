import SP1Clean.Export.WriteHintRecordOrigins
import SP1Clean.Soundness.HintSnapshotDecode
import ToClean.Air.AppendedAuthentication

/-! # The ordered outgoing queue walk in the installed native verifier

The word reader and the singleton seal own the complete word-walk ledger. Raw LogUp
acceptance therefore connects each public word, in physical order, to the actual
outgoing head recorded by the seal and ultimately to the null pointer.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics Soundness HostHintSnapshot WriteSourceRegistry

private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}

attribute [local irreducible] base withSources preprocessing

private theorem walk_channel : (HostHintSnapshot.channel (p := SP1Prime)).toRaw ∈ channels := by
  apply List.mem_of_getElem? (i := 10)
  rfl

/-- Every word-walk occurrence belongs to exactly these two physical slots. -/
theorem hint_walk_ledger (w : EnsembleWitness (preprocessing image source target final)) :
    let ch := (HostHintSnapshot.channel (p := SP1Prime)).toRaw
    w.interactionsWith ch = ((slot image source target final 10).table w).interactionsWith ch ++
      ((slot image source target final 11).table w).interactionsWith ch := by
  let ch := (HostHintSnapshot.channel (p := SP1Prime)).toRaw
  let prior := withSources image source target final
  let install := appended image source target final
  let suffix := w.tables.drop prior.tables.length
  let reader := slot image source target final 10
  let terminal := slot image source target final 11
  have silent {cs : List (Component F)} (names : ch.name ∉ cs.flatMap (fun c => c.circuit.channels.map RawChannel.name)) :
      ∀ c ∈ cs, ch ∉ c.circuit.channels :=
    fun c member used => names (List.mem_flatMap.mpr ⟨c,member,List.mem_map_of_mem used⟩)
  have eq := install.ledger_window w ch 10 2 (silent (of_decide_eq_true rfl)) (silent (of_decide_eq_true rfl))
  rw [EnsembleWitness.interactionsWith_nil_of_not_registered _ _ (protocol_fresh image source target final _ walk_channel),
    List.nil_append] at eq
  have registered : suffix.map (·.component) = tables source target := install.suffix_components w
  have length : 11 < suffix.length := by
    have size := congrArg List.length registered
    rw [List.length_map] at size
    rw [size]
    simp [tables]
  have readerRow : suffix[10]'(by omega) = reader.table w := by
    simp only [suffix, List.getElem_drop]
    rfl
  have sealRow : suffix[11]'(by omega) = terminal.table w := by
    simp only [suffix, List.getElem_drop]
    rfl
  change w.interactionsWith ch = (reader.table w).interactionsWith ch ++ (terminal.table w).interactionsWith ch
  rw [eq]
  change ((suffix.drop 10).take 2).flatMap _ = _
  rw [List.drop_eq_getElem_cons (by omega : 10 < suffix.length), List.drop_eq_getElem_cons (by omega : 11 < suffix.length),
    readerRow, sealRow]
  simp

/-- For a raw accepted native witness, all target words lie on the connected walk from the
private outgoing head to null, in exactly the public snapshot's order. -/
theorem native_hint_walk (w : EnsembleWitness (native image source target)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    let seen := observed w
    let endQueue := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) target.host.io.hints
    let reader := (slot image source target endQueue 10).table seen
    let terminal := slot image source target endQueue 11
    let state := Seal.physicalState target.host.io.hints (terminal.table seen) (terminal.table_component seen)
    Walk.IsWalk (physicalEdge reader) (endpoint 0 state.head) (endpoint (wordRows target.host.io.hints) 0)
      ((List.finRange reader.table.length).take (wordRows target.host.io.hints)) := by
  let seen := observed w
  let endQueue := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) target.host.io.hints
  let reader := slot image source target endQueue 10
  let terminal := slot image source target endQueue 11
  let ch := (HostHintSnapshot.channel (p := SP1Prime)).toRaw
  have paid := observed_balance w fit raw ch (protocol_installed image source target endQueue _ walk_channel)
    (of_decide_eq_true rfl)
  change BalancedInteractions (seen.interactionsWith ch) at paid
  rw [hint_walk_ledger seen] at paid
  have reordered := BalancedInteractions.of_perm paid (List.perm_append_comm ..)
  have ends := Seal.physical_walk_ledger target.host.io.hints (terminal.table seen) (terminal.table_component seen)
  rw [ends] at reordered
  exact physical_walk target.host.io.hints (reader.table seen) (reader.table_component seen)
    (reader.table_constraints seen ((observed_constraints w).mp checked)) _ reordered

/-- Once the whole witness's immutable lookup channels identify a common persistent store,
raw native acceptance forces that store to represent the complete public target queue. -/
theorem outgoing_queue_of_immutable_reads (store : HintQueue.Store)
    (w : EnsembleWitness (native image source target)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp)
    (nodes : ∀ r, HostHintQueue.nodeChannel.pulledValue r ∈ w.interactionsWith HostHintQueue.nodeChannel.toRaw →
      r.Valid ∧ r.Binds store)
    (words : ∀ r, HostHintQueue.wordChannel.pulledValue r ∈ w.interactionsWith HostHintQueue.wordChannel.toRaw →
      r.Binds store) :
    let seen := observed w
    let endQueue := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) target.host.io.hints
    let terminal := slot image source target endQueue 11
    let state := Seal.physicalState target.host.io.hints (terminal.table seen) (terminal.table_component seen)
    HintQueue.Represents store (Address.toNat state.head) target.host.io.hints := by
  let hints := target.host.io.hints
  let seen := observed w
  let endQueue := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) hints
  let reader := slot image source target endQueue 10
  let table := reader.table seen
  let installed : TableSlot (native image source target).tables (HostHintSnapshot.component (p := SP1Prime) hints) := reader
  have carries (ch : RawChannel F) : table.interactionsWith ch ⊆ w.interactionsWith ch :=
    installed.table_interactions_subset w ch
  have visible (i : Fin table.table.length) (_ : i.val < wordRows hints) : BoundReads store (physicalInput table i) := by
    have requirements := physical_lookups hints table (reader.table_component seen) i
    constructor
    · intro first
      exact nodes _ (carries _ (requirements.1 first))
    · intro active
      exact words _ (carries _ (requirements.2 active))
  obtain ⟨tails, chain⟩ := reads_snapshot_of_walk store hints table (reader.table_component seen)
    (reader.table_constraints seen ((observed_constraints w).mp checked)) _ (native_hint_walk w checked fit raw) visible
  exact chain.represents

/-- Each active lookup along the verifier-fixed outgoing queue walk has canonical shape and
comes from its incoming physical inventory or an active allocation publisher. -/
theorem outgoing_queue_read_origins (w : EnsembleWitness (native image source target)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (paid : w.Balanced .logUp) :
    let seen := observed w
    let endQueue := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) target.host.io.hints
    let reader := slot image source target endQueue 10
    let table := reader.table seen
    ∀ i : Fin table.table.length, let row := physicalInput table i
      (row.1.first = 1 → (row.1.node row.2.1).Valid ∧ NodeOrigin seen (row.1.node row.2.1)) ∧
      (row.1.active = 1 → (row.1.word row.2.1).Valid ∧ WordOrigin seen (row.1.word row.2.1)) := by
  intro seen endQueue reader table i
  let installed : TableSlot (native image source target).tables (HostHintSnapshot.component (p := SP1Prime) target.host.io.hints) := reader
  have lookups := physical_lookups target.host.io.hints table (reader.table_component seen) i
  obtain ⟨nodes,words⟩ := assembled_hint_read_origins w checked fit paid
  exact ⟨fun first => nodes _ (installed.table_interactions_subset w _ (lookups.1 first)),
    fun active => words _ (installed.table_interactions_subset w _ (lookups.2 active))⟩

/-- A common persistent extension of the incoming store represents the outgoing queue when
it binds the positive publications of the two dynamic allocation tables. Every fixed-source
binding and every snapshot lookup is derived from the installed witness. -/
theorem outgoing_queue_of_allocations (w : EnsembleWitness (native image source target)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (paid : w.Balanced .logUp) (store : HintQueue.Store)
    (extension : HintQueue.Extends (HintQueue.ofList source.host.io.hints).1 store)
    (nodes : ∀ r, PublishedBy ((slot image source target (SP1Clean.HostHintQueueBoundary.initial target.host.io.hints) 16).table
      (observed w)) WriteAllocation.Step.readers (fun s => s.node.node) r → r.Binds store)
    (words : ∀ r, PublishedBy ((slot image source target (SP1Clean.HostHintQueueBoundary.initial target.host.io.hints) 18).table
      (observed w)) WriteAllocation.Words.Row.wordReads WriteAllocation.Words.Row.word r → r.Binds store) :
    let seen := observed w
    let endQueue := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) target.host.io.hints
    let terminal := slot image source target endQueue 11
    let state := Seal.physicalState target.host.io.hints (terminal.table seen) (terminal.table_component seen)
    HintQueue.Represents store (Address.toNat state.head) target.host.io.hints := by
  obtain ⟨metadata,contents⟩ := assembled_hint_read_origins w checked fit paid
  apply outgoing_queue_of_immutable_reads store w checked fit paid
  · intro r read
    obtain ⟨valid,origin⟩ := metadata r read
    rcases origin with fixed | allocated
    · exact ⟨valid,fixed.2.2.extend extension⟩
    · exact ⟨valid,nodes r allocated⟩
  · intro r read
    obtain ⟨_,origin⟩ := contents r read
    rcases origin with fixed | allocated
    · exact fixed.2.2.extend extension
    · exact words r allocated

end SP1Clean.Export.WriteObservationAssembly
