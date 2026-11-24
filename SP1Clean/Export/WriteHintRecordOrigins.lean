import SP1Clean.Export.WriteObservationHandoff
import SP1Clean.Export.WriteHostSourceGrounding
import SP1Clean.Proofs.Operations.HintRecordPublications

/-! # Immutable hint record origins for the installed native observer

The original host consumers, fixed source inventories, outgoing snapshot reader and dynamic
allocation publishers retain their exact signed physical occurrences. Only the two incoming
inventories bind to the source store. Fresh publications have their own physical row origin.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics HintQueue Soundness WriteSourceRegistry HostHintQueue WriteAllocation HintRecordPublications

private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}

private abbrev original (w : EnsembleWitness (preprocessing image source target final)) :
    EnsembleWitness (HostObserved.ensemble image source target final) := supervisor w

attribute [local irreducible] withSources preprocessing

private def hostComponents (source target : ExecutionSnapshot) : List (Component F) :=
  ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component)) ++
     (HostHintReadHandoff.wordResources ++ (HostHintReadLocal.sourceResources source.host.io.hints ++ FinalMemoryChecks.checkTables target.sail.memorySnapshot))

private def hostRows (w : EnsembleWitness (preprocessing image source target final)) :=
  HostLocalCore.auxiliaryTables (hostWitness (original w))

private theorem host_components (w : EnsembleWitness (preprocessing image source target final)) :
    (hostRows w).map (·.component) = hostComponents source target := HostLocalCore.auxiliaryTables_components _

private theorem host_size (w : EnsembleWitness (preprocessing image source target final)) : (hostRows w).length = 35 := by
  have size := congrArg List.length (host_components w)
  rw [List.length_map] at size
  exact size

/-- An original auxiliary table of the host supervisor. Its physical position in the full
assembly is 63 plus the given index. -/
def hintHostTable (w : EnsembleWitness (preprocessing image source target final)) (i : Fin 35) : Table F :=
  (hostRows w)[i.val]'((host_size w).symm ▸ i.isLt)

private theorem host_component (w : EnsembleWitness (preprocessing image source target final)) (i : Fin 35) :
    (hintHostTable w i).component = (hostComponents source target)[i.val] := by
  have h := List.getElem_of_eq (host_components w) (i := i.val) (by rw [List.length_map, host_size]; exact i.isLt)
  simpa only [List.getElem_map, hintHostTable] using h

private theorem host_constraints (w : EnsembleWitness (preprocessing image source target final)) (checked : w.Constraints)
    (i : Fin 35) : (hintHostTable w i).Constraints := by
  have valid := supervisor_constraints w checked
  have inner := HostHintQueueBoundary.projected_constraints _ (HostFinalMemory.baseWitness_constraints _
    (HostObserved.baseWitness_constraints (original w) valid))
  exact inner _ (List.mem_of_mem_drop (List.getElem_mem (l := hostRows w) _))

private def hostUsed (source target : ExecutionSnapshot) (ch : RawChannel F) (i : Fin 35) : Bool :=
  ((hostComponents source target)[i.val].circuit.channels.map RawChannel.name).contains ch.name

private def hostSupport (source target : ExecutionSnapshot) (ch : RawChannel F) : List (Fin 35) :=
  (List.finRange 35).filter (hostUsed source target ch)

private theorem host_ledger (w : EnsembleWitness (preprocessing image source target final)) (ch : RawChannel F)
    (which : ch = nodeChannel.toRaw ∨ ch = wordChannel.toRaw) :
    (supervisor w).interactionsWith ch =
      (hostSupport source target ch).flatMap (fun i => (hintHostTable w i).interactionsWith ch) := by
  let host := hostWitness (original w)
  have registered : ch ∈ HostLocalCore.registry image source (HintReadWordChip.stateChannel.toRaw :: HostFinalMemory.sourceChannels target.sail.memorySnapshot) := by
    rcases which with rfl | rfl <;> simp [HostLocalCore.registry, HostFinalMemory.sourceChannels]
  have fresh : ch ∉ (LocalCore.baseEnsemble (p := SP1Prime) image source).channels := by
    apply LocalCore.not_mem_baseEnsemble_channels
    rcases which with rfl | rfl <;> simp [LocalCore.baseChannelNames, nodeChannel, wordChannel, Channel.toRaw]
  have split := HostLocalCore.interactions_split_new host ch registered fresh
    (by rcases which with rfl | rfl <;> simp [nodeChannel,wordChannel,WritePermissionProvider.channel,Channel.toRaw])
    (by rcases which with rfl | rfl <;> simp [nodeChannel,wordChannel,StaticTable.channel,ProgramImage.writePermissionTable,StaticTable.ofRows,Channel.toRaw])
  have quiet : (HostLocalCore.hostCallTable host).interactionsWith ch = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    rw [HostLocalCore.hostCallTable_component]
    intro used
    have found := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    rcases which with rfl | rfl <;> exact Bool.noConfusion (show false = true from found)
  have transport := host_protocol_ledger (original w) ch (by rcases which with rfl | rfl <;> simp)
  change (original w).interactionsWith ch = _
  rw [← transport,split,quiet,List.nil_append]
  have rows : hostRows w = (List.finRange 35).map (hintHostTable w) := by
    apply List.ext_getElem
    · simp [host_size]
    · intro i hi hj; simp only [List.getElem_map,List.getElem_finRange,hintHostTable,Fin.val_cast]
  change (hostRows w).flatMap _ = _
  rw [rows,List.flatMap_map]
  let used := hostUsed source target ch
  have select (xs : List (Fin 35)) : xs.flatMap (fun i => (hintHostTable w i).interactionsWith ch) =
      (xs.filter used).flatMap (fun i => (hintHostTable w i).interactionsWith ch) := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      cases yes : used i with
      | true => simp [yes,ih]
      | false =>
        have empty : (hintHostTable w i).interactionsWith ch = [] := by
          apply Table.interactionsWith_nil_of_channel_not_mem
          intro present
          rw [host_component] at present
          exact Bool.noConfusion ((List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) present)).symm.trans yes)
        simp [yes,ih,empty]
  exact select _

/-- The two original metadata consumers and the incoming fixed node source, in physical order. -/
theorem original_hint_nodes (w : EnsembleWitness (preprocessing image source target final)) :
    let ch := (nodeChannel (p := SP1Prime)).toRaw
    (supervisor w).interactionsWith ch = (hintHostTable w 0).interactionsWith ch ++
      ((hintHostTable w 19).interactionsWith ch ++ (hintHostTable w 23).interactionsWith ch) := by
  let ch := (nodeChannel (p := SP1Prime)).toRaw
  have mask : hostSupport source target ch = [0,19,23] := rfl
  simpa only [mask,List.flatMap_cons,List.flatMap_nil,List.append_nil] using host_ledger w ch (Or.inl rfl)

/-- The original HINT_READ handler, its two word tables, and the fixed incoming word source. -/
theorem original_hint_words (w : EnsembleWitness (preprocessing image source target final)) :
    let ch := (wordChannel (p := SP1Prime)).toRaw
    (supervisor w).interactionsWith ch = (hintHostTable w 0).interactionsWith ch ++ ((hintHostTable w 21).interactionsWith ch ++
      ((hintHostTable w 22).interactionsWith ch ++ (hintHostTable w 24).interactionsWith ch)) := by
  let ch := (wordChannel (p := SP1Prime)).toRaw
  have mask : hostSupport source target ch = [0,21,22,24] := rfl
  simpa only [mask,List.flatMap_cons,List.flatMap_nil,List.append_nil] using host_ledger w ch (Or.inr rfl)

private theorem empty_node (pointer : Nat) : node? #[] pointer = none := by cases pointer <;> rfl

private theorem node_consumer {t : Table F} (checked : t.Constraints)
    (auth : HostHintRecordSources.Authenticates #[] t.component)
    {i : Interaction F} (mem : i ∈ t.interactionsWith nodeChannel.toRaw) : ¬i.Push := by
  intro push
  obtain ⟨row,live,atRow⟩ := List.mem_flatMap.mp mem
  obtain ⟨_,_,_,node,found,_⟩ := auth.node _ (checked row live) _ atRow push
  rw [empty_node] at found
  contradiction

private theorem word_consumer {t : Table F} (checked : t.Constraints)
    (auth : HostHintRecordSources.Authenticates #[] t.component)
    {i : Interaction F} (mem : i ∈ t.interactionsWith wordChannel.toRaw) : ¬i.Push := by
  intro push
  obtain ⟨row,live,atRow⟩ := List.mem_flatMap.mp mem
  obtain ⟨_,_,_,node,found,_⟩ := auth.word _ (checked row live) _ atRow push
  rw [empty_node] at found
  contradiction

private theorem positive_node_source (w : EnsembleWitness (preprocessing image source target final)) (checked : w.Constraints)
    {i : Interaction F} (original : i ∈ (supervisor w).interactionsWith nodeChannel.toRaw) (push : i.Push) :
    i ∈ (hintHostTable w 23).interactionsWith nodeChannel.toRaw := by
  rw [original_hint_nodes w] at original
  rcases List.mem_append.mp original with receive | others
  · exact False.elim (node_consumer (host_constraints w checked 0)
      (by rw [host_component]; exact HostHintRecordSources.handler_authenticates #[]) receive push)
  rcases List.mem_append.mp others with length | fixed
  · exact False.elim (node_consumer (host_constraints w checked 19)
      (by rw [host_component]; exact HostHintRecordSources.hint_length_authenticates #[] false) length push)
  exact fixed

private theorem positive_word_source (w : EnsembleWitness (preprocessing image source target final)) (checked : w.Constraints)
    {i : Interaction F} (original : i ∈ (supervisor w).interactionsWith wordChannel.toRaw) (push : i.Push) :
    i ∈ (hintHostTable w 24).interactionsWith wordChannel.toRaw := by
  rw [original_hint_words w] at original
  rcases List.mem_append.mp original with receive | others
  · exact False.elim (word_consumer (host_constraints w checked 0)
      (by rw [host_component]; exact HostHintRecordSources.handler_authenticates #[]) receive push)
  rcases List.mem_append.mp others with interior | lastOrFixed
  · exact False.elim (word_consumer (host_constraints w checked 21)
      (by rw [host_component]; exact HostHintRecordSources.word_consumer_authenticates #[] false) interior push)
  rcases List.mem_append.mp lastOrFixed with last | fixed
  · exact False.elim (word_consumer (host_constraints w checked 22)
      (by rw [host_component]; exact HostHintRecordSources.word_consumer_authenticates #[] true) last push)
  exact fixed

private theorem authenticated_message {Record : TypeMap} [ProvableType Record] (ch : Channel F Record)
    {t : Table F} {P : Record F → Prop} (auth : t.Authenticates ch P) {i : Interaction F} (record : Record F)
    (mem : i ∈ t.interactionsWith ch.toRaw) (push : i.Push) (same : i.msg = (toElements record).toArray) : P record := by
  obtain ⟨row,live,atRow⟩ := List.mem_flatMap.mp mem
  obtain ⟨r,encoded,valid⟩ := auth row live i atRow push
  have eq := congrArg (fromElements (M := Record)) (Vector.toArray_inj.mp (encoded.symm.trans same))
  simp only [ProvableType.fromElements_toElements] at eq
  exact eq ▸ valid

/-- An immutable record is published at positive multiplicity by an actual active dynamic
allocation row. Its pointer, data and reader count are the values in that physical row. -/
def PublishedBy {Input : TypeMap} [ProvableType Input] {Record : Type}
    (table : Table F) (count : Input F → F) (payload : Input F → Record) (record : Record) : Prop :=
  ∃ row ∈ table.table, let r := valueFromOffset (ProvablePair Input field) 0 (table.environment row)
    r.2 = 1 ∧ count r.1 ≠ 0 ∧ payload r.1 = record

private theorem published_of_row {Input Record : TypeMap} [ProvableType Input] [ProvableType Record]
    (ch : Channel F Record) (t : Table F) (count : Input F → F) (payload : Input F → Record F)
    (ledger : ∀ env, let r := valueFromOffset (ProvablePair Input field) 0 env
      t.component.operations.interactionValuesWith ch.toRaw env = [ch.emittedValue (r.2 * count r.1) (payload r.1)])
    (gate : ∀ row ∈ t.table, IsBool (valueFromOffset (ProvablePair Input field) 0 (t.environment row)).2)
    (r : Record F) {i : Interaction F} (member : i ∈ t.interactionsWith ch.toRaw) (push : i.Push)
    (same : i.msg = (toElements r).toArray) : PublishedBy t count payload r := by
  obtain ⟨row,live,atRow⟩ := List.mem_flatMap.mp member
  rw [ledger] at atRow
  obtain rfl := List.mem_singleton.mp atRow
  let current := valueFromOffset (ProvablePair Input field) 0 (t.environment row)
  have nonzero : current.2 * count current.1 ≠ 0 := push.1
  have encoded : (toElements (payload current.1)).toArray = (toElements r).toArray := same
  have equal := congrArg (fromElements (M := Record)) (Vector.toArray_inj.mp encoded)
  simp only [ProvableType.fromElements_toElements] at equal
  refine ⟨row,live,?_,right_ne_zero_of_mul nonzero,equal⟩
  exact (gate row live).resolve_left (left_ne_zero_of_mul nonzero)

private theorem snapshot_has_no_push (w : EnsembleWitness (preprocessing image source target final)) (checked : w.Constraints)
    (ch : RawChannel F) (which : ch = nodeChannel.toRaw ∨ ch = wordChannel.toRaw) {i : Interaction F}
    (member : i ∈ ((slot image source target final 10).table w).interactionsWith ch) : ¬i.Push := by
  let reader : TableSlot (preprocessing image source target final).tables (HostHintSnapshot.component target.host.io.hints) :=
    slot image source target final 10
  obtain ⟨row,live,atRow⟩ := List.mem_flatMap.mp member
  have checks := reader.table_constraints w checked row live
  change i ∈ (reader.table w).component.operations.interactionValuesWith ch ((reader.table w).environment row) at atRow
  rw [reader.table_component w] at atRow checks
  exact snapshot_pulls _ ch which _ checks _ atRow

/-- A fixed physical provider emitted the identical serialized record at nonzero multiplicity. -/
def FixedPublication {Record : TypeMap} [ProvableType Record] (table : Table F) (ch : Channel F Record)
    (record : Record F) : Prop :=
  ∃ i ∈ table.interactionsWith ch.toRaw, i.Push ∧ i.msg = (toElements record).toArray

/-- Every active metadata request in the full ledger gets its record either from the checked
incoming queue or from a positively funded, active fresh-node row. -/
theorem node_read_origin (w : EnsembleWitness (preprocessing image source target final)) (checked : w.Constraints)
    (funded : w.BalancedChannel nodeChannel.toRaw) (r : NodeRecord F)
    (read : nodeChannel.pulledValue r ∈ w.interactionsWith nodeChannel.toRaw) :
    (FixedPublication (hintHostTable w 23) nodeChannel r ∧ r.Valid ∧ r.Binds (ofList source.host.io.hints).1) ∨
      PublishedBy ((slot image source target final 16).table w) Step.readers (fun step => step.node.node) r := by
  obtain ⟨i,member,same,push⟩ := funded.exists_push_of_pull _ read ⟨rfl,rfl⟩
  rw [hintNode_ledger w] at member
  rcases List.mem_append.mp member with prior | later
  · have fixed := positive_node_source w checked prior push
    have verified := HostHintQueue.source_authenticates source.host.io.hints (hintHostTable w 23)
      (host_component w 23) (host_constraints w checked 23)
    exact Or.inl ⟨⟨i,fixed,push,same⟩,authenticated_message _ verified r fixed push same⟩
  rcases List.mem_append.mp later with snap | fresh
  · exact (snapshot_has_no_push w checked _ (Or.inl rfl) snap push).elim
  let allocator : TableSlot (preprocessing image source target final).tables stepComponent := slot image source target final 16
  apply Or.inr
  apply published_of_row nodeChannel (allocator.table w) Step.readers (fun s => s.node.node) ?_ ?_ r fresh push same
  · intro env
    rw [allocator.table_component w]
    exact node_row env
  · intro row live
    have valid := allocator.table_constraints w checked row live
    rw [allocator.table_component w] at valid
    let input := varFromOffset (ProvablePair Step field) (F := F) 0
    have h := Guarded.activity_of_constraints stepCircuit stepSupported input _ _ ((Component.constraintsHold_iff _).mp valid)
    rwa [Guarded.eval_activity,eval_varFromOffset_valueFromOffset] at h

/-- Every active word request, including an outgoing snapshot read, matches the complete
incoming record or an actual active allocation word with the same pointer, position, limbs and final flag. -/
theorem word_read_origin (w : EnsembleWitness (preprocessing image source target final)) (checked : w.Constraints)
    (funded : w.BalancedChannel wordChannel.toRaw) (r : WordRecord F)
    (read : wordChannel.pulledValue r ∈ w.interactionsWith wordChannel.toRaw) :
    (FixedPublication (hintHostTable w 24) wordChannel r ∧ r.Valid ∧ r.Binds (ofList source.host.io.hints).1) ∨
      PublishedBy ((slot image source target final 18).table w) Words.Row.wordReads Words.Row.word r := by
  obtain ⟨i,member,same,push⟩ := funded.exists_push_of_pull _ read ⟨rfl,rfl⟩
  rw [hintWord_ledger w] at member
  rcases List.mem_append.mp member with prior | later
  · have fixed := positive_word_source w checked prior push
    have verified := HostHintQueue.sourceWord_authenticates source.host.io.hints (hintHostTable w 24)
      (host_component w 24) (host_constraints w checked 24)
    exact Or.inl ⟨⟨i,fixed,push,same⟩,authenticated_message _ verified r fixed push same⟩
  rcases List.mem_append.mp later with snap | fresh
  · exact (snapshot_has_no_push w checked _ (Or.inr rfl) snap push).elim
  let allocator : TableSlot (preprocessing image source target final).tables Words.wordComponent := slot image source target final 18
  apply Or.inr
  apply published_of_row wordChannel (allocator.table w) Words.Row.wordReads Words.Row.word ?_ ?_ r fresh push same
  · intro env
    rw [allocator.table_component w]
    exact word_row env
  · intro row live
    have valid := allocator.table_constraints w checked row live
    rw [allocator.table_component w] at valid
    let input := varFromOffset (ProvablePair Words.Row field) (F := F) 0
    have h := Guarded.activity_of_constraints Words.wordCircuit Words.wordSupported input _ _ ((Component.constraintsHold_iff _).mp valid)
    rwa [Guarded.eval_activity,eval_varFromOffset_valueFromOffset] at h

end SP1Clean.Export.WriteObservationAssembly
