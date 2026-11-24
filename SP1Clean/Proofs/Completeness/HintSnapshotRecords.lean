import SP1Clean.Proofs.Completeness.HintQueueReaders
import SP1Clean.Proofs.Operations.HintQueueSnapshot

/-! # Physical outgoing immutable queue demand

Every fixed snapshot row carries one node site and one word site. The first word of each live
buffer activates its node pull, all live words pull their stored value, and the fixed padding
retains both sites with zero multiplicity.
-/

namespace SP1Clean.HostHintSnapshot

open Circuit Air.Flat Semantics Semantics.HintQueue HostHintQueue
private abbrev F := ZMod SP1Prime

private theorem sites (hints : List Bytes) (env : Environment F) :
    let r := valueFromOffset Inputs 0 env
    let c := (component hints).operations
    c.interactionValuesWith nodeChannel.toRaw env = [nodeChannel.pulledIfValue r.1.first (r.1.node r.2.1)] ∧
    c.interactionValuesWith wordChannel.toRaw env = [wordChannel.pulledIfValue r.1.active (r.1.word r.2.1)] := by
  classical
  let c := component (p := SP1Prime) hints
  have project {M : TypeMap} [ProvableType M] (ch : Channel F M) (weight : F) (value : M F)
      (present : ch.pulledIfValue weight value ∈ c.operations.interactionValues env)
      (one : c.channelWidth ch.toRaw = 1) :
      c.operations.interactionValuesWith ch.toRaw env = [ch.pulledIfValue weight value] := by
    have length : (c.operations.interactionValuesWith ch.toRaw env).length = 1 :=
      (List.length_map ..).trans one
    obtain ⟨v, eq⟩ := List.length_eq_one_iff.mp length
    have mem : ch.pulledIfValue weight value ∈ c.operations.interactionValuesWith ch.toRaw env := by
      rw [Operations.interactionValuesWith_eq_filter]
      exact List.mem_filter.mpr ⟨present, by simp [Channel.pulledIfValue]⟩
    rw [eq] at mem
    exact eq.trans (congrArg (fun x => [x]) (List.mem_singleton.mp mem).symm)
  obtain ⟨n, w⟩ := lookup_occurrences hints env
  have channels : c.operations.interactions.map (·.channel) =
      [channel.toRaw, nodeChannel.toRaw, wordChannel.toRaw, channel.toRaw] := by
    rw [Component.interactions_eq]
    change (((main hints (varFromOffset Inputs 0)).operations (size Inputs)).interactions.map _) = _
    rw [ledger]
    rfl
  have width (ch : RawChannel F) : c.channelWidth ch = (c.operations.interactions.map (·.channel)).countP (fun k => decide (k = ch)) := by
    rw [List.countP_map, List.countP_eq_length_filter]
    rfl
  constructor
  · apply project _ _ _ n
    simp [width, channels, channel, nodeChannel, wordChannel, Channel.toRaw]
  · apply project _ _ _ w
    simp [width, channels, channel, nodeChannel, wordChannel, Channel.toRaw]

private theorem table_records {M : TypeMap} [ProvableType M] (ch : Channel F M) (take : Inputs F → Interaction F)
    (store : Store) (head : Nat) (hints : List Bytes) (fit : fits hints = true) (data : ProverData F)
    (point : ∀ env, (component hints).operations.interactionValuesWith ch.toRaw env = [take (valueFromOffset Inputs 0 env)]) :
    (tableFor store head hints fit data).interactionsWith ch.toRaw = (inputsFor (p := SP1Prime) store head hints).map take := by
  rw [List.map_eq_flatMap]
  unfold tableFor
  erw [Table.build_interactions]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro r _
  let c := component (p := SP1Prime) hints
  let rows := inputsFor (p := SP1Prime) store head hints
  let own := c.inputData rows data
  let env := Environment.fromArray (c.buildRow r own (.empty _)) own
  change c.operations.interactionValuesWith ch.toRaw env = [take r]
  rw [point]
  exact congrArg (fun x : Inputs F => [take x]) (c.rowInput_buildRow r own own (.empty _))

/-- The complete immutable node and word ledgers, in the verifier's fixed physical order. -/
theorem tableFor_records (store : Store) (head : Nat) (hints : List Bytes) (fit : fits hints = true) (data : ProverData F) :
    let t := tableFor store head hints fit data
    let rs := inputsFor (p := SP1Prime) store head hints
    t.interactionsWith nodeChannel.toRaw = rs.map (fun r => nodeChannel.pulledIfValue r.1.first (r.1.node r.2.1)) ∧
    t.interactionsWith wordChannel.toRaw = rs.map (fun r => wordChannel.pulledIfValue r.1.active (r.1.word r.2.1)) :=
  ⟨table_records _ _ _ _ _ fit data (fun env => (sites hints env).1),
   table_records _ _ _ _ _ fit data (fun env => (sites hints env).2)⟩

/-- Each immutable channel retains one occurrence per physical fixed row. -/
theorem tableFor_record_counts (store : Store) (head : Nat) (hints : List Bytes) (fit : fits hints = true) (data : ProverData F) :
    let t := tableFor store head hints fit data
    (t.interactionsWith nodeChannel.toRaw).length = (inventory (p := SP1Prime) hints).height ∧
    (t.interactionsWith wordChannel.toRaw).length = (inventory (p := SP1Prime) hints).height := by
  obtain ⟨nodes, words⟩ := tableFor_records store head hints fit data
  dsimp only
  rw [nodes, words, List.length_map, List.length_map]
  exact ⟨List.length_ofFn, List.length_ofFn⟩

private theorem live_gates (store : Store) (start head : Nat) (hints : List Bytes) :
    ∀ r ∈ liveInputs (p := SP1Prime) store start head hints, IsBool r.1.first ∧ r.1.active = 1 := by
  induction hints generalizing head start with
  | nil => simp [liveInputs]
  | cons b bs ih =>
    intro r member
    rcases List.mem_append.mp member with here | later
    · obtain ⟨s, used, rfl⟩ := List.mem_map.mp here
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp used
      dsimp only [shape]
      split <;> simp [IsBool]
    · exact ih _ _ _ later

private theorem selected_pulls {I : Type} {M : TypeMap} [ProvableType M] (ch : Channel F M)
    (gate : I → F) (value : I → M F) (rs : List I) (msg : Array F) (binary : ∀ r ∈ rs, IsBool (gate r)) :
    balanceOf (rs.map (fun r => ch.pulledIfValue (gate r) (value r))) msg =
      balanceOf ((rs.filterMap (fun r => if gate r = 1 then some (value r) else none)).map ch.pulledValue) msg := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have next := ih (fun r hr => binary r (List.mem_cons_of_mem _ hr))
    rcases binary r List.mem_cons_self with z | o
    · simp only [List.map_cons, List.filterMap_cons, z, zero_ne_one, ↓reduceIte, balanceOf_cons, next]
      simp [Channel.pulledIfValue, Interaction.signedMult]
    · simp only [List.map_cons, List.filterMap_cons, o, ↓reduceIte, balanceOf_cons, next]
      rfl

/-- Paid signed reads on the generated physical snapshot are precisely the represented target
demand, including every final padded word and exactly one metadata use per live buffer. -/
theorem tableFor_demands (store : Store) (head : Nat) (hints : List Bytes) (fit : fits hints = true)
    (data : ProverData F) (msg : Array F) :
    let t := tableFor store head hints fit data
    let q := TraceGen.HintQueueReaders.snapshot store head hints
    balanceOf (t.interactionsWith nodeChannel.toRaw) msg = balanceOf (q.nodes.map nodeChannel.pulledValue) msg ∧
    balanceOf (t.interactionsWith wordChannel.toRaw) msg = balanceOf (q.words.map wordChannel.pulledValue) msg := by
  obtain ⟨nodes, words⟩ := tableFor_records store head hints fit data
  let live := liveInputs (p := SP1Prime) store 0 head hints
  have padding {M : TypeMap} [ProvableType M] (ch : Channel F M) (v : M F) (n : Nat) :
      balanceOf (List.replicate n (ch.pulledIfValue 0 v)) msg = 0 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.replicate_succ, balanceOf_cons, ih]
      simp [Channel.pulledIfValue, Interaction.signedMult]
  rw [inputs_eq_padded store head hints fit] at nodes words
  dsimp only
  rw [nodes,words]
  simp only [List.map_append,List.map_replicate,Shape.padding,balanceOf_append,padding,add_zero]
  constructor
  · exact selected_pulls _ _ _ live msg (fun r hr => (live_gates store 0 head hints r hr).1)
  · apply congrArg (fun xs => balanceOf xs msg)
    simp only [TraceGen.HintQueueReaders.snapshot, List.map_map]
    apply List.map_congr_left
    intro r member
    rw [(live_gates store 0 head hints r member).2]
    rfl

end SP1Clean.HostHintSnapshot
