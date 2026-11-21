import SP1Clean.Export.InstalledHintAssembly
import SP1Clean.Soundness.ResourceFootprint

/-! # Required capacity of the installed verifier-fixed RAM membership provider

Every retained interval and every padded row emits a membership occurrence on the target RAM
channel. Its physical height is fixed by the public snapshot, even for a shard with no events.
-/

namespace SP1Clean.InitialMemoryLookup
open Semantics

/-- The verifier preallocates the next power of two above the exact interval count. -/
theorem membership_height (memory : ByteMemory) (limit : ℕ) (name : String) :
    (membership (p := SP1Prime) memory limit name).height =
      2 ^ Nat.clog 2 (memory.intervals limit).length := by
  change 2 ^ Nat.clog 2 (memory.fixedTable (p := SP1Prime) limit).length = _
  rw [ByteMemory.fixedTable_length]

/-- A fixed RAM slot fits the field exactly when the snapshot has fewer than 2^30
interior byte changes. Other consumers still share the same channel. -/
theorem membership_height_lt_prime_iff (memory : ByteMemory) (limit : ℕ) (name : String) :
    (membership (p := SP1Prime) memory limit name).height < SP1Prime ↔
      (memory.changePoints limit).card < 2 ^ 30 := by
  rw [membership_height, ByteMemory.intervals_length]
  have exactCut (exponent : ℕ) : 2 ^ exponent < SP1Prime ↔ exponent ≤ 30 := by
    constructor
    · intro small
      by_contra! large
      have lower := Nat.pow_le_pow_right (by decide : 0 < 2) (show 31 ≤ exponent by omega)
      exact (Nat.not_lt_of_ge ((by decide : SP1Prime ≤ 2 ^ 31).trans lower)) small
    · intro small
      exact (Nat.pow_le_pow_right (by decide : 0 < 2) small).trans_lt (by decide)
  rw [exactCut, Nat.clog_le_iff_le_pow (by decide)]
  by_cases positive : 0 < limit
  · rw [ite_eq_left positive]
    omega
  · obtain rfl : limit = 0 := by omega
    have noCuts : memory.changePoints 0 = ∅ := by ext; simp
    simp [noCuts]

end SP1Clean.InitialMemoryLookup

namespace SP1Clean.FormalModel.Shard
open Semantics Machine

/-- A public ceiling on total boundary payload bounds the preallocated RAM provider at both
complete endpoints. The field has the stated remaining capacity even at maximum padded height;
for any independent strict capacity, the last equivalence gives the exact budget left after
the endpoint's actual provider height. Other occurrences include all consumers of its channel. -/
theorem AdmissibleExecution.endpoint_ram_capacity {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits SP1Prime image source target events)
    (ceiling : limits.boundaryBytes ≤ 2 ^ 29 + 124) :
    ∀ endpoint ∈ [source, target], ∀ name : String,
      let height := (InitialMemoryLookup.membership (p := SP1Prime) endpoint.sail.memory
        NativeLayout.sailMemory.upper name).height
      height ≤ 2 ^ 30 ∧
      (∀ other ≤ SP1Prime - 1 - 2 ^ 30, height + other < SP1Prime) ∧
      ∀ capacity other : ℕ, height + other < capacity ↔
        height < capacity ∧ other ≤ capacity - 1 - height := by
  intro endpoint member name
  have checked : endpoint.realize.resources.Fits limits := by
    rcases List.mem_cons.mp member with rfl | last
    · exact execution.2.2.2.1
    · obtain rfl := List.mem_singleton.mp last
      exact execution.2.2.2.2.1
  rw [endpoint.resources_realize] at checked
  have payload := checked .boundaryBytes
  change endpoint.resources .boundaryBytes ≤ limits.boundaryBytes at payload
  have overhead : (endpoint.sail.memory.supportBelow NativeLayout.sailMemory.upper).card + 125 ≤
      endpoint.resources .boundaryBytes := by
    simp only [ExecutionSnapshot.resources, HostState.payloadCost, hintPayloadCost, bytePayloadCost]
    omega
  have count : 2 * (endpoint.sail.memory.supportBelow NativeLayout.sailMemory.upper).card + 1 ≤ 2 ^ 30 := by
    omega
  have rows := (endpoint.sail.memory.intervals_length_le NativeLayout.sailMemory.upper).trans count
  have padded := Nat.pow_le_pow_right (by decide : 0 < 2) ((Nat.clog_le_iff_le_pow (by decide)).mpr rows)
  dsimp only
  rw [InitialMemoryLookup.membership_height]
  refine ⟨padded, ?_, ?_⟩
  · intro other remaining
    exact (Nat.add_le_add padded remaining).trans_lt (by decide)
  · intro capacity other
    omega

end SP1Clean.FormalModel.Shard

namespace SP1Clean.Export.InstalledAssembly
open Air.Flat Semantics Soundness

private abbrev targetRam (context : Context) :=
  InitialMemoryLookup.membership (p := SP1Prime) context.target.sail.memory (2 ^ 48) "sp1.native.target_memory"

private theorem heightBound (context : Context) : (targetRam context).height < UInt64.size :=
  InitialMemoryLookup.membership_height_lt_uint64 _ _

private abbrev memoryAssembly (context : Context) :=
  HostFinalMemory.Installed context.image context.source context.target (context.withClock 0).finalHints

private def memorySlot (context : Context) :
    TableSlot (memoryAssembly context).tables ((targetRam context).component (heightBound context)) :=
  HostFinalMemory.checkSlot (image := context.image) (source := context.source)
    (target := context.target.sail.memorySnapshot) (final := (context.withClock 0).finalHints)
    (bankFinal := context.target.host) (names := HostFinalMemory.source_unique_names ..)
    (registration := HostFinalMemory.source_registration ..) 3

private theorem outside_receipts (context : Context) :
    ¬ (7 ≤ (memorySlot context).index.val ∧ (memorySlot context).index.val < 32) := by
  simp only [memorySlot, HostFinalMemory.checkSlot, TableSlot.cast_index,
    TableSlot.setOther, TableSlot.appendRight, TableSlot.ofIndex, HostFinalMemory.prefix_length]
  omega

attribute [local irreducible] assembly memorySlot HostFinalMemory.ensemble

private def targetRamSlot (context : Context) :
    TableSlot (assembly context).tables ((targetRam context).component (heightBound context)) :=
  ((HostObserved.retainedSlot (memorySlot context) (outside_receipts context)).appendLeft
    [CommitmentDeclaration.source context.commitments, HostHintQueueTerminal.component (publicCursor context)]).cast
      (tables_eq context).symm

/-- Every accepted raw statement already limits the actual byte changes of the supplied target RAM by its
fixed provider alone. The bound is independent of event count, multiplicities and public ceilings. -/
theorem target_ram_changes_of_statement (context : Context) {header : SP1PublicIO Fp} {heights : List ℕ}
    (accepted : (assembly context).Statement .logUp header heights) :
    (context.target.sail.memory.changePoints NativeLayout.sailMemory.upper).card < 2 ^ 30 := by
  obtain ⟨fit, witness, _, heightEq, _, _⟩ := accepted
  rw [← heightEq] at fit
  let slot := targetRamSlot context
  let table := slot.table witness
  have component : table.component = (targetRam context).component (heightBound context) := slot.table_component witness
  have fixed := table.fixed_rows_match
  rw [component] at fixed
  have physical : table.length = (targetRam context).height := fixed.1
  let channel := (targetRam context).channel.toRaw
  have registered : channel ∈ (assembly context).channels := by
    apply (assembly context).tables_channels table.component
      (EnsembleWitness.component_mem_tables_of_mem (slot.table_mem witness))
    rw [component]
    exact List.mem_singleton_self _
  have emits : 0 < table.component.channelWidth channel := by
    rw [component]
    simp [Component.channelWidth, Component.interactionsWith_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, circuit_norm, channel]
  have bound := ResourceEnsemble.accepted_table_budget witness ((witness.interactionsFit_iff .logUp).mp fit)
    (slot.table_mem witness) registered emits
  rw [physical] at bound
  apply (InitialMemoryLookup.membership_height_lt_prime_iff _ _ _).mp
  exact Nat.lt_of_le_of_lt bound (by decide)

/-- No choice of prover rows or announced heights admits a target with this many changes between neighboring bytes
through the current installed representation. -/
theorem not_statement_of_target_ram_changes (context : Context)
    (large : 2 ^ 30 ≤ (context.target.sail.memory.changePoints NativeLayout.sailMemory.upper).card)
    (header : SP1PublicIO Fp) (heights : List ℕ) : ¬ (assembly context).Statement .logUp header heights :=
  fun accepted => (Nat.not_lt_of_ge large) (target_ram_changes_of_statement context accepted)

end SP1Clean.Export.InstalledAssembly
