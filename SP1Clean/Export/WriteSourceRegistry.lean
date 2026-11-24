import SP1Clean.Soundness.HostObserved
import SP1Clean.Soundness.WriteAccessInventory
import SP1Clean.FormalModel.ShardHeader

/-! # Installing the native WRITE read-back sources

Each publisher decorates a particular component of the physical supervisor registry.
The indices refer to the registry before the final host boundary is chosen, so the same
registration works for a cursor reached after allocating new hint nodes.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Semantics Soundness WriteProbe WriteProbe.AccessInventory

/-- Canonical position in the supervisor registry. The ordinary order is owned by
`InstructionChipId.all`. -/
def position : Source → ℕ
  | .ordinary id => 7 + InstructionChipId.all.idxOf id
  | .finalizer false => 3
  | .finalizer true => 4
  | .refresh => 55
  | .host .ecall => 58
  | .host (.word false) => 84
  | .host (.word true) => 85

/-- The publication uses the same row cells, generation mode and original constraints. -/
def publisher {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] : Source → Component (ZMod p)
  | .ordinary id => OrdinarySources.component id
  | .host family => HostSources.component family
  | .refresh => have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
                refreshComponent
  | .finalizer ram => have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
                      finalComponent ram

theorem publisher_name (id : Source) :
    (publisher (p := SP1Prime) id).circuit.name = (original (p := SP1Prime) id).circuit.name := by
  cases id with
  | ordinary id => exact Receipt.many_name _ _ _ _
  | host family => exact Receipt.many_name _ _ _ _
  | refresh => rfl
  | finalizer ram => rfl

theorem publisher_channels (id : Source) {ch : RawChannel (ZMod SP1Prime)}
    (used : ch ∈ (publisher id).circuit.channels) :
    ch ∈ (original id).circuit.channels ∨ ch = readbackChannel.toRaw := by
  cases id with
  | ordinary id => exact Receipt.many_channels _ _ _ _ used
  | host family => exact Receipt.many_channels _ _ _ _ used
  | refresh => exact Receipt.channel_of_receipt _ _ (fun _ _ => trivial) _ used
  | finalizer ram => exact Receipt.channel_of_receipt _ _ (fun _ _ => trivial) _ used

/-- The 31 producers occupy distinct physical components. -/
theorem distinct : (sources.map position).Nodup := by decide

variable (image : ProgramImage) (source target : ExecutionSnapshot) (final : HostHintQueue.State (ZMod SP1Prime))

/-- The supervisor carrying the original host and memory protocols at an arbitrary target cursor. -/
def base := HostObserved.ensemble (p := SP1Prime) image source target final

private abbrev initial := HostFinalMemory.Installed (p := SP1Prime) image source target final

private theorem base_tables : (base image source target final).tables =
    (initial image source target final).tables.mapIdx HostOrdinaryReceipts.replace := by
  simp only [base, HostObserved.ensemble, ClosedVerifier.withInteractions, HostObserved.producers,
    HostOrdinaryReceipts.ensemble, HostSailBoundary.ensemble, PublicVerifier.install, initial, HostFinalMemory.Installed]

private theorem initial_length : (initial image source target final).tables.length = 98 := by
  simp only [initial, HostFinalMemory.Installed, HostFinalMemory.tables_eq, List.length_set, List.length_append,
    HostFinalMemory.prefix_length, FinalMemoryChecks.checkTables, List.length_cons, List.length_nil]
  rfl

/-- Number of components before the packet and endpoint extensions. -/
theorem base_length : (base image source target final).tables.length = 98 := by
  rw [base_tables, List.length_mapIdx, initial_length]

private theorem original_ordinary (id : InstructionChipId) :
    (base image source target final).tables[position (.ordinary id)]? = some (original (.ordinary id)) := by
  have bound : InstructionChipId.all.idxOf id < 25 := List.idxOf_lt_length_iff.mpr (InstructionChipId.mem_all id)
  rw [base_tables, List.getElem?_mapIdx, List.getElem?_eq_getElem (by rw [initial_length]; change 7 + InstructionChipId.all.idxOf id < 98; omega)]
  simp only [position, Option.map_some, HostOrdinaryReceipts.replace,
    show 7 ≤ 7 + InstructionChipId.all.idxOf id ∧ 7 + InstructionChipId.all.idxOf id < 32 by omega,
    and_self, ↓reduceDIte, Nat.add_sub_cancel_left, List.getElem_idxOf, original]

private theorem outside (i : ℕ) (off : ¬(7 ≤ i ∧ i < 32)) :
    (base image source target final).tables[i]? = (initial image source target final).tables[i]? := by
  rw [base_tables, List.getElem?_mapIdx]
  rw [show HostOrdinaryReceipts.replace (p := SP1Prime) i = id by funext c; exact dite_eq_right off]
  exact congrFun Option.map_id _

/-- Receipt installation retains the original host/core tables between the lookup providers
and the target-memory checks, except for the HALT replacement. -/
theorem retained_at (i : ℕ) (lo : 32 ≤ i) (hi : i < 94) (other : i ≠ 57) :
    (base image source target final).tables[i]? =
      (HostFinalMemory.beforeChecks image source HostCallReceivers.available
        (HostHintReadLocal.sourceResources source.host.io.hints))[i]? := by
  rw [outside _ _ _ _ _ (by omega), initial, HostFinalMemory.Installed, HostFinalMemory.tables_eq,
    List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
    List.getElem?_append_left (by rw [HostFinalMemory.prefix_length]; exact hi)]

/-- The original target consumers and both snapshot providers occupy the four final positions. -/
theorem target_check_at (i : Fin 4) :
    (base image source target final).tables[94 + i.val]? =
      (FinalMemoryChecks.checkTables (p := SP1Prime) target.sail.memorySnapshot)[i.val]? := by
  rw [outside _ _ _ _ _ (by omega), initial, HostFinalMemory.Installed, HostFinalMemory.tables_eq,
    List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have size : (HostFinalMemory.beforeChecks (p := SP1Prime) image source HostCallReceivers.available
      (HostHintReadLocal.sourceResources source.host.io.hints)).length = 94 := by
    rw [HostFinalMemory.prefix_length]
    rfl
  rw [List.getElem?_append_right (by rw [size]; omega), size, Nat.add_sub_cancel_left]

private theorem core (i : ℕ) (lo : 32 ≤ i) (hi : i < 63) (other : i ≠ 57) :
    (base image source target final).tables[i]? = ((ProtectedLocalCore.tables image source).set 58 HostCallLedger.producer)[i]? := by
  rw [retained_at _ _ _ _ _ lo (by omega) other, HostFinalMemory.beforeChecks, HostLocalCore.tables,
    List.getElem?_append_left (by rw [List.length_set, ProtectedLocalCore.tables_length]; exact hi)]

private theorem word (last : Bool) :
    (base image source target final).tables[position (.host (.word last))]? = some (original (.host (.word last))) := by
  cases last <;>
    rw [retained_at _ _ _ _ _ (by decide) (by decide) (by decide), HostFinalMemory.beforeChecks, HostLocalCore.tables,
      List.getElem?_append_right (by rw [List.length_set, ProtectedLocalCore.tables_length]; decide),
      List.length_set, ProtectedLocalCore.tables_length] <;> rfl

private theorem final_slot (ram : Bool) :
    (base image source target final).tables[position (.finalizer ram)]? = some (original (.finalizer ram)) := by
  cases ram <;> rw [outside _ _ _ _ _ (by decide), initial, HostFinalMemory.Installed, HostFinalMemory.tables_eq]
  · simp only [position]
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by simp only [List.length_set, List.length_append, HostFinalMemory.prefix_length]; omega)]
    rfl
  · simp only [position]
    rw [List.getElem?_set_self (by simp only [List.length_set, List.length_append, HostFinalMemory.prefix_length]; omega)]
    rfl

private theorem prefix_core_slot (i : ℕ) (inside : i < 7) (reg : i ≠ 3) (ram : i ≠ 4) :
    (base image source target final).tables[i]? = (LocalCore.tables (p := SP1Prime) image source)[i]? := by
  rw [outside _ _ _ _ _ (by omega), initial, HostFinalMemory.Installed, HostFinalMemory.tables_eq,
    List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
    List.getElem?_append_left (by rw [HostFinalMemory.prefix_length]; omega), HostFinalMemory.beforeChecks,
    HostLocalCore.tables, List.getElem?_append_left (by rw [List.length_set, ProtectedLocalCore.tables_length]; omega), List.getElem?_set_ne (by omega)]
  simp only [ProtectedLocalCore.tables]
  rw [List.getElem?_append_left (by simp only [List.length_set, LocalCore.tables_length]; omega),
    List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

/-- The original lookup and boundary tables survive all ordinary, HALT and ECALL wrappers
outside the three replaced core positions and the instruction band. -/
theorem retained_core_at (i : ℕ) (hi : i < 61) (outsideInstructions : i < 7 ∨ 32 ≤ i)
    (reg : i ≠ 3) (ram : i ≠ 4) (halt : i ≠ 57) (syscall : i ≠ 58) :
    (base image source target final).tables[i]? = (LocalCore.tables (p := SP1Prime) image source)[i]? := by
  rcases outsideInstructions with lo | lo
  · exact prefix_core_slot _ _ _ _ i lo reg ram
  · rw [core _ _ _ _ i lo (by omega) halt,List.getElem?_set_ne (by omega),ProtectedLocalCore.tables,
      List.getElem?_append_left (by simp only [List.length_set,LocalCore.tables_length]; omega),
      List.getElem?_set_ne (by omega),List.getElem?_set_ne (by omega),List.getElem?_set_ne (by omega),List.getElem?_set_ne (by omega)]

/-- The padding component replaced by the HALT wrapper has the original position 57. -/
theorem halt_at : (base image source target final).tables[57]? = some HaltPaddingChip.component := by
  rw [outside _ _ _ _ _ (by decide),initial,HostFinalMemory.Installed,HostFinalMemory.tables_eq,
    List.getElem?_set_ne (by decide),List.getElem?_set_ne (by decide),List.getElem?_set_self]
  rw [List.length_append,HostFinalMemory.prefix_length]
  omega

/-- The fixed Program provider keeps its exact position after host and receipt installation. -/
theorem program_at :
    (base image source target final).tables[6]? = some (FixedProgramProvider.Preprocessed.component image) := by
  rw [prefix_core_slot _ _ _ _ 6 (by decide) (by decide) (by decide)]
  rfl

/-- The first six genuine supervisor slots are the two source providers and their seal,
followed by the two original receipt-publishing finalizers and their own seal. -/
theorem boundary_prefix :
    (base image source target final).tables.take 6 =
      [(SnapshotMemoryEnsemble.registerView source.sail.memorySnapshot).component,
       (SnapshotMemoryEnsemble.ramView source.sail.memorySnapshot).component,
       SnapshotMemoryEnsemble.terminalView.component, original (.finalizer false), original (.finalizer true),
       (OrderedMemoryEnsemble.terminalView OrderedFinalProvider.channelName (by decide)).component] := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take]
  by_cases bound : i < 6
  · rw [ite_eq_left bound]
    interval_cases i
    · rw [prefix_core_slot _ _ _ _ 0 (by decide) (by decide) (by decide)]; rfl
    · rw [prefix_core_slot _ _ _ _ 1 (by decide) (by decide) (by decide)]; rfl
    · rw [prefix_core_slot _ _ _ _ 2 (by decide) (by decide) (by decide)]; rfl
    · exact final_slot image source target final false
    · exact final_slot image source target final true
    · rw [prefix_core_slot _ _ _ _ 5 (by decide) (by decide) (by decide)]; rfl
  · rw [ite_eq_right bound, List.getElem?_eq_none (by change 6 ≤ i; omega)]

/-- Full component identity, including the executable scheduler and fixed-cell interpretation. -/
theorem original_at (id : Source) :
    (base image source target final).tables[position id]? = some (original id) := by
  cases id with
  | ordinary id => exact original_ordinary image source target final id
  | host family => cases family with
    | ecall =>
      rw [core _ _ _ _ _ (by decide) (by decide) (by decide)]
      simp only [position]
      rfl
    | word last => exact word image source target final last
  | refresh =>
    rw [core _ _ _ _ _ (by decide) (by decide) (by decide), List.getElem?_set_ne (by decide)]
    rfl
  | finalizer ram => exact final_slot image source target final ram

/-- Source selection is computed from the canonical typed inventory. -/
def sourceAt (index : ℕ) : Option Source := sources.find? (fun id => position id == index)

theorem sourceAt_position (id : Source) : sourceAt (position id) = some id := by
  cases id with
  | ordinary id => cases id <;> decide
  | host family => cases family with
    | ecall => decide
    | word last => cases last <;> decide
  | refresh => decide
  | finalizer ram => cases ram <;> decide

/-- Selection recovers the unique physical table index of its source. -/
theorem position_of_sourceAt {index : ℕ} {id : Source} (found : sourceAt index = some id) :
    position id = index := eq_of_beq (List.find?_some (p := fun candidate => position candidate == index) found)

/-- Publish the registered sources in place. All other physical components retain their
original generation modes and circuits. -/
def decorate (index : ℕ) (old : Component (ZMod SP1Prime)) : Component (ZMod SP1Prime) :=
  (sourceAt index).elim old publisher

theorem sameName (index : ℕ) (old : Component (ZMod SP1Prime))
    (installed : (base image source target final).tables[index]? = some old) :
    (decorate index old).circuit.name = old.circuit.name := by
  unfold decorate
  cases found : sourceAt index with
  | none => rfl
  | some id =>
    have same := original_at image source target final id
    rw [position_of_sourceAt found, installed] at same
    exact (publisher_name id).trans (congrArg (fun c => c.circuit.name) (Option.some.inj same).symm)

end SP1Clean.Export.WriteSourceRegistry
