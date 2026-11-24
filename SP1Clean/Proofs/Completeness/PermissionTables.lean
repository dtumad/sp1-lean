import SP1Clean.Soundness.WritePermissionBalance
import SP1Clean.Math.SP1Field
import ToClean.Air.GuardedLedger
import ToClean.Air.StaticMembershipReaders

/-! # Generating the native permission tables at their actual byte demand

The dynamic guard checks one complete writable-interval membership for each requested byte.
Its fixed provider counts those exact signed interval pulls, including repeated equal requests.
-/

namespace SP1Clean.TraceGen.PermissionTables

open Circuit Air.Flat WitnessGeneration Semantics WritePermissionProvider

private abbrev F := ZMod SP1Prime

/-- Canonical typed permission inputs, preserving the order and multiplicities of the byte writes. -/
def inputs (bytes : List ℕ) : List (Inputs F) := bytes.map (fun addr => ⟨Address.ofNat addr⟩)

/-- The original guarded table at the rounded physical height of all requested bytes. -/
def table (image : ProgramImage) (bytes : List ℕ) (data : ProverData F)
    (fit : demandHeight bytes.length ≤ UInt64.size) : Table F :=
  Table.ofInputs (component image) (guardedRows (inputs bytes)) data
    ((guardedRows_length _).trans_le (by simpa only [inputs, List.length_map] using fit)) (fun _ => trivial)

/-- All physical constraints and guarantees follow from the actual writable byte addresses. -/
theorem valid (image : ProgramImage) (bytes : List ℕ) (data : ProverData F) (fit)
    (permitted : ∀ addr ∈ bytes, addr < 2 ^ 48 ∧ image.readOnly addr = false) :
    (table image bytes data fit).Constraints ∧ (table image bytes data fit).Guarantees := by
  apply Table.ofInputs_valid
  apply guardedRows_all (Spec image)
  intro i used
  obtain ⟨addr,listed,rfl⟩ := List.mem_map.mp used
  obtain ⟨bounded,allowed⟩ := permitted addr listed
  exact ⟨Address.bounded_ofNat _, by simpa only [Address.toNat_ofNat _ bounded] using bounded,
    by simpa only [Address.toNat_ofNat _ bounded] using allowed⟩

/-- Each original guard row gives one permission push at its own activity, including padding. -/
theorem ledger (image : ProgramImage) (bytes : List ℕ) (data : ProverData F) (fit) :
    (table image bytes data fit).interactionsWith channel.toRaw =
      (guardedRows (F := F) (inputs bytes)).map (fun row => channel.pushedIfValue row.2 row.1.address) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger
  intro env
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((((circuit image).main (varFromOffset RowInput 0)).operations (size RowInput)).interactionsWith channel.toRaw).map _ = _
  rw [Soundness.WritePermission.provider_emission]
  simp only [List.map_singleton, AbstractInteraction.eval_guard, Channel.eval_pushed]
  apply congrArg List.singleton
  change _ = channel.pushedIfValue (valueFromOffset RowInput 0 env).2 (valueFromOffset RowInput 0 env).1.address
  rw [← eval_varFromOffset_valueFromOffset RowInput 0 env]
  simp only [varFromOffset_pair, circuit_norm, explicit_provable_type, Channel.pushedIfValue, Channel.pushedValue, mul_one]

/-- Discarding only zero weights leaves one unit push per actual byte, with repeats preserved. -/
theorem byte_sum (image : ProgramImage) (bytes : List ℕ) (data : ProverData F) (fit) (msg : Array F) :
    balanceOf ((table image bytes data fit).interactionsWith channel.toRaw) msg =
      balanceOf ((bytes.map (fun a => Address.ofNat (p := SP1Prime) a)).map channel.pushedValue) msg := by
  rw [ledger, guarded_push_sum channel _ Inputs.address]
  simp only [inputs, List.map_map, Function.comp_def]

private theorem interval_pulls (image : ProgramImage) :
    ∀ a ∈ (component (p := SP1Prime) image).operations.interactionsWith image.writePermissionTable.channel.toRaw,
      a.direction = .pull := by
  classical
  intro a used
  rw [Component.interactionsWith_eq] at used
  change a ∈ ((Guarded.main (activeCircuit image) (guard_supported image) (varFromOffset RowInput 0)).operations
    (size RowInput)).interactionsWith _ at used
  rw [Guarded.main_interactionsWith] at used
  obtain ⟨x, member, rfl⟩ := List.mem_map.mp used
  obtain ⟨raw,selected⟩ := List.mem_filter.mp member
  change x ∈ ((activeMain image _).operations _).interactions at raw
  rw [activeMain_interactions] at raw
  rcases List.mem_cons.mp raw with rfl | tail
  · rfl
  · cases List.mem_singleton.mp tail
    have same := congrArg RawChannel.name (of_decide_eq_true selected)
    have name : (image.writePermissionTable (p := SP1Prime)).channel.toRaw.name = "sp1.native.write_permission" := by
      simp [ProgramImage.writePermissionTable, StaticTable.channel, StaticTable.ofRows, Channel.toRaw]
    rw [name] at same
    exact False.elim ((by decide : "SP1WritePermission" ≠ "sp1.native.write_permission") same)

/-- The physical fixed membership counts fund the entire signed interval ledger of the guard. -/
theorem membership (image : ProgramImage) (bytes : List ℕ) (data : ProverData F) (fit)
    (permitted : ∀ addr ∈ bytes, addr < 2 ^ 48 ∧ image.readOnly addr = false) :
    let t := image.writePermissionTable (p := SP1Prime)
    let guard := table image bytes data fit
    ∃ ids, t.readers? (guard.interactionsWith t.channel.toRaw) = some ids ∧
      let physical := t.buildMembership (membership_height_lt_uint64 image) (fun i => ((ReaderCounts.counts ids)[i] : F)) data
      physical.Constraints ∧ physical.Guarantees ∧ physical.length = t.height ∧
        LogUpBalanced (physical.interactionsWith t.channel.toRaw ++ guard.interactionsWith t.channel.toRaw) := by
  intro t guard
  apply t.fromClient _ guard _ (valid image bytes data fit permitted) _ data
  · intro _ _ _; trivial
  · exact interval_pulls image

end SP1Clean.TraceGen.PermissionTables
