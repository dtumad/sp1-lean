import SP1Clean.Proofs.Completeness.MixedTargetMemory
import SP1Clean.Soundness.FinalMemoryChecks

/-! # Building the native target-value consumers from the ordered terminal records

The two original checkers each consume every finalizer record of their own address kind.
The source and target snapshots determine the change selector. Active rows retain the full
clock, word, and address, and the table is padded to its real physical demand height.
-/

namespace SP1Clean.TraceGen.MixedTargetMemory

open Circuit Air.Flat Semantics Soundness Machine FormalModel.Shard Channels
open WriteProbe.SparseBoundary WitnessGeneration

private abbrev F := ZMod SP1Prime

/-- The two original target validator components as they appear in the native verifier. -/
def checkComponent (target : MemorySnapshot) (ram : Bool) : Component F :=
  if ram then (FinalMemoryChecks.checkTables target)[1]'(by change 1 < 4; decide)
  else (FinalMemoryChecks.checkTables target)[0]'(by change 0 < 4; decide)

private abbrev payload (ram : Bool) : TypeMap := if ram then FinalRamCheck.Inputs else FinalRegisterCheck.Inputs

private instance (ram : Bool) : ProvableType (payload ram) := by
  cases ram <;> dsimp [payload] <;> infer_instance

private instance : Hashable MemLoc := ⟨fun loc => hash loc.busAddress⟩

private def input (ram : Bool) (changed : Std.HashSet MemLoc) (record : MemoryMsg F) : payload ram F :=
  let selected : F := if changed.contains (MemoryMsg.locOf record) then 1 else 0
  match ram with
  | false => ⟨record,selected⟩
  | true => ⟨record,selected⟩

private def inputs (source target : MemorySnapshot) (ram : Bool) (rows : List (Terminal F)) : List (payload ram F) :=
  let changed := Std.HashSet.ofList (source.changes target)
  (rows.filter (fun r => r.ram == ram)).map (fun r => input ram changed r.record)

private theorem inputs_length (source target : MemorySnapshot) (ram : Bool) (rows : List (Terminal F)) :
    (inputs source target ram rows).length = (rows.filter (fun r => r.ram == ram)).length := by
  simp [inputs]

/-- Compile every terminal exactly once on the corresponding native target-check component. -/
def checkTable (source target : MemorySnapshot) (ram : Bool) (rows : List (Terminal F)) (data : ProverData F)
    (fit : demandHeight (rows.filter (fun r => r.ram == ram)).length ≤ UInt64.size) : Table F :=
  match ram with
  | false => Table.ofInputs (checkComponent target false) (guardedRows (inputs source target false rows)) data
      ((guardedRows_length _).trans_le (by rw [inputs_length]; exact fit)) (fun _ => trivial)
  | true => Table.ofInputs (checkComponent target true) (guardedRows (inputs source target true rows)) data
      ((guardedRows_length _).trans_le (by rw [inputs_length]; exact fit)) (fun _ => trivial)

private theorem reg_input (source target : MemorySnapshot) (r : Terminal F) (valid : FinalRegisterValue.Spec target r.record) (d : ProverData F) (h : ProverHint F) :
    (FinalRegisterCheck.circuit target).ProverAssumptions (input false (Std.HashSet.ofList (source.changes target)) r.record,1) d h := by
  let built := input false (Std.HashSet.ofList (source.changes target)) r.record
  have generated : FinalRegisterCheck.populate? source target r.record = some (built,1) := by
    by_cases changed : MemoryMsg.locOf r.record ∈ source.changes target <;>
      simp [built, input, FinalRegisterCheck.populate?, FinalRegisterValue.populate?, valid, Std.HashSet.contains_ofList, changed]
  exact (FinalRegisterCheck.populate?_sound source target r.record _ generated d h).1

private theorem ram_input (source target : MemorySnapshot) (r : Terminal F) (valid : FinalRamValue.Spec target r.record) (d : ProverData F) (h : ProverHint F) :
    (FinalRamCheck.circuit target).ProverAssumptions (input true (Std.HashSet.ofList (source.changes target)) r.record,1) d h := by
  let built := input true (Std.HashSet.ofList (source.changes target)) r.record
  have generated : FinalRamCheck.populate? source target r.record = some (built,1) := by
    by_cases changed : MemoryMsg.locOf r.record ∈ source.changes target <;>
      simp [built, input, FinalRamCheck.populate?, FinalRamValue.populate?, valid, Std.HashSet.contains_ofList, changed]
  exact (FinalRamCheck.populate?_sound source target r.record _ generated d h).1

/-- The original active and padding rows satisfy both constraints and interaction guarantees. -/
theorem checkTable_valid (source target : MemorySnapshot) (ram : Bool) (rows : List (Terminal F)) (data : ProverData F) (fit)
    (checked : ∀ r ∈ rows, if r.ram then FinalRamValue.Spec target r.record else FinalRegisterValue.Spec target r.record) :
    (checkTable source target ram rows data fit).Constraints ∧ (checkTable source target ram rows data fit).Guarantees := by
  cases ram <;> unfold checkTable <;> apply Table.ofInputs_valid <;> intro row member
  all_goals
    rcases List.mem_append.mp member with active | padding
    · obtain ⟨entry,inside,rfl⟩ := List.mem_map.mp active
      unfold inputs at inside
      obtain ⟨r,used,rfl⟩ := List.mem_map.mp inside
      obtain ⟨listed,tag⟩ := List.mem_filter.mp used
      have ready := checked r listed
      rw [eq_of_beq tag] at ready
      first | exact reg_input source target r ready _ _ | exact ram_input source target r ready _ _
    · obtain ⟨_,rfl⟩ := List.mem_replicate.mp padding
      exact ⟨Or.inl rfl,fun h => (zero_ne_one h).elim⟩

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (keys : List ℕ) (data : ProverData F) (hint : ProverHint F)

/-- Build the actual target validator from the mixed tape at its physical demand height. -/
noncomputable def fromExecution (ram : Bool) : Table F :=
  let tape := MixedMemoryHistory.stream image source events rows
  checkTable source.sail.memorySnapshot target.sail.memorySnapshot ram (terminals source.sail.memorySnapshot tape keys data hint) data
    (terminal_count_fit ram _ _ _ (MixedMemoryHistory.canonical run routed) data hint)

/-- The generated native target checkers require only the real bounded execution and its routing. -/
theorem fromExecution_valid (ram : Bool) :
    (fromExecution run routed keys data hint ram).Constraints ∧ (fromExecution run routed keys data hint ram).Guarantees :=
  checkTable_valid _ _ ram _ data _ (fun _ used => terminal_spec run routed keys data hint used)

end SP1Clean.TraceGen.MixedTargetMemory
