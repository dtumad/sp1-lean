import SP1Clean.Proofs.Completeness.MixedTargetChecks
import SP1Clean.Proofs.Completeness.MixedSnapshotMembership

/-! # Counting the original target register and RAM memberships

Each guarded register or RAM checker has its own fixed membership resource. Its actual signed
private ledger determines all physical counts, including repeated interval reads at the target.
-/

namespace SP1Clean.TraceGen.MixedTargetMemory

open Circuit Air.Flat Semantics Soundness Machine FormalModel.Shard Channels
open WriteProbe.SparseBoundary SnapshotReadDirections

private abbrev F := ZMod SP1Prime

/-- Original verifier-fixed resource of each target check component. -/
def targetMembers (target : MemorySnapshot) (ram : Bool) : StaticTable F (MembershipRow ram) :=
  match ram with
  | false => FinalRegisterValue.membership target
  | true => InitialMemoryLookup.membership target.memory (2^48) "sp1.native.target_memory"

/-- Native target resources fit Clean's physical fixed-row index. -/
theorem targetMembers_fit (target : MemorySnapshot) (ram : Bool) : (targetMembers target ram).height < UInt64.size := by
  cases ram
  · exact FinalRegisterValue.membership_height_lt_uint64 target
  · exact InitialMemoryLookup.membership_height_lt_uint64 target.memory _

private theorem reads (target : MemorySnapshot) (ram : Bool) :
    ∀ a ∈ (checkComponent target ram).operations.interactionsWith (targetMembers target ram).channel.toRaw, a.direction = .pull := by
  classical
  intro a used
  cases ram
  · simp only [checkComponent, Bool.false_eq_true, ↓reduceIte, FinalMemoryChecks.checkTables,
      List.getElem_cons_zero, Component.interactionsWith_eq, Component.rowOperations,
      FinalRegisterCheck.circuit, Guarded.circuit] at used
    rw [Guarded.main_interactionsWith] at used
    obtain ⟨x, member, rfl⟩ := List.mem_map.mp used
    have all (i : Var FinalRegisterCheck.Inputs F) (n : ℕ) :
        ((FinalRegisterCheck.main target i).operations n).interactions.all
          (fun a => a.direction == .pull || a.channel.name != "sp1.native.target_registers") = true := by
      simp only [FinalRegisterCheck.main, FinalRegisterValue.circuit, FinalRegisterValue.main, FinalMemoryChange.circuit,
        FinalMemoryChange.main, circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions, FormalAssertion.toSubcircuit_interactions]
      rfl
    obtain ⟨raw, channel⟩ := List.mem_filter.mp member
    have checked := List.all_eq_true.mp (all _ _) x raw
    have same : x.channel = (targetMembers target false).channel.toRaw := of_decide_eq_true channel
    rw [same] at checked
    change (x.direction == .pull || "sp1.native.target_registers" != "sp1.native.target_registers") = true at checked
    change x.direction = .pull
    simpa using checked
  · simp only [checkComponent, ↓reduceIte, FinalMemoryChecks.checkTables,
      List.getElem_cons_zero, List.getElem_cons_succ, Component.interactionsWith_eq, Component.rowOperations,
      FinalRamCheck.circuit, Guarded.circuit] at used
    rw [Guarded.main_interactionsWith] at used
    obtain ⟨x,member,rfl⟩ := List.mem_map.mp used
    have words (i : Var Word F) (n : ℕ) : ((InitialMemoryRead.main target.memory i "sp1.native.target_memory").operations n).interactions.all (allowed true) = true :=
      wordAllowed true target.memory i n
    have equal (i : Var (ProvablePair Word Word) F) (n : ℕ) : (((Gadgets.Equality.circuit (F := F) Word).main i).operations n).interactions.all (allowed true) = true :=
      otherChannels true (Gadgets.Equality.circuit (F := F) Word).base (by rfl) i n
    have changes (i : Var FinalMemoryChange.Inputs F) (n : ℕ) :
        (((FinalMemoryChange.circuit (p := SP1Prime) true).main i).operations n).interactions.all (allowed true) = true :=
      otherChannels true (FinalMemoryChange.circuit true).base (by rfl) i n
    have all (i : Var FinalRamCheck.Inputs F) (n : ℕ) :
        ((FinalRamCheck.main target i).operations n).interactions.all (allowed true) = true := by
      simp only [FinalRamCheck.main, FinalRamValue.circuit, FinalRamValue.main, InitialMemoryRead.circuitNamed, circuit_norm,
        GeneralFormalCircuit.toSubcircuit_interactions, FormalAssertion.toSubcircuit_interactions, List.all_append, words]
      exact ⟨equal _ _, changes _ _⟩
    obtain ⟨raw,channel⟩ := List.mem_filter.mp member
    have checked := List.all_eq_true.mp (all _ _) x raw
    have same : x.channel = (targetMembers target true).channel.toRaw := of_decide_eq_true channel
    change (x.direction == .pull || x.channel.name != "sp1.native.target_memory") = true at checked
    rw [same] at checked
    change (x.direction == .pull || "sp1.native.target_memory" != "sp1.native.target_memory") = true at checked
    change x.direction = .pull
    simpa using checked

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (keys : List ℕ) (data : ProverData F) (hint : ProverHint F)

/-- Preallocate the original target inventory at its exact height from the genuine mixed checks. -/
theorem target_memberships (ram : Bool) :
    let client := fromExecution run routed keys data hint ram
    let fixed := targetMembers target.sail.memorySnapshot ram
    ∃ ids, fixed.readers? (client.interactionsWith fixed.channel.toRaw) = some ids ∧
      let provider := fixed.buildMembership (targetMembers_fit _ ram) (fun i => ((ReaderCounts.counts ids)[i] : F)) data
      provider.Constraints ∧ provider.Guarantees ∧ provider.length = fixed.height ∧
        LogUpBalanced (provider.interactionsWith fixed.channel.toRaw ++ client.interactionsWith fixed.channel.toRaw) := by
  intro client fixed
  apply fixed.fromClient _ client _ (fromExecution_valid run routed keys data hint ram) _ data
  · cases ram <;> intro _ _ <;> exact fun _ => trivial
  · cases ram <;> exact reads _ _

end SP1Clean.TraceGen.MixedTargetMemory
