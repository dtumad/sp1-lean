import SP1Clean.Export.WritePermissionInstallation

/-! # Physical support of the native write-permission channel -/

namespace SP1Clean.Export.WriteMixedPermissionLedger
open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard WritePermissionProvider WriteSourceRegistry WriteProbe.AccessInventory
private abbrev F := ZMod SP1Prime
private abbrev permBus := (channel (p := SP1Prime)).toRaw

private theorem outsideCore (image : ProgramImage) (source : ExecutionSnapshot) :
    permBus ∉ (LocalCore.baseEnsemble (p := SP1Prime) image source).channels := by
  simp [LocalCore.baseEnsemble,sp1Ensemble_channels,OrderedBoundary.channel,SnapshotMemoryEnsemble.channelName,
    OrderedFinalProvider.channelName,channel,circuit_norm]

variable {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}

/-- The public State, Sail, Memory and host endpoint checks all leave the original permission
ledger on its physical tables. -/
theorem verifier_silent (w : EnsembleWitness (base image source target finish)) :
    w.verifierInteractionsWith permBus = [] := by
  have registered : permBus ∈ HostLocalCore.registry image source (HintReadWordChip.stateChannel.toRaw ::
      HostFinalMemory.sourceChannels (p := SP1Prime) target.sail.memorySnapshot) := by simp [HostLocalCore.registry]
  let original := HostFinalMemory.Installed (p := SP1Prime) image source target finish
  have known : permBus ∈ original.channels := List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ registered))
  change (HostObserved.ensemble image source target finish).verifierOperations.interactionValuesWith permBus _ = []
  rw [HostObserved.verifier_interactions,ite_eq_right (by apply ne_of_apply_ne RawChannel.name; decide),List.append_nil]
  change ((SailBoundary.checker source target).install original).verifierOperations.interactionValuesWith permBus _ = []
  rw [PublicVerifier.install_verifier_interactions_of_mem _ _ _ _ known]
  apply HostFinalMemory.verifier_silent registered (outsideCore image source) _ (by apply ne_of_apply_ne RawChannel.name; decide)
  apply HostHintQueueBoundary.boundary_silent
  all_goals apply ne_of_apply_ne RawChannel.name; decide

private def quiet (c : Component F) := !(c.circuit.channels.map RawChannel.name).contains permBus.name

private theorem quiet_sound {c : Component F} (checked : quiet c = true) : permBus ∉ c.circuit.channels := by
  intro member
  change (!(c.circuit.channels.map RawChannel.name).contains permBus.name) = true at checked
  rw [List.contains_iff_mem.mpr (List.mem_map_of_mem member)] at checked
  cases checked

private abbrev hostTables (source : ExecutionSnapshot) :=
  (HostHintReadHandoff.receiver (p := SP1Prime) :: HostCallReceivers.available).map (·.component) ++
    (HostHintReadHandoff.wordResources ++ HostHintReadLocal.sourceResources source.host.io.hints)

private theorem hostSilent (source : ExecutionSnapshot) :
    ((hostTables source).take 21 ++ (hostTables source).drop 23).all quiet = true := by rfl

private theorem original_ordinary_silent (id : InstructionChipId)
    (other : position (.ordinary id) ∉ [25,26,27,28]) : permBus ∉ (original (.ordinary id)).circuit.channels := by
  cases id <;> first | (exact False.elim (other (by decide))) | (exact quiet_sound (of_decide_eq_true rfl))

/-- Physical positions of the four STORE tables, permission guard and both HINT_READ word tables. -/
def permissionPositions : List Nat := [25,26,27,28,61,84,85]

attribute [local irreducible] base HostLocalCore.tables LocalCore.tables

/-- Every other physical component of the original verifier is silent on byte permissions. -/
theorem table_silent {c : Component F} {i : ℕ} (location : (base image source target finish).tables[i]? = some c)
    (absent : i ∉ permissionPositions) : permBus ∉ c.circuit.channels := by
  have max := (List.getElem?_eq_some_iff.mp location).1
  rw [base_length] at max
  simp only [permissionPositions,List.mem_cons,List.not_mem_nil,or_false,not_or] at absent
  by_cases instructions : 7 ≤ i ∧ i < 32
  · let j : Fin InstructionChipId.all.length := ⟨i-7,by change i-7 < 25; omega⟩
    let id := InstructionChipId.all[j.val]
    have pos : position (.ordinary id) = i := by
      change 7 + InstructionChipId.all.idxOf InstructionChipId.all[j.val] = i
      rw [InstructionChipId.all_nodup.idxOf_getElem j]
      dsimp only [j]; omega
    have reg := original_at image source target finish (.ordinary id)
    rw [pos,location] at reg
    rw [Option.some.inj reg]
    exact original_ordinary_silent id (by rw [pos]; simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; exact ⟨absent.1,absent.2.1,absent.2.2.1,absent.2.2.2.1⟩)
  by_cases ordinary : i < 61
  · by_cases special : i = 3 ∨ i = 4 ∨ i = 57 ∨ i = 58
    · rcases special with rfl | rfl | rfl | rfl
      · rw [show (base image source target finish).tables[3]? = _ from original_at image source target finish (.finalizer false)] at location
        cases Option.some.inj location; exact quiet_sound (of_decide_eq_true rfl)
      · rw [show (base image source target finish).tables[4]? = _ from original_at image source target finish (.finalizer true)] at location
        cases Option.some.inj location; exact quiet_sound (of_decide_eq_true rfl)
      · rw [halt_at] at location
        cases Option.some.inj location; exact quiet_sound (of_decide_eq_true rfl)
      · rw [show (base image source target finish).tables[58]? = _ from original_at image source target finish (.host .ecall)] at location
        cases Option.some.inj location; exact quiet_sound (of_decide_eq_true rfl)
    rw [retained_core_at _ _ _ _ i ordinary (by omega) (by omega) (by omega) (by omega) (by omega)] at location
    exact fun member => outsideCore image source ((LocalCore.baseEnsemble (p := SP1Prime) image source).tables_channels c (List.mem_of_getElem? location) member)
  by_cases fixed : i = 62
  · subst i
    rw [show (base image source target finish).tables[62]? = _ from WriteMixedFixedResources.registered_at image source target finish (.permission true)] at location
    cases Option.some.inj location
    apply quiet_sound
    simp only [WriteMixedFixedResources.component,↓reduceIte,WritePermissionProvider.membershipComponent,ProgramImage.writePermissionTable]
    rfl
  by_cases host : i < 94
  · rw [retained_at _ _ _ _ i (by omega) host (by omega),HostFinalMemory.beforeChecks,HostLocalCore.tables,
      List.getElem?_append_right (by rw [List.length_set,ProtectedLocalCore.tables_length]; omega),List.length_set,ProtectedLocalCore.tables_length] at location
    change (hostTables source)[i-63]? = some c at location
    have mem : c ∈ (hostTables source).take 21 ++ (hostTables source).drop 23 := by
      by_cases early : i-63 < 21
      · exact List.mem_append_left _ (List.mem_of_getElem? (by rw [List.getElem?_take,ite_eq_left early,location]))
      · apply List.mem_append_right
        apply List.mem_of_getElem? (i := i-86)
        rwa [List.getElem?_drop,show 23+(i-86) = i-63 by omega]
    exact quiet_sound (List.all_eq_true.mp (hostSilent source) c mem)
  let j : Fin 4 := ⟨i-94,by omega⟩
  rw [show i = 94+j.val by dsimp only [j]; omega,target_check_at] at location
  have mem := List.mem_of_getElem? location
  have checked : (FinalMemoryChecks.checkTables (p := SP1Prime) target.sail.memorySnapshot).all quiet = true := by rfl
  exact quiet_sound (List.all_eq_true.mp checked c mem)

end SP1Clean.Export.WriteMixedPermissionLedger
