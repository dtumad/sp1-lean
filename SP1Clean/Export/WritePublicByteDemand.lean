import SP1Clean.Export.WriteByteProviderInstallation
import SP1Clean.Soundness.HostObservedConsumer

/-! # Authenticating the public verifier's original twelve Byte requests -/

namespace SP1Clean.Export.WritePublicByteDemand
open Circuit Air.Flat Semantics Soundness Channels WriteSourceRegistry ByteProviderDemand

private abbrev F := ZMod SP1Prime

private theorem state_sites (vars : Var SP1PublicIO F) :
    ((sp1StateVerifierProgram (p := SP1Prime)).main vars).circuitOperations.interactions =
      ((sp1StateVerifierMain vars).operations 0).interactions := by
  simp only [sp1StateVerifierProgram,Verifier.ofInteractions_interactions]

/-- Running the proved boundary circuit on its public header discharges all twelve original
Byte guarantees from exactly the limb bounds of the declared clocks and program counters. -/
theorem state_guarantees (data : ProverData F) (limbs : (data.getPublicInput SP1PublicIO).LimbBounds) :
    (sp1StateVerifierProgram (p := SP1Prime)).circuitOperations.FullGuarantees data.publicEnvironment := by
  let vars := varFromOffset (F := F) SP1PublicIO 0
  let env : ProverEnvironment F := ⟨data.publicEnvironment,.empty F⟩
  let ops := (sp1StateVerifierMain vars).operations 0
  have length : FlatOperation.localLength ops.toFlat = 0 :=
    FlatOperation.localLength_toFlat.trans ((sp1StateVerifier.localLength_eq vars 0).trans rfl)
  have uses : env.UsesLocalWitnesses 0 ops := by
    rw [ProverEnvironment.usesLocalWitnesses_iff_flat,ProverEnvironment.usesLocalWitnessesFlat_iff_extends]
    intro i
    exact (Nat.not_lt_zero i.val (lt_of_lt_of_eq i.isLt length)).elim
  have input : sp1StateVerifier.ProverAssumptions (eval env vars) env.data env.hint := by
    rw [CircuitType.eval_var_prover_to_verifier]
    change (eval data.publicEnvironment vars).LimbBounds
    rwa [← ProverData.getPublicInput_eq_eval]
  have honest := (sp1StateVerifier.original_full_completeness 0 env vars uses input).2
  change ((sp1StateVerifierProgram (p := SP1Prime)).main vars).circuitOperations.FullGuarantees data.publicEnvironment
  rw [Operations.FullGuarantees,state_sites]
  exact honest

/-- Public Byte sites are unit pulls of the original circuit. Their exact direction and
multiplicity hold for arbitrary public data before any balance argument. -/
theorem state_reader (env : Environment F) (i : Interaction F)
    (seen : i ∈ (sp1StateVerifierProgram (p := SP1Prime)).circuitOperations.interactionValuesWith byteChannel.toRaw env) :
    i.direction = .pull ∧ i.mult = 1 := by
  obtain ⟨a,used,rfl⟩ := List.mem_map.mp seen
  have onByte := Operations.channel_eq_of_mem_interactionsWith used
  have raw := List.mem_of_mem_filter used
  change a ∈ ((sp1StateVerifierProgram (p := SP1Prime)).main (varFromOffset SP1PublicIO 0)).circuitOperations.interactions at raw
  rw [state_sites] at raw
  simp only [
    sp1StateVerifierMain,circuit_norm,List.mem_cons,List.not_mem_nil,or_false] at raw
  rcases raw with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst a
  all_goals first | exact ⟨rfl,rfl⟩ | exact False.elim ((Ne.symm byteChannel_toRaw_ne_stateChannel) onByte)

/-- The host, final-memory, source and observation boundaries preserve every original public
Byte lookup. Ordered register/RAM endpoints emit only on their own channels. -/
theorem supervisor_values (image : ProgramImage) (source target : ExecutionSnapshot)
    (finish : HostHintQueue.State F) (env : Environment F) :
    (base image source target finish).verifierOperations.interactionValuesWith byteChannel.toRaw env =
      (sp1StateVerifierProgram (p := SP1Prime)).circuitOperations.interactionValuesWith byteChannel.toRaw env := by
  rw [base,HostObserved.verifier_byte_values]
  have registered : byteChannel.toRaw ∈ HostLocalCore.registry (p := SP1Prime) image source
      (HintReadWordChip.stateChannel.toRaw :: HostFinalMemory.sourceChannels target.sail.memorySnapshot) := by
    simp [HostLocalCore.registry,LocalCore.baseEnsemble,sp1Ensemble_channels]
  have absent : byteChannel.toRaw ∉ (HostHintQueueBoundary.boundary source finish target.host).circuit.channels := by
    intro member
    apply (show "SP1Byte" ∉ ((HostHintQueueBoundary.boundaryChannels (p := SP1Prime)).map RawChannel.name) by decide)
    exact List.mem_map_of_mem (HostHintQueueBoundary.boundary_channels_subset source finish target.host member)
  rw [HostFinalMemory.verifier_core_values registered absent (by
    intro eq; exact Bool.noConfusion (congrArg (fun c => c.name == "SP1Byte") eq))]
  simp [LocalCore.boundaryVerifier,sp1StateVerifierProgram,OrderedBoundaryVerifier.verifierProgram,
    Verifier.Program.circuitOperations,Verifier.Program.operations,Verifier.ofInteractions,sp1StateVerifierMain,
    OrderedBoundaryVerifier.main,Operations.interactionValuesWith,Operations.interactionsWith,
    OrderedBoundary.channel,SnapshotMemoryEnsemble.channelName,OrderedFinalProvider.channelName,
    stateChannel,byteChannel,exitChannel,circuit_norm]

/-- Each real Byte read of the original supervisor is a unit demand whose complete payload
is admitted by the released providers at the authenticated public header. -/
theorem supervisor_readers (image : ProgramImage) (source target : ExecutionSnapshot)
    (finish : HostHintQueue.State F) (data : ProverData F) (limbs : (data.getPublicInput SP1PublicIO).LimbBounds)
    (i : Interaction F) (member : i ∈ (base image source target finish).verifierOperations.interactionValuesWith
      byteChannel.toRaw data.publicEnvironment) :
    i.direction = .pull ∧ i.mult = 1 ∧ ByteServable (messageKey i.msg) := by
  rw [supervisor_values] at member
  obtain ⟨pull,unit⟩ := state_reader _ _ member
  obtain ⟨a,seen,rfl⟩ := List.mem_map.mp member
  refine ⟨pull,unit,unit_guarantee_servable (Operations.channel_eq_of_mem_interactionsWith seen) pull unit data ?_⟩
  exact AbstractInteraction.eval_guarantees.mpr (state_guarantees data limbs a (List.mem_of_mem_filter seen))

end SP1Clean.Export.WritePublicByteDemand
