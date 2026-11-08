import SP1Clean.Soundness.FinalMemoryReceipts
import SP1CleanTest.Core.StaticMembership
import SP1CleanTest.Core.ComponentExport
import SP1Clean.Native.Operations.FinalRegisterValue
import SP1Clean.Native.Operations.FinalRamValue
import SP1Clean.Model.SP1Field

/-! # Physical finalizer receipt installation

The fixture builds the original ordered finalizers and real target-check consumers, then
installs receipts on the same arrays and reads Clean's canonical interaction ledger. Only the
two receipt balances are claimed here; execution Memory balance and target-check Byte closure
belong to the enclosing machine.
-/

namespace SP1CleanTest.Alignment.Core.FinalMemoryReceipts

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness

private abbrev Fp := ZMod SP1Prime

private def target : MemorySnapshot := ⟨Vector.replicate 32 0, ⟨[]⟩⟩

private def record (address clock : ℕ) : Channels.MemoryMsg Fp :=
  let word := Target.bitVecToWord (p := SP1Prime) (BitVec.ofNat 64 address)
  ⟨0, clock, word[0], word[1], word[2], Target.bitVecToWord 0⟩

private def consumers : List (Component Fp) :=
  [SP1CleanTest.Core.ComponentExport.component (FinalRegisterValue.circuit target), SP1CleanTest.Core.ComponentExport.component (FinalRamValue.circuit target)]

private theorem names :
    (((FinalMemoryEnsemble.inventory (p := SP1Prime)).views.map (·.component) ++ consumers).map
      (·.circuit.name)).Nodup := by decide

private def channels : List (RawChannel Fp) :=
  [Channels.byteChannel.toRaw, Channels.memoryChannel.toRaw,
    (FinalRegisterValue.membership target).channel.toRaw,
    (InitialMemoryLookup.membership target.memory (2 ^ 48) "sp1.native.target_memory").channel.toRaw,
    (FinalMemoryValue.channel false).toRaw, (FinalMemoryValue.channel true).toRaw]

private theorem channelNames :
    (((OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw :: channels).map (·.name)).Nodup := by
  decide

private theorem registered :
    ∀ component ∈ (FinalMemoryEnsemble.inventory (p := SP1Prime)).views.map (·.component) ++ consumers,
      component.circuit.channels ⊆ (OrderedBoundary.channel OrderedFinalProvider.channelName).toRaw :: channels := by
  intro component member channel used
  rcases List.mem_append.mp member with finals | consumerMem
  · obtain ⟨view, viewMem, rfl⟩ := List.mem_map.mp finals
    change view ∈ [FinalMemoryEnsemble.viewFor .registers,
      FinalMemoryEnsemble.viewFor .ram, FinalMemoryEnsemble.viewFor .terminal] at viewMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at viewMem
    rcases viewMem with rfl | rfl | rfl <;>
      have support := FinalMemoryEnsemble.view_channels_subset _ used <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at support <;>
      rcases support with rfl | rfl | rfl <;> simp [channels]
  · simp only [consumers, List.mem_cons, List.not_mem_nil, or_false] at consumerMem
    rcases consumerMem with rfl | rfl
    · change channel ∈ (FinalRegisterValue.circuit target).channels at used
      rw [GeneralFormalCircuit.channels,
        show (FinalRegisterValue.circuit target).channelsWithGuarantees =
          (FinalRegisterValue.elaborated target).channelsWithGuarantees from rfl,
        show (FinalRegisterValue.circuit target).channelsWithRequirements =
          [(FinalMemoryValue.channel false).toRaw] from rfl] at used
      simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at used
      simp only [channels, List.mem_cons, List.not_mem_nil, or_false]
      tauto
    · change channel ∈ (FinalRamValue.circuit target).channels at used
      rw [GeneralFormalCircuit.channels,
        show (FinalRamValue.circuit target).channelsWithGuarantees =
          (FinalRamValue.elaborated target).channelsWithGuarantees from rfl,
        show (FinalRamValue.circuit target).channelsWithRequirements =
          [(FinalMemoryValue.channel true).toRaw] from rfl] at used
      simp only [circuit_norm, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at used
      simp only [channels, List.mem_cons, List.not_mem_nil, or_false]
      simp only [List.mem_flatten, List.mem_ofFn] at used
      rcases used with h | h | ⟨items, ⟨i, rfl⟩, h⟩ | h <;>
        (try simp only [List.mem_cons, List.not_mem_nil, or_false] at *) <;> tauto

private def original (registers ram : List (Channels.MemoryMsg Fp))
    (checkedRegisters checkedRam : List (Channels.MemoryMsg Fp))
    (bounded : registers.length ≤ UInt64.size ∧ ram.length ≤ UInt64.size ∧
      checkedRegisters.length ≤ UInt64.size ∧ checkedRam.length ≤ UInt64.size := by decide) :
    EnsembleWitness (FinalMemoryEnsemble.ensemble (PublicIO := unit) consumers channels names channelNames registered) :=
  EnsembleWitness.ofTables _
    [SP1CleanTest.StaticMembership.buildTable (FinalMemoryEnsemble.viewFor .registers).component
      (registers.map fun item => OrderedMemoryProvider.populate item 0
        (Word.toNat (MemoryBoundary.address item))) [] (.empty Fp) (ProverHint.empty Fp) (by exact (List.length_map _).le.trans bounded.1),
     SP1CleanTest.StaticMembership.buildTable (FinalMemoryEnsemble.viewFor .ram).component
      (ram.map fun item => OrderedMemoryProvider.populate item 2
        (Word.toNat (MemoryBoundary.address item))) [] (.empty Fp) (ProverHint.empty Fp) (by exact (List.length_map _).le.trans bounded.2.1),
     SP1CleanTest.StaticMembership.buildTable (FinalMemoryEnsemble.viewFor .terminal).component []
      [] (.empty Fp) (ProverHint.empty Fp) (by decide),
     SP1CleanTest.StaticMembership.buildTable (SP1CleanTest.Core.ComponentExport.component (FinalRegisterValue.circuit target)) checkedRegisters
      [] (.empty Fp) (ProverHint.empty Fp) bounded.2.2.1,
     SP1CleanTest.StaticMembership.buildTable (SP1CleanTest.Core.ComponentExport.component (FinalRamValue.circuit target))
      checkedRam [] (.empty Fp) (ProverHint.empty Fp) bounded.2.2.2]
    () (by rfl)

private def ledger {ens : Ensemble Fp unit} (witness : EnsembleWitness ens)
    (name : String) : List (Array Fp × Fp) :=
  (witness.interactions.filter fun interaction => interaction.channel.name == name).map
    fun interaction => (interaction.msg, interaction.signedMult)

private def balanced (interactions : List (Array Fp × Fp)) : Bool :=
  interactions.length < SP1Prime && interactions.all fun interaction =>
    ((interactions.filter fun other => other.1 == interaction.1).map Prod.snd).sum == 0

private def receipts (registers ram checkedRegisters checkedRam : List (Channels.MemoryMsg Fp))
    (bounded : registers.length ≤ UInt64.size ∧ ram.length ≤ UInt64.size ∧
      checkedRegisters.length ≤ UInt64.size ∧ checkedRam.length ≤ UInt64.size := by decide) : Bool :=
  let witness := Soundness.FinalMemoryReceipts.lift (registerReceipt := by simp [channels]) (ramReceipt := by simp [channels]) (original registers ram checkedRegisters checkedRam bounded)
  balanced (ledger witness "SP1FinalRegisterValue") && balanced (ledger witness "SP1FinalRamValue")

/-- Receipt insertion retains the original arrays, heights, and decoded Memory inventory. -/
theorem physicalRoundTrip :
    let before := original [record 31 273, record 1 9] [record 65536 281]
      [record 1 9, record 31 273] [record 65536 281]
    let after := Soundness.FinalMemoryReceipts.lift (registerReceipt := by simp [channels]) (ramReceipt := by simp [channels]) before
    (after.tables.map (·.table)) = before.tables.map (·.table) ∧
      after.heights = before.heights ∧
      (FinalMemoryEnsemble.records (Soundness.FinalMemoryReceipts.original after)).map toElements =
        [record 31 273, record 1 9, record 65536 281].map toElements ∧
      ledger after "SP1Byte" = ledger before "SP1Byte" ∧
      ledger after "SP1Memory" = ledger before "SP1Memory" := by
  native_decide

/-- Actual installed receipts reject missing, duplicated, wrong-clock and wrong-kind consumers;
physical row order and empty inventories remain immaterial. -/
theorem receiptMutation :
    [receipts [record 31 273, record 1 9] [record 65536 281]
        [record 1 9, record 31 273] [record 65536 281],
     receipts [record 1 9] [] [] [],
     receipts [record 1 9] [] [record 1 9, record 1 9] [],
     receipts [record 1 9] [] [record 1 10] [],
     receipts [record 1 9] [] [] [record 1 9],
     receipts [] [] [] []] = [true, false, false, false, false, true] := by
  native_decide

end SP1CleanTest.Alignment.Core.FinalMemoryReceipts
