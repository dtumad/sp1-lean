import SP1Clean.Soundness.FinalMemoryCheckLedger

/-! # Complete outgoing Memory comparison from raw boundary acceptance

The installed witness supplies all facts: Byte closure authenticates target reads and finalizer
addresses, complete-record receipt balance matches every final row, and the verifier's change
ledger covers the complete complement. The result is the existing finite `checkFinal` relation.
Connecting this boundary subsystem to mixed execution grounding remains an assembly transport,
not a new semantics or an additional caller certificate.
-/

namespace SP1Clean.Soundness.FinalMemoryChecks

open Circuit Air.Flat Channels Model.Core Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
  {source target : MemorySnapshot} {auxiliary : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}

private theorem register_key (record : MemoryMsg (ZMod p)) (valid : FinalRegisterValue.Spec target record) :
    FinalMemoryChange.key false record = FinalMemoryChange.encode (MemoryMsg.locOf record) := by
  have location : MemoryMsg.locOf record = .reg (BitVec.ofNat 5 record.addr0.val) := by
    simp only [MemoryMsg.locOf, valid.1, valid.2.1, valid.2.2.1, and_self, ↓reduceIte]
  apply FinalMemoryChange.key_eq_encode false record ?_ (by rw [location])
  constructor
  · apply Word.isU64_of_cases <;>
      simp only [MemoryBoundary.address, valid.2.1, valid.2.2.1, circuit_norm, ZMod.val_zero] <;>
      have := valid.1 <;> omega
  · simp only [MemoryBoundary.address, Word.toNat, location, MemLoc.busAddress,
      valid.2.1, valid.2.2.1, circuit_norm, ZMod.val_zero, zero_mul, add_zero,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt valid.1]

private theorem ram_key (record : MemoryMsg (ZMod p)) (valid : MemoryBoundary.RamFinalSpec record) :
    FinalMemoryChange.key true record = FinalMemoryChange.encode (MemoryMsg.locOf record) := by
  apply FinalMemoryChange.key_eq_encode true record valid.1.2
  have lower : 32 ≤ (MemoryMsg.locOf record).busAddress := le_trans (by decide) valid.2
  cases location : MemoryMsg.locOf record with
  | reg index =>
      rw [location] at lower
      have := index.isLt
      change 32 ≤ index.toNat at lower
      omega
  | ram cell => rfl

/-- RAM-domain provenance is inherited from the matched physical finalizer, not assumed by
the target checker or supplied independently of the receipt ledger. -/
theorem ramInputs_finalSpec (witness : EnsembleWitness (ensemble source target auxiliary channels))
    (interface : Interface auxiliary) (checked : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∀ input ∈ ramInputs witness, MemoryBoundary.RamFinalSpec input.value.record := by
  have bytes : (FinalMemoryReceipts.ramTable (receiptWitness witness)).ChannelGuarantees byteChannel.toRaw := by
    rw [ramFinalTable_eq]
    exact ramFinalSlot.table_channelGuarantees witness byteChannel.toRaw
      (byte_guarantees witness interface checked balanced)
  have finalized := FinalMemoryReceipts.ram_records_spec (receiptWitness witness)
    (receiptWitness_constraints witness checked) bytes
  intro input present
  exact finalized _ ((ram_receipts_perm witness interface balanced).mem_iff.mp
    (List.mem_map_of_mem (f := fun input : FinalRamCheck.Inputs (ZMod p) => input.value.record) present))

/-- Raw constraints and complete channel balance imply complete target Memory validation.
There is no witness-supplied inventory, readiness predicate, or endpoint-comparison premise. -/
theorem checkFinal (witness : EnsembleWitness (ensemble source target auxiliary channels))
    (interface : Interface auxiliary) (checked : witness.Constraints) (balanced : witness.BalancedChannels) :
    source.checkFinal target
      ((records witness).map fun record => (MemoryMsg.locOf record, Word.toBitVec64 record.value)) = true := by
  apply FinalMemoryChangeCoverage.checkFinal_of_balanced source target (records witness) (validationRows witness)
    (receipts_perm witness interface balanced) ?_ ?_ ?_ (changes_balanced witness interface balanced)
  · intro row member
    rcases List.mem_append.mp member with register | ram
    · obtain ⟨input, present, rfl⟩ := List.mem_map.mp register
      exact (registerInputs_spec witness interface checked balanced input present).1.2.2.2.2.symm
    · obtain ⟨input, present, rfl⟩ := List.mem_map.mp ram
      exact ((ramInputs_spec witness interface checked balanced input present).1.final_snapshot target _
        (ramInputs_finalSpec witness interface checked balanced input present)).symm
  · intro row member
    rcases List.mem_append.mp member with register | ram
    · obtain ⟨input, present, rfl⟩ := List.mem_map.mp register
      exact (registerInputs_spec witness interface checked balanced input present).2
    · obtain ⟨input, present, rfl⟩ := List.mem_map.mp ram
      exact (ramInputs_spec witness interface checked balanced input present).2
  · intro row member
    rcases List.mem_append.mp member with register | ram
    · obtain ⟨input, present, rfl⟩ := List.mem_map.mp register
      exact register_key _ (registerInputs_spec witness interface checked balanced input present).1
    · obtain ⟨input, present, rfl⟩ := List.mem_map.mp ram
      exact ram_key _ (ramInputs_finalSpec witness interface checked balanced input present)

end SP1Clean.Soundness.FinalMemoryChecks
