import SP1Clean.Proofs.Chips.WriteProbeFinal
import SP1Clean.Proofs.Chips.WriteProbeRefresh
import SP1Clean.Soundness.WriteReadbackSupply
import SP1Clean.Soundness.FinalMemoryReceipts

/-! # Authenticating the genuine physical WRITE sources

The same structural receipts used by the counted supplier originate in the registered
MemoryBump row or the original register/RAM ordered finalizers. The latter publish the
very records consumed by the legacy Memory bus, also when the key finishes at genesis.
-/

namespace SP1Clean.WriteProbe

open Circuit Air.Flat Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem actual_sources (table : Table (ZMod p)) (rows : List (ZMod p × Readback (ZMod p)))
    (ledger : table.interactionsWith readbackChannel.toRaw = rows.map fun r => readbackChannel.pushedIfValue r.1 r.2) :
    table.Authenticates readbackChannel (fun record => ∃ gate, (gate, record) ∈ rows ∧ gate ≠ 0) := by
  intro row member interaction emitted push
  have seen : interaction ∈ table.interactionsWith readbackChannel.toRaw := List.mem_flatMap.mpr ⟨row, member, emitted⟩
  rw [ledger] at seen
  obtain ⟨⟨gate, record⟩, inside, rfl⟩ := List.mem_map.mp seen
  exact ⟨record, rfl, gate, inside, push.1⟩

omit [Fact (2 ^ 17 < p)] in
private theorem actual_rows (table : Table (ZMod p)) (physical : List (Array (ZMod p)))
    (gate : Array (ZMod p) → ZMod p) (payload : Array (ZMod p) → Readback (ZMod p))
    (ledger : table.interactionsWith readbackChannel.toRaw =
      physical.map fun row => readbackChannel.pushedIfValue (gate row) (payload row)) :
    table.Authenticates readbackChannel (fun record => ∃ row ∈ physical, gate row ≠ 0 ∧ payload row = record) := by
  let rows := physical.map fun row => (gate row, payload row)
  apply (actual_sources table rows ?_).mono
  · intro record h
    obtain ⟨weight, mem, on⟩ := h
    obtain ⟨row, inside, pair⟩ := List.mem_map.mp mem
    exact ⟨row, inside, fun zero => on ((congrArg Prod.fst pair).symm.trans zero), congrArg Prod.snd pair⟩
  · simpa only [rows, List.map_map, Function.comp_def] using ledger

/-- A positive refresh receipt refers to an actual physical row and its exact unchanged-word packet. -/
def FromRefresh (table : Table (ZMod p)) (record : Readback (ZMod p)) : Prop :=
  ∃ row ∈ table.table, let r := valueFromOffset MemoryBumpChip.Inputs 0 (table.environment row)
                       r.is_real ≠ 0 ∧ refreshReadback r = record

/-- A positive finalizer receipt refers to an actual finalized key, timestamp and output word. -/
def FromFinal (ram : Bool) (table : Table (ZMod p)) (record : Readback (ZMod p)) : Prop :=
  ∃ row ∈ table.table, let env := table.environment row
                       (valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env).2 ≠ 0 ∧
                         finalReadback (finalRecordAt ram env) = record

/-- Exact provenance for every MemoryBump source contributing to the counted source ledger. -/
theorem refresh_authenticates (table : Table (ZMod p))
    (family : table.component = { circuit := MemoryBumpChip.circuit
                                  Assumptions := MemoryBumpChip.circuit.Assumptions
                                  generation := MemoryBumpChip.generation }) :
    (publishRefresh table family).Authenticates readbackChannel (FromRefresh table) :=
  actual_rows _ table.table (fun row => (valueFromOffset MemoryBumpChip.Inputs 0 (table.environment row)).is_real)
    (fun row => refreshReadback (valueFromOffset MemoryBumpChip.Inputs 0 (table.environment row)))
    (publishRefresh_receipts table family)

/-- Exact provenance for every closed suffix from a RAM or register finalizer. -/
theorem final_authenticates (ram : Bool) (table : Table (ZMod p)) (family : table.component = originalFinal ram) :
    (publishFinal ram table family).Authenticates readbackChannel (FromFinal ram table) :=
  actual_rows (publishFinal ram table family) table.table
    (fun row => (valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 (table.environment row)).2)
    (fun row => finalReadback (finalRecordAt ram (table.environment row)))
    (publishFinal_receipts ram table family)

/-- Raw row constraints and the balanced receipt channel authenticate the source of every
counted version in this four-table component group. The possible producers are exactly the
genuine refresh, register-final and RAM-final rows; no source-validity premise is needed. -/
theorem authenticates_physical_versions [Fact (2 ^ 24 < p)]
    (refresh registers ram supply : Table (ZMod p))
    (registered : refresh.component = { circuit := MemoryBumpChip.circuit
                                        Assumptions := MemoryBumpChip.circuit.Assumptions
                                        generation := MemoryBumpChip.generation })
    (rf : registers.component = originalFinal false) (mf : ram.component = originalFinal true)
    (sf : supply.component = ReadbackSupply.component) (checked : supply.Constraints)
    (balanced : BalancedInteractions ([supply, publishRefresh refresh registered, publishFinal false registers rf,
      publishFinal true ram mf].flatMap (·.interactionsWith readbackChannel.toRaw))) :
    supply.Authenticates versionChannel (fun version => ∃ record,
      (FromRefresh refresh record ∨ FromFinal false registers record ∨ FromFinal true ram record) ∧
      version.key = record.key ∧ version.value = record.value ∧
      Address.toNat version.lower = Semantics.clkNat record.previousHigh record.previousLow ∧
      Address.toNat version.upper = Semantics.clkNat record.currentHigh record.currentLow) := by
  refine ReadbackSupply.authenticates_versions _ supply sf checked _ ?_ balanced
  intro table member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (refresh_authenticates refresh registered).mono (fun _ => Or.inl)
  · exact (final_authenticates false registers rf).mono (fun _ h => Or.inr (Or.inl h))
  · exact (final_authenticates true ram mf).mono (fun _ h => Or.inr (Or.inr h))

/-- Both concrete finalizer circuits output the original row's full Memory record. -/
theorem finalRecordAt_eq (ram : Bool) (env : Environment (ZMod p)) :
    finalRecordAt ram env = Soundness.FinalMemoryEnsemble.rowRecord env := by
  cases ram
  · exact Soundness.FinalMemoryEnsemble.registerView_output env
  · exact Soundness.FinalMemoryEnsemble.ramView_output env

section Installed

open Soundness OrderedFinalProvider

variable {PublicIO : TypeMap} [ProvableType PublicIO]
variable {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
variable {names : (((FinalMemoryEnsemble.inventory (p := p)).views.map (·.component) ++ auxiliary).map (·.circuit.name)).Nodup}
variable {channelNames : (((OrderedBoundary.channel channelName).toRaw :: channels).map (·.name)).Nodup}
variable {registered : ∀ table ∈ (FinalMemoryEnsemble.inventory (p := p)).views.map (·.component) ++ auxiliary,
      table.circuit.channels ⊆ (OrderedBoundary.channel channelName).toRaw :: channels}
variable {registerReceipt : (FinalMemoryValue.channel false).toRaw ∈ channels}
variable {ramReceipt : (FinalMemoryValue.channel true).toRaw ∈ channels}

/-- Both wrappers apply directly at the existing register and RAM slots of a physical final inventory. -/
theorem installedFinal_slots (witness : EnsembleWitness (FinalMemoryReceipts.ensemble (PublicIO := PublicIO)
    auxiliary channels names channelNames registered registerReceipt ramReceipt)) :
    (FinalMemoryReceipts.registerTable witness).component = originalFinal false ∧
      (FinalMemoryReceipts.ramTable witness).component = originalFinal true :=
  ⟨FinalReceiptEnsemble.table_component (FinalMemoryReceipts.registerWitness witness),
    FinalReceiptEnsemble.table_component witness⟩

end Installed

end SP1Clean.WriteProbe
