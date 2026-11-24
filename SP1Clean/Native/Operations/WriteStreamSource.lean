import SP1Clean.Semantics.Host.WriteStreamMetadata
import ToClean.Air.StaticProvider

/-! # Fixed source of WRITE bytes and supplied hook reply records

The provider takes the verifier's complete host endpoints. It exposes exactly their local
lengths, hook descriptors and return counts, including metadata for empty lists. Physical demand determines
only multiplicities; every active source row admits an independently derived endpoint lookup.
-/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat Semantics

variable {p : ℕ} [Fact p.Prime]

/-- Multiplicities are determined by the physical demands for real metadata. -/
def recordChannel : Channel (ZMod p) Record where
  name := "sp1.native.write_fixed_stream"
  Guarantees _ _ := True

/-- Verifier-fixed record inventory for this source and target host. -/
def streamTable (source target : HostState) : StaticTable (ZMod p) Record :=
  let streams := WriteStreams.fromEndpoints source target
  StaticTable.ofRows "sp1.native.write_fixed_streams" (if inventoryOK streams then metadataRows streams else [])

omit [Fact p.Prime] in
/-- The verifier-fixed inventory and its padding always fit Clean’s unsigned row index. -/
theorem streamTable_height_lt_uint64 (source target : HostState) : (streamTable (p := p) source target).height < UInt64.size := by
  let s := WriteStreams.fromEndpoints source target
  have rows : (streamTable (p := p) source target).length < 2 ^ 48 := by
    change (if inventoryOK s then metadataRows (p := p) s else []).length < 2^48
    split
    · exact (metadataRows_le_queries s).trans_lt ((inventoryOK_iff s).mp (by assumption)).1
    · change 0 < 2^48; decide
  have padding := (streamTable (p := p) source target).height_lt_double
  norm_num [UInt64.size] at *
  omega

/-- An original fixed-prefix Clean table indexed solely by the public endpoints. -/
def streamComponent (source target : HostState) : Component (ZMod p) :=
  (streamTable source target).payloadComponent recordChannel (by intros; trivial) (streamTable_height_lt_uint64 source target)

/-- Every active physical occurrence refers to the actual source reply or destination stream. -/
theorem stream_authenticates (source target : HostState) (table : Table (ZMod p))
    (component : table.component = streamComponent source target) (checked : table.Constraints) :
    table.Authenticates recordChannel (fun row => row.Binds (.fromEndpoints source target)) := by
  apply ((streamTable source target).payload_authenticates recordChannel (by intros; trivial)
    (streamTable_height_lt_uint64 source target) table component checked).mono
  intro row member
  let s := WriteStreams.fromEndpoints source target
  change row ∈ (if inventoryOK s then metadataRows s else []) at member
  split at member
  · rename_i valid
    obtain ⟨q,v,_,found,same⟩ := (metadataRows_iff ..).mp member
    exact ⟨q,v,q.enumerated found,found,Query.fits_of_inventory valid found,same⟩
  · cases member

omit [Fact p.Prime] in
theorem streamTable_length {source target : HostState} (checked : inventoryOK (.fromEndpoints source target) = true) :
    (streamTable (p := p) source target).length = 3 + ((WriteStreams.fromEndpoints source target).hooks.map fun r => 3 + r.hints.length).sum := by
  change (if inventoryOK _ then metadataRows (p := p) _ else []).length = _
  simp only [checked,ite_true,metadataRows_length]

omit [Fact p.Prime] in
theorem metadata_available {source target : HostState} {q : Query} {v : Nat} (isMeta : q.IsMetadata)
    (checked : inventoryOK (.fromEndpoints source target) = true) (found : q.lookup (.fromEndpoints source target) = some v) :
    (streamTable (p := p) source target).Spec (q.encode v) := by
  change q.encode v ∈ (if inventoryOK _ then metadataRows _ else [])
  simp only [checked,ite_true]
  exact (metadataRows_iff ..).mpr ⟨q,v,isMeta,found,rfl⟩

end SP1Clean.WriteEffects
