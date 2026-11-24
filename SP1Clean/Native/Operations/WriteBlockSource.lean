import SP1Clean.Semantics.Host.WriteStreamBlocks
import ToClean.Air.StaticProvider

/-! # Verifier-fixed word-sized WRITE data source

The table has one physical preallocation per occupied eight-byte region. Its rows identify the
stream, reply, hint, block position and valid extent. Copies and repeated demand use the standard
Clean multiplicity column; the contents always come from the two public host endpoints.
-/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat Semantics

variable {p : Nat} [Fact p.Prime]

/-- Authenticates an aligned block and its number of occupied byte lanes. -/
def blockChannel : Channel (ZMod p) StreamBlock where
  name := "sp1.native.write_stream_blocks"
  Guarantees _ _ := True

/-- Verifier-fixed aligned blocks of the public endpoint stream data. -/
def blockTable (s : WriteStreams) : StaticTable (ZMod p) StreamBlock :=
  StaticTable.ofRows "sp1.native.write_stream_blocks" (if inventoryOK s then dataBlocks s else [])

omit [Fact p.Prime] in
private theorem block_height (s : WriteStreams) : (blockTable (p := p) s).height < UInt64.size := by
  have rows : (blockTable (p := p) s).length < 2^48 := by
    change (if inventoryOK s then dataBlocks (p := p) s else []).length < 2^48
    split
    · exact (dataBlocks_length s).trans_lt ((inventoryOK_iff s).mp (by assumption)).1
    · change 0 < 2^48; decide
  have pad := (blockTable (p := p) s).height_lt_double
  norm_num [UInt64.size] at *
  omega

/-- Preallocated provider for aligned output, request and returned-hint blocks. -/
def blockComponent (source target : HostState) : Component (ZMod p) :=
  let s := WriteStreams.fromEndpoints source target
  (blockTable s).payloadComponent blockChannel (by intros; trivial) (block_height s)

/-- All positive fixed block traffic at once. The clean provider may repeat a genuine block
with its scheduled multiplicity. -/
theorem block_authenticates (source target : HostState) (table : Table (ZMod p))
    (installed : table.component = blockComponent source target) (checked : table.Constraints) :
    table.Authenticates blockChannel fun block =>
      let s := WriteStreams.fromEndpoints source target
      inventoryOK s = true ∧ ∃ key bytes index, key.contents s = some bytes ∧
        8 * index < bytes.length ∧ block = encodeBlock key bytes index := by
  let s := WriteStreams.fromEndpoints source target
  apply ((blockTable s).payload_authenticates blockChannel (by intros; trivial) (block_height s) table installed checked).mono
  intro block mem
  change block ∈ (if inventoryOK s then dataBlocks s else []) at mem
  split at mem
  · exact ⟨by assumption,(dataBlocks_iff ..).mp mem⟩
  · cases mem

omit [Fact p.Prime] in
theorem block_available {s : WriteStreams} (checked : inventoryOK s = true) {key : StreamKey} {bytes : Bytes}
    (owner : key.contents s = some bytes) {index : Nat} (used : 8 * index < bytes.length) :
    (blockTable (p := p) s).Spec (encodeBlock key bytes index) := by
  change encodeBlock (p := p) key bytes index ∈ (if inventoryOK s then dataBlocks s else [])
  simp only [checked, ite_true]
  exact (dataBlocks_iff ..).mpr ⟨key,bytes,index,owner,used,rfl⟩

end SP1Clean.WriteEffects
