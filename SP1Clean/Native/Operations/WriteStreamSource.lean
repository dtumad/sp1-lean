import SP1Clean.Semantics.Host.WriteStreamRecords
import ToClean.Air.StaticProvider

/-! # Fixed source of WRITE bytes and supplied hook reply records

The provider takes the verifier's complete host endpoints. It exposes exactly their local
output and consumed replies, including metadata for empty lists. Physical demand determines
only multiplicities; every active source row admits an independently derived endpoint lookup.
-/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat Semantics

variable {p : ℕ} [Fact p.Prime]

/-- Counts belong to the provider and may be zero when a record is unused. -/
def recordChannel : Channel (ZMod p) Record where
  name := "sp1.native.write_fixed_stream"
  Guarantees _ _ := True

def streamTable (source target : HostState) : StaticTable (ZMod p) Record :=
  StaticTable.ofRows "sp1.native.write_fixed_streams" (fixedRows (.fromEndpoints source target))

omit [Fact p.Prime] in
private theorem height_bound (source target : HostState) : (streamTable (p := p) source target).height < UInt64.size := by
  have rows : (streamTable (p := p) source target).length < 2 ^ 48 := fixedRows_length _
  have padding := (streamTable (p := p) source target).height_lt_double
  norm_num [UInt64.size] at *
  omega

/-- An original fixed-prefix Clean table indexed solely by the public endpoints. -/
def streamComponent (source target : HostState) : Component (ZMod p) :=
  (streamTable source target).payloadComponent recordChannel (by intros; trivial) (height_bound source target)

/-- Every active physical occurrence refers to the actual source reply or destination stream. -/
theorem stream_authenticates (source target : HostState) (table : Table (ZMod p))
    (component : table.component = streamComponent source target) (checked : table.Constraints) :
    table.Authenticates recordChannel (fun row => row.Binds (.fromEndpoints source target)) := by
  apply ((streamTable source target).payload_authenticates recordChannel (by intros; trivial)
    (height_bound source target) table component checked).mono
  exact fun row member => ((fixedRows_iff _ row).mp member).2

end SP1Clean.WriteEffects
