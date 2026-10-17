import SP1Clean.FormalModel.Contracts.HintQueue
import ToClean.Air.StaticProvider

/-! # Verifier-fixed initial hint nodes

The complete source queue determines the node fields. Only multiplicities are prover-owned;
unused nodes, padding and repeated physical occurrences remain in the authenticated inventory.
Later allocations require their own providers.
-/

namespace SP1Clean.HostHintQueue

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Model.Core.HintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- Source identities already bound the complete node inventory and its power-of-two padding. -/
theorem source_height_lt_uint64 (hints : List Bytes) :
    (sourceTable (p := p) hints).height < UInt64.size := by
  have length : (sourceTable (p := p) hints).length < 2 ^ 48 := by
    simp only [sourceTable, StaticTable.ofRows]
    unfold sourceRows
    split_ifs with fits
    · simpa only [List.length_ofFn, ofList_size] using fits
    · norm_num
  have padded := (sourceTable (p := p) hints).height_lt_double
  norm_num [UInt64.size] at *
  omega

/-- The fixed prefix establishes canonical node contents; counts satisfy requests on the
existing node channel without a separate membership component. -/
def source (hints : List Bytes) : Component (ZMod p) :=
  (sourceTable hints).payloadComponent nodeChannel
    (fun record member _ => (sourceTable_sound hints record member).1)
    (source_height_lt_uint64 hints)

/-- Every active physical source emission binds to the immutable source store. -/
theorem source_authenticates (hints : List Bytes) (table : Table (ZMod p))
    (same : table.component = source hints) (consistent : table.DataConsistency)
    (constraints : table.Constraints) :
    table.Authenticates nodeChannel (fun record => record.Valid ∧ record.Binds (ofList hints).1) := by
  exact ((sourceTable hints).payload_authenticates nodeChannel
    (fun record member _ => (sourceTable_sound hints record member).1)
    (source_height_lt_uint64 hints) table same consistent constraints).mono
      (sourceTable_sound hints)

end SP1Clean.HostHintQueue
