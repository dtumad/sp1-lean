module

public import SP1Clean.FormalModel.Contracts.HintWords
public import ToClean.Air.StaticProvider

/-! # Verifier-fixed source words for immutable hints

All source words, including the mandatory final zero-padded word, are fixed by the source
queue. Counts are prover-owned. Physically oversized source inventories fail closed as a
whole; the native hint-count and byte-count ceilings preserve the entire admitted inventory.
Allocation providers and complete consumer coverage remain separate obligations.
-/

@[expose] public section

namespace SP1Clean.HostHintQueue

open Circuit Air.Flat Model.Core Model.Core.HintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Bound the inventory before materializing words; never retain a truncated source prefix. -/
def sourceWordInventory (hints : List Bytes) : StaticTable (ZMod p) WordRecord :=
  if hints.length + (hints.map List.length).sum < 2 ^ 48 then sourceWordTable hints
  else StaticTable.ofRows "sp1.native.hint_source_words" []

omit [Fact (2 ^ 17 < p)] in
/-- Existing semantic live-hint ceilings imply full source preservation. For the native SP1
field both ceilings are at most its characteristic minus one, far below this bound. -/
theorem sourceWordInventory_of_limits (hints : List Bytes) (limit : ℕ)
    (nodes : hints.length ≤ limit) (bytes : (hints.map List.length).sum ≤ limit)
    (bounded : limit < 2 ^ 47) :
    sourceWordInventory (p := p) hints = sourceWordTable hints := by
  have fits : hints.length + (hints.map List.length).sum < 2 ^ 48 := by
    norm_num at bounded ⊢
    omega
  simp only [sourceWordInventory, if_pos fits]

omit [Fact (2 ^ 17 < p)] in
/-- Every retained word has the original immutable source meaning. -/
theorem sourceWordInventory_spec (hints : List Bytes) (record : WordRecord (ZMod p))
    (member : (sourceWordInventory hints).Spec record) :
    (sourceWordTable hints).Spec record := by
  unfold sourceWordInventory at member
  split at member
  · exact member
  · simp [StaticTable.ofRows] at member

omit [Fact (2 ^ 17 < p)] in
/-- Actual hint count and byte length bound all words and power-of-two padding. -/
theorem sourceWord_height_lt_uint64 (hints : List Bytes) :
    (sourceWordInventory (p := p) hints).height < UInt64.size := by
  have length : (sourceWordInventory (p := p) hints).length < 2 ^ 48 := by
    unfold sourceWordInventory
    split
    · rename_i fits
      simpa only [sourceWordTable, StaticTable.ofRows] using
        (sourceWordRows_length_le (p := p) hints).trans_lt fits
    · simp [StaticTable.ofRows]
  have padded := (sourceWordInventory (p := p) hints).height_lt_double
  norm_num [UInt64.size] at *
  omega

/-- One fixed source table publishes complete word records at their requested multiplicities. -/
def sourceWord (hints : List Bytes) : Component (ZMod p) :=
  (sourceWordInventory hints).payloadComponent wordChannel
    (fun record member _ => (sourceWordTable_sound hints record
      (sourceWordInventory_spec hints record member)).1)
    (sourceWord_height_lt_uint64 hints)

/-- Physical source rows authenticate both field representation and exact immutable bytes. -/
theorem sourceWord_authenticates (hints : List Bytes) (table : Table (ZMod p))
    (same : table.component = sourceWord hints) (consistent : table.DataConsistency)
    (constraints : table.Constraints) :
    table.Authenticates wordChannel (fun record => record.Valid ∧ record.Binds (ofList hints).1) := by
  apply ((sourceWordInventory hints).payload_authenticates wordChannel
    (fun record member _ => (sourceWordTable_sound hints record
      (sourceWordInventory_spec hints record member)).1)
    (sourceWord_height_lt_uint64 hints) table same consistent constraints).mono
  intro record member
  exact sourceWordTable_sound hints record (sourceWordInventory_spec hints record member)

end SP1Clean.HostHintQueue
