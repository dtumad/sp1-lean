import SP1Clean.Proofs.Completeness.WriteCountedTables

/-! # Selecting physical WRITE sources for the exact released read requests

The selector reads only the registered predecessor occurrences. It preserves the complete
released read and order, checks the physical interval and computes its division columns.
-/

namespace SP1Clean.WriteProbe.Counted
open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- A candidate must certify the incoming clock and return the entire requested key and word. -/
def Covers (record : Readback (ZMod p)) (read : Read (ZMod p)) : Prop :=
  let input := populate (ReadbackSupply.populate record 0).version read.clock
  Spec input ∧ input.read = read

instance (record : Readback (ZMod p)) (read : Read (ZMod p)) : Decidable (Covers record read) := by
  unfold Covers Spec Address.Bounded ValidKey Word.isU64
  infer_instance

/-- Choose the first matching physical occurrence in actual registry order. -/
def route? (records : List (Readback (ZMod p))) (reads : List (Read (ZMod p))) :
    Option (List (Request records.length (ZMod p))) :=
  reads.mapM fun read => (records.findFinIdx? (fun r => Covers r read)).map (fun i => (i, read.clock))

omit [Fact (2 ^ 25 < p)] in
/-- Any successful route builds every native probe honestly and emits exactly the requested
sequence, including repeated reads of the same version. -/
theorem route?_spec (records : List (Readback (ZMod p))) (reads : List (Read (ZMod p)))
    {requests : List (Request records.length (ZMod p))} (routed : route? records reads = some requests) :
    (∀ input ∈ probes records requests, ProverAssumptions input) ∧
      (probes records requests).map Inputs.read = reads := by
  induction reads generalizing requests with
  | nil => cases routed; exact ⟨by simp [probes], rfl⟩
  | cons read rest ih =>
    simp only [route?, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff,
      Option.pure_def, Option.some.injEq] at routed
    obtain ⟨_, ⟨i, selected, rfl⟩, later, tail, rfl⟩ := routed
    have one := of_decide_eq_true (List.findFinIdx?_eq_some_iff.mp selected).1
    obtain ⟨spec, projects⟩ := one
    obtain ⟨valid, ordered⟩ := ih tail
    refine ⟨?_, ?_⟩
    · intro input member
      rcases List.mem_cons.mp member with rfl | after
      · exact ⟨spec, rfl⟩
      · exact valid _ after
    · exact congrArg₂ List.cons projects ordered

omit [Fact (2 ^ 25 < p)] in
/-- Supply coverage makes deterministic routing total. This is a local bridge for discharging
coverage from the installed history at each released header or packet-word read. -/
theorem route?_exists (records : List (Readback (ZMod p))) (reads : List (Read (ZMod p)))
    (covered : ∀ read ∈ reads, ∃ r ∈ records, Covers r read) :
    ∃ requests, route? records reads = some requests := by
  induction reads with
  | nil => exact ⟨[], rfl⟩
  | cons read rest ih =>
    obtain ⟨r, member, chosen⟩ := covered read List.mem_cons_self
    obtain ⟨tail, routed⟩ := ih (fun x hx => covered x (List.mem_cons_of_mem read hx))
    cases found : records.findFinIdx? (fun r => Covers r read) with
    | none => exact False.elim ((List.findFinIdx?_eq_none_iff.mp found r member) (decide_eq_true chosen))
    | some i =>
      exact ⟨(i, read.clock) :: tail, by unfold route? at routed ⊢; simp [List.mapM_cons, found, routed]⟩

/-- At a successful route the ordinary Clean table builders produce both registered tables,
their checked constraints, and both balanced private ledgers. The host sees exactly its
chronological reads. The two height bounds are for the actual padded tables. -/
theorem physical_tables (raw : AccessInventory.Source → Table (ZMod p))
    (registered : ∀ id, (raw id).component = AccessInventory.original id)
    (sourceChecked : ∀ id, (raw id).Constraints)
    (bounded : ∀ r ∈ live (AccessInventory.records raw), Bounded r)
    (reads : List (Read (ZMod p))) {requests : List (Request (live (AccessInventory.records raw)).length (ZMod p))}
    (routed : route? (live (AccessInventory.records raw)) reads = some requests)
    (data : ProverData (ZMod p)) (supplyFits probeFits) :
    let records := live (AccessInventory.records raw)
    let supply := table (allocated records requests) data supplyFits
    let inputs := probes records requests
    let observer := WriteProbe.table inputs data probeFits
    supply.Constraints ∧ supply.Guarantees ∧ observer.Constraints ∧ observer.Guarantees ∧
      LogUpBalanced (AccessInventory.ledger raw registered supply) ∧
      LogUpBalanced (supply.interactionsWith versionChannel.toRaw ++ observer.interactionsWith versionChannel.toRaw) ∧
      inputs.map Inputs.read = reads ∧ inputs.length = reads.length := by
  obtain ⟨valid, emitted⟩ := route?_spec _ _ routed
  obtain ⟨localSupply, guarantees, incoming⟩ := readback_balanced raw registered requests sourceChecked bounded data supplyFits
  obtain ⟨localReads, readGuarantees⟩ := WriteProbe.table_complete valid data probeFits
  exact ⟨localSupply, guarantees, localReads, readGuarantees, incoming, version_balanced _ requests data data _ _,
    emitted, by simpa only [List.length_map] using congrArg List.length emitted⟩

end SP1Clean.WriteProbe.Counted
