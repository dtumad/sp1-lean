import SP1Clean.Proofs.Chips.HostRamReadChip.Formal
import SP1Clean.Proofs.Chips.HostRamAccessChip.Populate
import SP1Clean.Model.Core.MemorySpan

/-! # Constructing host RAM reads

The constructor preserves the prior word and computes every timestamp column. A WRITE span
uses its distinct physical cells directly; the supplying Memory history remains responsible
for the prior record at each cell.
-/

namespace SP1Clean.HostRamReadChip

open Circuit Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

def populate (prior : MemoryMsg (ZMod p)) (clkHigh clk0 clk1 : ZMod p) : Inputs (ZMod p) :=
  ⟨HostRamAccessChip.populate prior clkHigh clk0 clk1 prior.value⟩

theorem populate_assumptions (prior : MemoryMsg (ZMod p)) (clkHigh clk0 clk1 : ZMod p)
    (valid : HostRamAccessChip.Domain prior clkHigh clk0 clk1 prior.value) :
    ProverAssumptions (populate prior clkHigh clk0 clk1) :=
  ⟨HostRamAccessChip.populate_assumptions _ _ _ _ _ valid, rfl⟩

/-- Construct one read per physical cell of the requested WRITE buffer. -/
def populateSpan (span : MemorySpan) (prior : ℕ → MemoryMsg (ZMod p))
    (clkHigh clk0 clk1 : ZMod p) : List (Inputs (ZMod p)) :=
  span.cells.map fun cell => populate (prior cell) clkHigh clk0 clk1

/-- Bounded, strictly earlier records suffice; no timestamp witness is supplied. -/
theorem populateSpan_assumptions (span : MemorySpan) (prior : ℕ → MemoryMsg (ZMod p))
    (clkHigh clk0 clk1 : ZMod p)
    (valid : ∀ cell ∈ span.cells,
      HostRamAccessChip.Domain (prior cell) clkHigh clk0 clk1 (prior cell).value) :
    ∀ input ∈ populateSpan span prior clkHigh clk0 clk1, ProverAssumptions input := by
  intro input member
  simp only [populateSpan, List.mem_map] at member
  obtain ⟨cell, member, rfl⟩ := member
  exact populate_assumptions _ _ _ _ (valid cell member)

omit [Fact (2 ^ 25 < p)] in
/-- Correctly indexed history produces exactly the span's minimal physical address list. -/
theorem populateSpan_addresses (span : MemorySpan) (prior : ℕ → MemoryMsg (ZMod p))
    (clkHigh clk0 clk1 : ZMod p)
    (keys : ∀ cell ∈ span.cells, Word.toNat (MemoryBoundary.address (prior cell)) = cell * 8) :
    (populateSpan span prior clkHigh clk0 clk1).map
        (fun input => Word.toNat (MemoryBoundary.address input.ram.pushed)) =
      span.cells.map (· * 8) := by
  simp only [populateSpan, List.map_map, Function.comp_def]
  change (span.cells.map fun cell => Word.toNat (MemoryBoundary.address (prior cell))) = _
  exact List.map_congr_left keys

omit [Fact (2 ^ 25 < p)] in
/-- Correctly indexed history records never create duplicate physical read addresses. -/
theorem populateSpan_addresses_nodup (span : MemorySpan)
    (prior : ℕ → MemoryMsg (ZMod p)) (clkHigh clk0 clk1 : ZMod p)
    (keys : ∀ cell ∈ span.cells, Word.toNat (MemoryBoundary.address (prior cell)) = cell * 8) :
    ((populateSpan span prior clkHigh clk0 clk1).map
      (fun input => Word.toNat (MemoryBoundary.address input.ram.pushed))).Nodup := by
  rw [populateSpan_addresses _ _ _ _ _ keys]
  exact span.nodup_cells.map (fun _ _ equal => by omega)

end SP1Clean.HostRamReadChip
