import Mathlib.Data.List.Range
import Mathlib.Data.List.Dedup

/-! # Native byte intervals at the Memory bus's cell granularity

A span names requested bytes using natural addresses. Its cell inventory is the minimal cover
by aligned eight-byte cells; an empty span has no cells. Unions retain one occurrence per cell,
so overlapping host buffers do not introduce simultaneous duplicate accesses. This is a native
semantic footprint, not the exact Rust executor's untraced physical read inventory.
-/

namespace SP1Clean.Model.Core

structure MemorySpan where
  address : ℕ
  length : ℕ
deriving DecidableEq, Repr

namespace MemorySpan

/-- Cell indices, whose corresponding byte addresses are eight times the index. -/
def cells (span : MemorySpan) : List ℕ :=
  if span.length = 0 then [] else
    List.range' (span.address / 8) ((span.address + span.length - 1) / 8 + 1 - span.address / 8)

theorem mem_cells (span : MemorySpan) (cell : ℕ) :
    cell ∈ span.cells ↔ 0 < span.length ∧ span.address / 8 ≤ cell ∧
      cell ≤ (span.address + span.length - 1) / 8 := by
  simp only [cells]
  split_ifs with empty
  · simp [empty]
  · simp only [List.mem_range'_1]
    omega

theorem nodup_cells (span : MemorySpan) : span.cells.Nodup := by
  unfold cells
  split_ifs
  · exact List.nodup_nil
  · exact List.nodup_range'

/-- Every requested byte belongs to an inventoried cell, including unaligned endpoint bytes. -/
theorem byte_cell_mem (span : MemorySpan) (offset : ℕ) (bound : offset < span.length) :
    (span.address + offset) / 8 ∈ span.cells := by
  rw [mem_cells]
  omega

/-- A cell outside the inventory has no byte in the requested interval. -/
theorem byte_outside (span : MemorySpan) (cell offset : ℕ) (bound : offset < 8)
    (outside : cell ∉ span.cells) :
    cell * 8 + offset < span.address ∨ span.address + span.length ≤ cell * 8 + offset := by
  rw [mem_cells] at outside
  omega

/-- Covers of bounded native guest spans stay entirely inside the aligned guest-memory window. -/
theorem cell_in_window (span : MemorySpan)
    (lower : 2 ^ 16 ≤ span.address) (upper : span.address + span.length ≤ 2 ^ 48)
    (cell : ℕ) (member : cell ∈ span.cells) :
    2 ^ 16 ≤ cell * 8 ∧ cell * 8 + 8 ≤ 2 ^ 48 := by
  rw [mem_cells] at member
  omega

/-- One inventory for all byte intervals, with overlapping cells shared. -/
def unionCells (spans : List MemorySpan) : List ℕ :=
  (spans.flatMap cells).dedup

theorem mem_unionCells (spans : List MemorySpan) (cell : ℕ) :
    cell ∈ unionCells spans ↔ ∃ span ∈ spans, cell ∈ span.cells := by
  simp [unionCells]

theorem nodup_unionCells (spans : List MemorySpan) : (unionCells spans).Nodup := by
  exact List.nodup_dedup _

end MemorySpan

end SP1Clean.Model.Core
