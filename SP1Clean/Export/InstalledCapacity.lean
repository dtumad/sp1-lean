import SP1Clean.Export.InstalledHintAssembly

/-! # Shared LogUp headroom in the installed assembly

Clean checks each registered channel using its verifier count and the sum of the physical
height times the syntactic width of each component. Adding rows therefore spends a common
remaining budget on each channel. These laws use the actual installed components and the
complete height vector in verifier order.
-/

namespace SP1Clean.Export.InstalledAssembly
open Circuit Air.Flat

/-- The full verifier height vector associated with the installed table inventory. -/
def physicalHeights (context : Context) (rows : Component Fp → ℕ) : List ℕ :=
  (assembly context).tables.map rows

/-- The width used by Clean's verifier for a registered channel name, including all repeated emissions. -/
def rowOccurrences (table : Component Fp) (channel : String) : ℕ :=
  table.operations.interactions.countP (·.channel.name == channel)

/-- Additional occurrences contributed by an arbitrary simultaneous change in physical heights. -/
def additionalOccurrences (context : Context) (extra : Component Fp → ℕ) (channel : String) : ℕ :=
  ((assembly context).tables.map fun table => extra table * rowOccurrences table channel).sum

/-- Updating all physical heights adds their occurrence counts once to the existing count map.
The base count includes the verifier even when every base table has height zero. -/
theorem interactionCount_add (context : Context) (base extra : Component Fp → ℕ) (channel : String) :
    (assembly context).interactionCount channel (physicalHeights context fun table => base table + extra table) =
      (assembly context).interactionCount channel (physicalHeights context base) + additionalOccurrences context extra channel := by
  simp only [Ensemble.interactionCount, physicalHeights, additionalOccurrences, rowOccurrences]
  generalize (assembly context).tables = tables
  induction tables with
  | nil => simp
  | cons table rest ih => simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, Nat.add_mul]; omega

/-- Clean's complete registered-channel check is equivalent to the per-channel residual
inequalities for the actual incremental rows. The base capacity test handles empty residuals. -/
theorem interactionsFit_add_iff (context : Context) (base extra : Component Fp → ℕ) :
    (assembly context).interactionsFit .logUp (physicalHeights context fun table => base table + extra table) ↔
      ∀ channel ∈ (assembly context).channels,
        let used := (assembly context).interactionCount channel.name (physicalHeights context base)
        used < SP1Prime ∧ additionalOccurrences context extra channel.name ≤ SP1Prime - 1 - used := by
  rw [Ensemble.interactionsFit, List.all_eq_true]
  simp only [Balance.logUp, decide_eq_true_eq, ComputableRingChar.char_eq, ZMod.ringChar_zmod_n, interactionCount_add]
  constructor <;> intro checks ch member <;> specialize checks ch member <;> omega

private theorem single_cost (tables : List (Component Fp)) (slot : Component Fp) (extra : ℕ) (channel : String)
    (unique : (tables.map (·.circuit.name)).Nodup) (installed : slot ∈ tables) :
    (tables.map fun table => (if table.circuit.name = slot.circuit.name then extra else 0) * rowOccurrences table channel).sum =
      extra * rowOccurrences slot channel := by
  induction tables with
  | nil => simp at installed
  | cons table rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp installed with rfl | later
    · have zero : ∀ t ∈ rest, t.circuit.name ≠ slot.circuit.name := fun t member same =>
        unique.1 (same ▸ List.mem_map_of_mem (f := fun c : Component Fp => c.circuit.name) member)
      have erased := List.map_congr_left (l := rest) (fun t member => show (if t.circuit.name = slot.circuit.name then extra else 0) *
        rowOccurrences t channel = 0 by simp [zero t member])
      simp only [List.map_cons, List.sum_cons, ↓reduceIte, erased]
      simp
    · have different : table.circuit.name ≠ slot.circuit.name := fun same =>
        unique.1 (same ▸ List.mem_map_of_mem (f := fun c : Component Fp => c.circuit.name) later)
      simp only [List.map_cons, List.sum_cons, ite_eq_right different, Nat.zero_mul, Nat.zero_add]
      exact ih unique.2 later

/-- Exact extra physical rows that one installed component can add while all other heights
stay fixed. Channels with zero width impose only the base count test. -/
theorem interactionsFit_grow_iff (context : Context) (base : Component Fp → ℕ) (slot : Component Fp)
    (installed : slot ∈ (assembly context).tables) (extra : ℕ) :
    (assembly context).interactionsFit .logUp (physicalHeights context fun table =>
      base table + if table.circuit.name = slot.circuit.name then extra else 0) ↔
      ∀ channel ∈ (assembly context).channels,
        let used := (assembly context).interactionCount channel.name (physicalHeights context base)
        let width := rowOccurrences slot channel.name
        used < SP1Prime ∧ (0 < width → extra ≤ (SP1Prime - 1 - used) / width) := by
  rw [interactionsFit_add_iff]
  simp only [additionalOccurrences, single_cost _ slot extra _ (assembly context).unique_names installed]
  constructor <;> intro checks channel member <;> obtain ⟨baseFit, cost⟩ := checks channel member <;> refine ⟨baseFit, ?_⟩
  · intro positive
    exact (Nat.le_div_iff_mul_le positive).mpr cost
  · by_cases positive : 0 < rowOccurrences slot channel.name
    · exact (Nat.le_div_iff_mul_le positive).mp (cost positive)
    · simp [Nat.eq_zero_of_not_pos positive]

end SP1Clean.Export.InstalledAssembly
