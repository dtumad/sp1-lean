module

public import SP1Clean.FormalModel.TraceGen.SailAlu
public import SP1Clean.Proofs.Completeness.Assembly

/-! # ALU execution events satisfy generated chip constraints

The shared ALU fold produces well-formed events, which Add/Sub completeness turns into valid
physical rows. Table construction takes its exact input-length capacity proof and explicit evaluation data. Transport to an ensemble's
canonical data is a separate step; this module does not establish channel balance or program
commitment agreement.

The execution bridge keeps its domain explicit: a supplied decoder, a preserved 48-bit PC bound
and nonzero destination routing. Register widths follow from Sail's types, and the generator
maintains the clock and timestamp invariants.
-/

@[expose] public section

namespace SP1Clean.Soundness

open SP1Clean.TraceGen
open Air.Flat (Table)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- **A generated ALU stream builds a satisfying `Add` table.** -/
theorem aluEvents_addTable_constraints (g : GenState) (clk : ℕ) (steps : List AluStep)
    (hb : g.Bounded (clk + Semantics.regCOffset)) (hclk : clk % Semantics.ordinaryClkInc = 1)
    (hs : ∀ s ∈ steps, s.WellFormed) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bounded : (AddChip.traceInputs (p := p) (aluEvents g clk steps) padding).length ≤ UInt64.size) :
    (Table.build (AddChip.component (p := p))
      (AddChip.traceInputs (aluEvents g clk steps) padding) data hint bounded).Constraints :=
  AddChip.traceTable_constraints _ _ _ _ (aluEvents_wellFormed steps g clk hb hclk hs) bounded

/-- The same table satisfies its channel guarantees, so the messages it pushes carry the payloads
the buses promise. -/
theorem aluEvents_addTable_guarantees (g : GenState) (clk : ℕ) (steps : List AluStep)
    (hb : g.Bounded (clk + Semantics.regCOffset)) (hclk : clk % Semantics.ordinaryClkInc = 1)
    (hs : ∀ s ∈ steps, s.WellFormed) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bounded : (AddChip.traceInputs (p := p) (aluEvents g clk steps) padding).length ≤ UInt64.size) :
    (Table.build (AddChip.component (p := p))
      (AddChip.traceInputs (aluEvents g clk steps) padding) data hint bounded).Guarantees :=
  AddChip.traceTable_guarantees _ _ _ _ (aluEvents_wellFormed steps g clk hb hclk hs) bounded

/-- **`Sub` too** — the R-type family shares the adapter, so the fold serves every chip in it
without a per-chip generator. Stated for a second chip precisely to make that visible. -/
theorem aluEvents_subTable_constraints (g : GenState) (clk : ℕ) (steps : List AluStep)
    (hb : g.Bounded (clk + Semantics.regCOffset)) (hclk : clk % Semantics.ordinaryClkInc = 1)
    (hs : ∀ s ∈ steps, s.WellFormed) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bounded : (SubChip.traceInputs (p := p) (aluEvents g clk steps) padding).length ≤ UInt64.size) :
    (Table.build (SubChip.component (p := p))
      (SubChip.traceInputs (aluEvents g clk steps) padding) data hint bounded).Constraints :=
  SubChip.traceTable_constraints _ _ _ _ (aluEvents_wellFormed steps g clk hb hclk hs) bounded


/-! ## From a Sail run to generated tables

The PC invariant is supplied by the caller; nonzero destination routing sends x0 writes to the
separate AluX0 chip. The decoder remains a parameter, so a restricted instantiation does not
silently become a claim about arbitrary instruction execution.
-/

/-- **Every ALU row a run generates satisfies the `Add` chip's constraint system.** -/
theorem sailRun_addTable_constraints
    {decode : SailState → Option AluDecoded} {P : SailState → Prop}
    (hpc : ∀ s, P s → ∀ v, s.regs.get? LeanRV64D.Defs.Register.PC = some v → v.toNat < 2 ^ 48)
    (hpres : ∀ s s', P s → Machine.stepOnce s = some s' → P s')
    (hrd : ∀ s d, decode s = some d → d.2.1 ≠ 0)
    (n : ℕ) (s : SailState) (hP : P s) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bounded : (AddChip.traceInputs (p := p)
      (aluEvents GenState.initial 1 (aluStepsFrom decode s n)) padding).length ≤ UInt64.size) :
    (Table.build (AddChip.component (p := p))
      (AddChip.traceInputs
        (aluEvents GenState.initial 1 (aluStepsFrom decode s n)) padding) data hint bounded).Constraints :=
  aluEvents_addTable_constraints _ _ _ initial_bounded_at_genesis (by norm_num)
    (aluStepsFrom_wellFormed hpc hpres hrd n s hP) padding data hint bounded

/-- The same run's `Sub` table. The R-type family shares one adapter, so one generator serves it. -/
theorem sailRun_subTable_constraints
    {decode : SailState → Option AluDecoded} {P : SailState → Prop}
    (hpc : ∀ s, P s → ∀ v, s.regs.get? LeanRV64D.Defs.Register.PC = some v → v.toNat < 2 ^ 48)
    (hpres : ∀ s s', P s → Machine.stepOnce s = some s' → P s')
    (hrd : ∀ s d, decode s = some d → d.2.1 ≠ 0)
    (n : ℕ) (s : SailState) (hP : P s) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bounded : (SubChip.traceInputs (p := p)
      (aluEvents GenState.initial 1 (aluStepsFrom decode s n)) padding).length ≤ UInt64.size) :
    (Table.build (SubChip.component (p := p))
      (SubChip.traceInputs
        (aluEvents GenState.initial 1 (aluStepsFrom decode s n)) padding) data hint bounded).Constraints :=
  aluEvents_subTable_constraints _ _ _ initial_bounded_at_genesis (by norm_num)
    (aluStepsFrom_wellFormed hpc hpres hrd n s hP) padding data hint bounded

/-- **The generated table is no taller than the run is long** — the shard-size fact. -/
theorem sailRun_rows_le (decode : SailState → Option AluDecoded) (n : ℕ) (s : SailState) :
    (aluStepsFrom decode s n).length ≤ n :=
  aluStepsFrom_length_le decode n s

end SP1Clean.Soundness
