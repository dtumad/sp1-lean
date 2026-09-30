import SP1Clean.Semantics.Specs.DivRem
import SP1Clean.Proofs.Operations.MulOperation.Formal
import SP1Clean.Native.Operations.DivRemOperation.OwnAsserts

/-! # DivRem product-cluster evidence

Contracts for the bundled `DivRemCore.circuit`: product placement, selection, ranges and the
intermediate raw assertion evidence used by the case proofs. Raw assertions are implementation
evidence; the independent public contract is `DivRemContract.RowSpec`.
-/

namespace SP1Clean.DivRemCore


/-- The DivRem row's own assertZero tail, **as evaluated field equations**: every entry of the
`DivRemChip.ownAsserts` chain (the `[E13…E367, adapter.op_a_0]` list, whose carrier-generic body is
here instantiated at `R = ZMod p`) is zero on the committed row.

This is the `DivRemCore` contract's one **deliberately-raw** component: it is exactly the content
the `assertZeros (ownAsserts cols)` block of the gadget's `main` contributes to `h_holds` (each
constraint expression evaluates to `0`), transported to the evaluated row by
`DivRemCore.ownAsserts_map_eval` (`Proofs/Operations/DivRemOperation/Core.lean`). Per the
semantic-not-structural principle the 121 equations are *not* restated semantically here — their
semantic form IS the chip-level evidence layer (`Proofs/Chips/DivRemChip/{Soundness,Cases}.lean`),
which extracts each needed equation by list membership. The selection facts a consumer most often
needs (`is_real`/flag binariness, the one-hot sum, `SelectionSpec`) are already derived out of this
bundle into `CoreSpec`'s explicit conjuncts. -/
def OwnAssertsHold {p : ℕ} (cols : DivRemChip.Columns (ZMod p)) : Prop :=
  ∀ x ∈ DivRemChip.ownAsserts cols, x = 0

/- **Overview of `ProductSpec` and its evidence cluster** (the `ProductSpec` definition follows
below, after its two `@[irreducible]` placement leaf contracts). The semantic evidence certified by
the DivRem row's **product/own-assert/byte-range assertion
cluster** (`Native/Operations/DivRemOperation/Core.lean`), `DivRemCompare.CompareSpec`'s structural
twin:

* the two composed `MulOperation` semantic `Spec`s at the committed instantiations — `lower`
  (`is_mul = is_real`) and `upper` (`is_real_not_word` gate, `is_mulh = is_div + is_rem`,
  `is_mulhu = is_divu + is_remu`) — exactly the `Assumptions → Spec` currency
  `Proofs/Chips/DivRemChip/Extract.lean`'s `mul_lo_spec`/`mul_hi_spec_*` consume;
* the product-glue limb links in the form `rwlo_product`/`rwhi_product_{unsigned,signed}` expect:
  `c_times_quotient[i] = product[2i] + product[2i+1]·256` against `lower`'s bytes 0–7
  on real rows, and against `upper`'s bytes 8–15 under the 64-bit gate
  `g64 = is_div + is_divu + is_rem + is_remu`;
* the raw `OwnAssertsHold` bundle (see its docstring);
* the derived selection facts: `is_real`/`is_real_not_word`/all eight variant flags binary, the
  ungated one-hot sum `E367`, and `DivRemContract.SelectionSpec` (a real row selects a case);
* mirroring `MulOperation.Spec`'s convention of carrying its own byte pulls' facts (its `RawSpec`
  ranges), the cluster's 32 u16 `Range` pulls as gated `.val < 2^16` facts — the 8 carry-chain
  composites (`E123…E151`) and the `abs_c`/`abs_remainder`/`quotient`/`remainder`/
  `c_times_quotient` limbs on `is_real`. The word-variant checks on
  `remainder[1]`/`quotient[1]` are emitted once by their `U16MSBOperation` subcircuits in
  `DivRemCompare`, exactly as in the Rust AIR. -/
/-- The real-row lower-product bytes reassembled into the four committed u16 limbs.

This leaf contract is irreducible on purpose. `circuit_proof_start` simplifies the surrounding
`ProductSpec`; if this implication is exposed there, Lean distributes its conjunction into the
parent proof state and destroys the small proof boundary. Consumers cross it explicitly with
`rw [LowerProductPlacement]`. -/
@[irreducible] def LowerProductPlacement {p : ℕ} (cols : DivRemChip.Columns (ZMod p)) : Prop :=
  cols.is_real = 1 →
    cols.c_times_quotient[0] =
      cols.c_times_quotient_lower.product[0] + cols.c_times_quotient_lower.product[1] * 256 ∧
    cols.c_times_quotient[1] =
      cols.c_times_quotient_lower.product[2] + cols.c_times_quotient_lower.product[3] * 256 ∧
    cols.c_times_quotient[2] =
      cols.c_times_quotient_lower.product[4] + cols.c_times_quotient_lower.product[5] * 256 ∧
    cols.c_times_quotient[3] =
      cols.c_times_quotient_lower.product[6] + cols.c_times_quotient_lower.product[7] * 256

/-- The 64-bit selector-gated upper-product bytes reassembled into the four high u16 limbs.

Like `LowerProductPlacement`, this stays opaque to generic circuit-proof setup and is opened only by
the product proof that owns the boundary. -/
@[irreducible] def UpperProductPlacement {p : ℕ} (cols : DivRemChip.Columns (ZMod p)) : Prop :=
  cols.is_div + cols.is_divu + cols.is_rem + cols.is_remu = 1 →
    cols.c_times_quotient[4] =
      cols.c_times_quotient_upper.product[8] + cols.c_times_quotient_upper.product[9] * 256 ∧
    cols.c_times_quotient[5] =
      cols.c_times_quotient_upper.product[10] + cols.c_times_quotient_upper.product[11] * 256 ∧
    cols.c_times_quotient[6] =
      cols.c_times_quotient_upper.product[12] + cols.c_times_quotient_upper.product[13] * 256 ∧
    cols.c_times_quotient[7] =
      cols.c_times_quotient_upper.product[14] + cols.c_times_quotient_upper.product[15] * 256

/-- The two Mul contracts and their folded product-to-u16-limb placement contracts. This named
semantic cluster is kept folded at chip boundaries so proofs need not unfold the unrelated
selection and range evidence merely to reason about a generated Mul witness block. -/
def ProductSpec {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]
    (cols : DivRemChip.Columns (ZMod p)) : Prop :=
  let lo := cols.c_times_quotient_lower
  let up := cols.c_times_quotient_upper
  MulOperation.Spec
    ⟨cols.quotient_comp, cols.c, lo, cols.is_real, cols.is_real, 0, 0, 0, 0⟩ ∧
  MulOperation.Spec
    ⟨cols.quotient_comp, cols.c, up, cols.is_real_not_word, 0,
     cols.is_div + cols.is_rem, cols.is_divu + cols.is_remu, 0, 0⟩ ∧
  LowerProductPlacement cols ∧
  UpperProductPlacement cols

/-- Binary gates, the ungated one-hot equation, and the resulting unique committed instruction
selection. -/
def SelectionEvidenceSpec {p : ℕ} (cols : DivRemChip.Columns (ZMod p)) : Prop :=
  (cols.is_real = 0 ∨ cols.is_real = 1) ∧
  (cols.is_real_not_word = 0 ∨ cols.is_real_not_word = 1) ∧
  (cols.is_div = 0 ∨ cols.is_div = 1) ∧ (cols.is_divu = 0 ∨ cols.is_divu = 1) ∧
  (cols.is_rem = 0 ∨ cols.is_rem = 1) ∧ (cols.is_remu = 0 ∨ cols.is_remu = 1) ∧
  (cols.is_divw = 0 ∨ cols.is_divw = 1) ∧ (cols.is_remw = 0 ∨ cols.is_remw = 1) ∧
  (cols.is_divuw = 0 ∨ cols.is_divuw = 1) ∧ (cols.is_remuw = 0 ∨ cols.is_remuw = 1) ∧
  (cols.is_divu + cols.is_remu + cols.is_div + cols.is_rem
    + cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw = 1) ∧
  DivRemContract.SelectionSpec cols.is_real cols

/-- The core's 32 byte-table range facts exposed semantically as `< 2^16` bounds. -/
def RangeSpec {p : ℕ} (cols : DivRemChip.Columns (ZMod p)) : Prop :=
  let rn := cols.rem_neg * 65535
  cols.is_real = 1 →
    (cols.c_times_quotient[0] + cols.remainder_comp[0]
      - cols.carry[0] * 65536).val < 2 ^ 16 ∧
    (cols.c_times_quotient[1] + cols.remainder_comp[1]
      - cols.carry[1] * 65536 + cols.carry[0]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[2] + cols.remainder_comp[2]
      - cols.carry[2] * 65536 + cols.carry[1]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[3] + cols.remainder_comp[3]
      - cols.carry[3] * 65536 + cols.carry[2]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[4] + rn - cols.carry[4] * 65536 + cols.carry[3]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[5] + rn - cols.carry[5] * 65536 + cols.carry[4]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[6] + rn - cols.carry[6] * 65536 + cols.carry[5]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[7] + rn - cols.carry[7] * 65536 + cols.carry[6]).val < 2 ^ 16 ∧
    (∀ i (_ : i < 4), cols.abs_c[i].val < 2 ^ 16) ∧
    (∀ i (_ : i < 4), cols.abs_remainder[i].val < 2 ^ 16) ∧
    (∀ i (_ : i < 4), cols.quotient[i].val < 2 ^ 16) ∧
    (∀ i (_ : i < 4), cols.remainder[i].val < 2 ^ 16) ∧
    (∀ i (_ : i < 8), cols.c_times_quotient[i].val < 2 ^ 16)

/-- The arithmetic core's auditable contract, split into four independently folded clusters:
products/glue, the exact raw Rust assertion tail, selection, and byte ranges. -/
def CoreSpec {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)] (cols : DivRemChip.Columns (ZMod p)) : Prop :=
  ProductSpec cols ∧ OwnAssertsHold cols ∧ SelectionEvidenceSpec cols ∧ RangeSpec cols

end SP1Clean.DivRemCore
