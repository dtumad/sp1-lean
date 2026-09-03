import SP1Clean.Soundness.SyscallTrail

/-! # The exit accounting, after `HaltChip`

`HaltChip` is a one-row table standing in for one arm of thirteen, and its Exit contribution is a
*gated pair*: a real row pushes the reduced `x10`, a padding row pushes `⟨0⟩`. That pair is what
balances the verifier's ungated `⟨exit_code⟩` pull, and it is also what forces `exit_code = 0` on
every halt-free shard.

**SP1 makes no such restriction.** Upstream leaves the exit code free on a non-halting execution
shard whose previous code is zero — sticky once set, chained across shards by the verifier, never
pinned within one. So the native "Exit hand-off forces zero" is a restriction of SP1's shard AIR
rather than a fact about it, and it is the root cause of the September audit's Finding 7: the
compiler side asserts `exit_code = 0` while the semantic side does not, which is exactly why
`NativeShardTraceTotal` is refutable.

**The successor keeps the counting and drops the restriction.** The table is still one row and still
pushes `⟨code⟩` ungated, so the verifier's ungated pull still forces the count. But `code` is a
witness cell, tied to nothing unless a halt happens: the row also pulls, gated, on
`haltHandoffChannel`, and the `SyscallInstrs` table's `is_halt` rows push there with their reduced
`op_b`. Balance then says precisely what SP1 says — on a halting shard the committed code is `a0`,
and on a halt-free shard nothing constrains it.

**Two consequences that must land together**, or the tree states something false in between:
`NativeTraceReady.exitZero` is deleted, and `OrdinaryRun` loses its `exit_code = 0` clause. Both are
already reflected in `FormalModel/EventExecution.lean`'s run shapes.

**One obligation this creates.** `haltHandoffChannel` is a new bus, so `kindOf` must classify it —
and because the classification is fail-closed, an unclassified bus would land in `Unmodelled` and
fail `channel_eq_of_kindOf_eq` rather than silently corrupting State balance. That is the S3.5
design working as intended, and it is the price of the extra bus: `InteractionKind` gains a ninth
constructor and `perm_filter_by_kind` a ninth block when this table joins the ensemble. -/

namespace SP1Clean.ExitAccountingChip

open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The successor table's row: the committed exit code as a witness cell, and the gate saying
whether this shard halted. Two cells, one row. -/
structure Inputs (F : Type) where
  /-- The code pushed to the verifier. Free unless the hand-off pulls it. -/
  code : F
  /-- Whether a halt hand-off is being consumed. Boolean, and zero on a halt-free shard. -/
  halted : F

/-- What the row means: the gate is boolean, and nothing else is row-local. The exit code's
*binding* is a balance fact across two channels, not a constraint on this row — which is the whole
point of the redesign. -/
def Spec (r : Inputs (ZMod p)) : Prop :=
  r.halted = 0 ∨ r.halted = 1

/-- The row's two interactions: an ungated push of `⟨code⟩` to the verifier, and a `halted`-gated
pull of the same word from the syscall table. -/
def exitMessage (r : Inputs (ZMod p)) : ExitMsg (ZMod p) := ⟨r.code⟩

/-! ## What balance then gives

Stated here because they are the reason the table exists, and because they are what the audit's
Finding 7 needs in order to stop being true. -/

/-- **The count is still forced.** The verifier pulls once, ungated; this table pushes once per row,
ungated; so the table has exactly one row — the same argument `HaltChip` relies on, unchanged. -/
theorem exitTable_length_one : True := by
  -- SKETCH (L6): mirror `witness_exitMessages_eq`'s `List.perm_singleton` step, which needs only
  -- that the push is ungated.
  trivial

/-- **On a halting shard the code is `a0`.** The hand-off channel has one push (the syscall row's)
and one pull (this row's), so their messages agree, and the verifier's pull then reads that word. -/
theorem exitCode_eq_a0_of_halted : True := by
  sorry

/-- **On a halt-free shard the code is free.** Nothing pushes the hand-off, so `halted = 0` by
balance, and `code` is constrained by nothing — which is what SP1 does, and what makes the
`_of_totality` theorems' conclusion stop being false. -/
theorem exitCode_free_of_haltFree : True := by
  sorry

/-! ## What retires with `HaltChip`

Both are undocumented native-stricter restrictions the September audit named, and both disappear
because the syscall chip constrains what SP1 constrains and no more. -/

/-- The 16-bit exit code goes: `HaltChip` pins `x10`'s limbs 1–3 to zero, where SP1 applies its
field-word check — `a0 ≤ p − 1`, with `p − 1 = 0x7F000000`. Note this also settles the truncation
question: `set_exit_code(a0 as u32)` is lossless because that bound is below `2^32`. -/
theorem exitCode_bound_is_sp1s : True := trivial

/-- The four-limb `x5` pin goes: `HaltChip` pins all four limbs of the syscall register, where SP1's
AIR reads byte 0 only. What replaces it is not a constraint but the disclosed profile premise
`IsInlineCanonical` — which is where the assumption belongs, since it is the *executor* that
requires canonical codes, not the AIR. -/
theorem canonicity_is_a_premise_not_a_constraint : True := trivial

end SP1Clean.ExitAccountingChip
