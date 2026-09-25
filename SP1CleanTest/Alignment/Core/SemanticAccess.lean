import SP1Clean.Proofs.Completeness.SemanticAccess
import SP1Clean.Model.Machine.ConfiguredState

/-! # Canonical memory access and refresh regressions

These finite projection fixtures exercise aliases and `x0` across a refresh boundary. They test
the extractor/scheduler, not a second execution relation; the existing active Sail/JAL anchor
separately consumes the universal compiler-totality theorem.
-/

namespace SP1CleanTest.Core.SemanticAccess
open SP1Clean SP1Clean.Semantics SP1Clean.Soundness.Target SP1Clean.TraceGen LeanRV64D.Defs

private def source : SailState :=
  { configuredState 65536 with
    regs := (configuredState 65536).regs.insert Register.x1 70000
    mem := (∅ : Std.ExtHashMap ℕ (BitVec 8)).insertMany
      [(70000, 7), (70001, 0), (70002, 0), (70003, 0),
        (70004, 0), (70005, 0), (70006, 0), (70007, 0)] }

private def compiled (decoded : instruction) (target : SailState) : Option CompiledInstructionEvent := do
  let key ← instructionRouteKey decoded
  let id ← instructionRouteId decoded
  compileInstructionEvent?
    ⟨65536, 0, decoded, key, id, instructionAccessPlan? decoded source target⟩
    AccessFrontier.initial (2 ^ 24 + 1)

private def summary (result : Option CompiledInstructionEvent) :
    Option (InstructionChipId × List ℕ × List (ℕ × ℕ) × List ℕ) := do
  let result ← result
  pure (result.routed.id, result.stamped.map StampedTouch.previous,
    result.memoryBumps.map (fun event => (event.addr, event.currTs)),
    result.plan.map (fun touch => touch.pushed.toNat))

/-- An aliased load refreshes its base only once; A cites B's fresh timestamp and posts the target value. -/
theorem loadAlias : summary (compiled (.LOAD (0, .Regidx 1, .Regidx 1, false, 8))
    { source with regs := source.regs.insert Register.x1 7 }) =
      some (.loadDouble, [0, 2 ^ 24 + 2, 2 ^ 24 + 4], [(1, 2 ^ 24 + 2)], [7, 70000, 7]) := by
  native_decide

/-- Aliased store operands share the same refresh and remain read-backs, while RAM posts the new word. -/
theorem storeAlias : summary (compiled (.STORE (0, .Regidx 1, .Regidx 1, 1))
    { source with mem := source.mem.insert 70000 112 }) =
      some (.storeByte, [0, 2 ^ 24 + 2, 2 ^ 24 + 4], [(1, 2 ^ 24 + 2)], [112, 70000, 70000]) := by
  native_decide

/-- LOAD-to-x0 retains the RAM read and immutable zero destination, with two distinct register refreshes. -/
theorem loadX0 : summary (compiled (.LOAD (0, .Regidx 1, .Regidx 0, false, 8)) source) =
    some (.loadX0, [0, 2 ^ 24 + 2, 2 ^ 24 + 2], [(1, 2 ^ 24 + 2), (0, 2 ^ 24 + 2)],
      [7, 70000, 0]) := by
  native_decide

/-- Missing any enclosing-cell byte rejects projection, even when the requested byte is present. -/
theorem missingCellByte : (instructionAccessPlan? (.LOAD (0, .Regidx 1, .Regidx 0, false, 1))
    { source with mem := source.mem.erase 70007 } source).isNone := by
  native_decide

end SP1CleanTest.Core.SemanticAccess
