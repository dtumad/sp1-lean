import SP1Clean.Math.Word
import SP1Clean.Model.SP1Field

/-! # Shared scaffolding for the circuit-as-trace-generator layer (`TraceGenTests/`).

These fixtures derive whole trace rows from each chip's own circuit and the event-to-input
helpers in `EventPopulate.lean`. Real-row satisfiability checks use them independently of export.
Released-SP1 conformance is tested in `rust/sp1-comparison/tests/instruction_export.rs`, using
actual `MachineAir::generate_trace` rows and Clean's built-in Rust witness machinery.

The chips are field-generic over `ZMod p`; the anchors run at SP1's **concrete field**
(KoalaBear), where SP1's prover actually runs, so this file discharges the chips' `Fact`
assumptions once at that prime. The generic generators stay axiom-clean. -/

namespace SP1Clean.TraceGenTests

open SP1Clean

/-! The prime and its `Fact` instances are shared with the production library through
`Model.SP1Field`. -/

/-- Cast a single ℕ (a canonical field value) into SP1's field. -/
def toField (n : ℕ) : ZMod SP1Prime := (n : ZMod SP1Prime)

end SP1Clean.TraceGenTests
