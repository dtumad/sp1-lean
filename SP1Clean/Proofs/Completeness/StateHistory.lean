module

public import SP1Clean.Proofs.Completeness.StateInventory
public import SP1Clean.Proofs.Completeness.ChipLedger

/-! # State inventory agreement with physical tables

`StateInventory` owns semantic refreshes, chronology and regrouping. This adapter states their
agreement with the actual instruction and StateBump rows and derives the complete State-ledger
hand-off. It does not add a second execution representation or assume channel balance.
-/

@[expose] public section

namespace SP1Clean.Soundness

open SP1Clean.LookupAccessList
open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance stateHistoryFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The sole remaining representation bridge for State completeness.

The first two fields identify the actual links decoded from the built instruction/StateBump tables
with the compiler's field-free projections.  The last two identify the verifier boundary row with
the compiler's semantic endpoints.  No balance or chain property is hidden here. -/
structure StateTraceAgreement (trace : SupportedCoreTraceWitness p)
    (events : List RoutedEvent) (initial final : StateRecord) : Prop where
  instruction : stateInstrLinks trace = physicalInstructionStateLinks (p := p) events
  bumps : stateBumpLinks trace = physicalStateBumpLinks (p := p) events
  initial : stateInitToken trace = initial.key (p := p)
  final : stateFinalToken trace = final.key (p := p)

/-- Agreement gives the explicit physical-to-chronological regrouping required by State balance. -/
theorem StateTraceAgreement.links_perm_chronological
    {trace : SupportedCoreTraceWitness p} {events : List RoutedEvent}
    {initial final : StateRecord} (agreement : StateTraceAgreement trace events initial final) :
    (stateInstrLinks trace ++ stateBumpLinks trace).Perm
      (chronologicalStateLinks (p := p) events) := by
  rw [agreement.instruction, agreement.bumps]
  exact physicalStateLinks_perm_chronological events

/-- Agreement plus field-free chronology closes the semantic State hand-off. -/
theorem StateTraceAgreement.isHandoffChain
    {trace : SupportedCoreTraceWitness p} {events : List RoutedEvent}
    {initial final : StateRecord} (agreement : StateTraceAgreement trace events initial final)
    (chronology : StateChronology initial events final) :
    IsHandoffChain (stateInitToken trace) (chronologicalStateLinks (p := p) events)
      (stateFinalToken trace) := by
  rw [agreement.initial, agreement.final]
  exact chronologicalStateLinks_isHandoffChain chronology

/-- The complete State-ledger hand-off theorem for a compiled chronological history.  Its
`hbinary`/`hbump` premises are the ordinary selector facts produced by table constraints; all
ordering content comes from the compiler agreement and field-free chronology above. -/
theorem StateTraceAgreement.ledger_perm_handoff
    {trace : SupportedCoreTraceWitness p} {events : List RoutedEvent}
    {initial final : StateRecord} (agreement : StateTraceAgreement trace events initial final)
    (hbinary : ∀ decoded ∈ decodedInstructionRows (p := p) trace.witness.tables,
      (decoded.toChipRow trace.witness.data).is_real = 0 ∨
        (decoded.toChipRow trace.witness.data).is_real = 1)
    (hbump : ∀ row ∈ (stateBumpTable trace.witness).table,
      (stateBumpRow trace.witness.data row).is_real = 0 ∨
        (stateBumpRow trace.witness.data row).is_real = 1)
    (hhalt : ∀ row ∈ (haltTable trace.witness).table,
      (haltRow trace.witness.data row).is_real = 0)
    (hsyscall : ∀ row ∈ (syscallInstrsTable trace.witness).table,
      (syscallInstrsRow trace.witness.data row).is_real = 0)
    (chronology : StateChronology initial events final) :
    (active trace.stateLedger).Perm
      (handoff (chainTokens (stateInitToken trace,
        chronologicalStateLinks (p := p) events, stateFinalToken trace))) :=
  stateLedger_perm_handoff_chronological trace hbinary hbump hhalt hsyscall _
    agreement.links_perm_chronological (agreement.isHandoffChain chronology)

end SP1Clean.Soundness
