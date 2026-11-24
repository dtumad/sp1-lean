import SP1Clean.Export.WriteMixedHostTables
import SP1Clean.Export.NativeShardBoundary
import SP1Clean.Proofs.Completeness.MixedCommitDeclarations
import ToClean.Air.StaticReadCounts

/-! # Counting the declaration reads of both physical commitment banks

A generated bank row retains its CPU call and selected slot. Agreement of the semantic
event with the public statement therefore pays for that row at the immutable provider.
Repeated declarations count once per active physical input.
-/

namespace SP1Clean.Export.CommitmentReaders

open Circuit Air.Flat Machine Semantics TraceGen FormalModel.Shard
open Soundness.Target (bitVecToWord)

private abbrev F := ZMod SP1Prime

variable {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot}
  {events : List ExecutionEvent} {statement : CommitmentStatement}
  (run : AdmissibleExecution limits SP1Prime image source target events)
  (agreement : statement.Matches events)

include agreement in
/-- Replay selects the very same declaration as the verifier-owned bank. -/
theorem covered (d : Bool) (row : CommitBanks.Entry) (used : row ∈ WriteMixedHostTables.bankRows run d) :
    CommitBanks.declaration d row.1 row.2 ∈ CommitmentDeclaration.rows statement := by
  obtain ⟨i, bound, same⟩ := List.getElem_of_mem used
  have origin := CommitBanks.rows_origins (WriteMixedHostTables.bankRows_eq run d)
  have inside : i < (CommitBanks.calls d events).length := origin.length_eq ▸ bound
  let call := (CommitBanks.calls d events)[i]
  obtain ⟨slot, message⟩ := origin.get bound inside
  change ((WriteMixedHostTables.bankRows run d)[i]).1.val = call.arg1.toNat at slot
  change ((WriteMixedHostTables.bankRows run d)[i]).2.call = CommitBanks.message call at message
  rw [same] at slot message
  have picked : call ∈ CommitBanks.calls d events := List.getElem_mem ..
  obtain ⟨event, seen, selected⟩ := List.mem_filterMap.mp picked
  obtain ⟨rfl, code⟩ := (CommitBanks.select_iff ..).mp selected
  have both := agreement _ seen
  have agreed : statement.MatchesDeclaration d call := by
    cases d
    · exact both.1
    · exact both.2
  obtain ⟨flag, index, argument, word⟩ := agreed code
  have small : index.val < 2^64 := by have := index.isLt; omega
  have index_eq : row.1 = index := by
    apply Fin.ext
    simpa only [argument, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using slot
  have fixed : CommitBanks.declaration d row.1 row.2 = CommitmentDeclaration.encode statement d index := by
    unfold CommitBanks.declaration CommitmentDeclaration.encode
    rw [flag, message, CommitBanks.arg2_field, word, index_eq]
    cases d <;> rfl
  rw [fixed]
  cases d
  · exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨_, rfl⟩)
  · exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨_, rfl⟩)

/-- All public and deferred reads in physical lane order, preserving their multiplicities. -/
def requests := CommitBanks.bankRequests false (WriteMixedHostTables.bankRows run false) ++
  CommitBanks.bankRequests true (WriteMixedHostTables.bankRows run true)

include agreement in
private theorem bank_covered (d : Bool) (r : CommitmentDeclaration.Row F)
    (seen : r ∈ CommitBanks.bankRequests d (WriteMixedHostTables.bankRows run d)) :
    (CommitmentDeclaration.table statement).Spec r := by
  obtain ⟨slot, _, member⟩ := List.mem_flatMap.mp seen
  obtain ⟨input, active, rfl⟩ := List.mem_map.mp member
  exact covered run agreement d (slot, input) ((CommitBanks.lane_mem ..).mp active)

include agreement in
private theorem requests_covered (r : CommitmentDeclaration.Row F) (requested : r ∈ requests run) :
    (CommitmentDeclaration.table statement).Spec r :=
  (List.mem_append.mp requested).elim (bank_covered run agreement false r) (bank_covered run agreement true r)

/-- The original sixteen-row provider with counts from both generated banks. -/
def provider (data : ProverData F) : Table F :=
  (CommitmentDeclaration.table statement).countedPayload CommitmentDeclaration.channel
    (fun _ _ _ => trivial) (CommitmentDeclaration.height_bounded statement)
    (requests run) (requests_covered run agreement) data

/-- Every provider row satisfies its constraints and the complete active demand balances. -/
theorem provider_checked (data : ProverData F) :
    let t := provider run agreement data
    t.Constraints ∧ t.Guarantees ∧
      (t.interactionsWith CommitmentDeclaration.channel.toRaw).length = (CommitmentDeclaration.table (p := SP1Prime) statement).height ∧
      LogUpBalanced (t.interactionsWith CommitmentDeclaration.channel.toRaw ++ (requests run).map CommitmentDeclaration.channel.pulledValue) :=
  (CommitmentDeclaration.table statement).countedPayload_checked CommitmentDeclaration.channel
    (fun _ _ _ => trivial) (CommitmentDeclaration.height_bounded statement)
    (requests run) (requests_covered run agreement) data

end SP1Clean.Export.CommitmentReaders

namespace SP1Clean.Export.NativeShard

open Circuit Air.Flat Machine Semantics FormalModel.Shard

private abbrev F := ZMod SP1Prime

variable {ctx : InstalledAssembly.Context} {events : List ExecutionEvent}
  (execution : ReleaseStatementExecution ctx.limits SP1Prime ctx.commitments ctx.image ctx.source ctx.target events)
  (w : EnsembleWitness (observer ctx)) (data : ProverData F)

/-- Append the fixed declaration source with the actual read counts of the two banks. -/
def withFundedDeclarations : EnsembleWitness (withDeclarations ctx) :=
  appendDeclaration ctx w (CommitmentReaders.provider execution.1.1 execution.2.2 data) rfl

/-- The provider consumes no new public input. Its full signed ledger follows the observer's. -/
theorem withFundedDeclarations_ledger (ch : RawChannel F) :
    (withFundedDeclarations execution w data).interactionsWith ch =
      w.interactionsWith ch ++ (CommitmentReaders.provider execution.1.1 execution.2.2 data).interactionsWith ch :=
  appendDeclaration_ledger ..

theorem withFundedDeclarations_header : (withFundedDeclarations execution w data).publicInput = w.publicInput := by
  simp only [withFundedDeclarations, appendDeclaration, Ensemble.AppendedTables.extend, EnsembleWitness.ofTables_publicInput]

end SP1Clean.Export.NativeShard
