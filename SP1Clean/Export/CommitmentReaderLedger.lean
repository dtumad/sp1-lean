import SP1Clean.Export.CommitmentReaders
import SP1Clean.Export.CheckedLedger

/-! # Funding the physical declaration ledger

The sixteen commitment lanes read the declarations selected by the chronological tape.
Every fixed provider row and every padded lane contributes its own occurrence to the field bound.
-/

namespace SP1Clean.Export.CommitmentReaders

open Circuit Air.Flat Machine Semantics TraceGen FormalModel.Shard

private abbrev F := ZMod SP1Prime
private abbrev ch := CommitmentDeclaration.channel (p := SP1Prime)

variable {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
  {statement : CommitmentStatement}
  (run : AdmissibleExecution limits SP1Prime image source target events)
  (agreement : statement.Matches events) (data : ProverData F)

/-- The reads of the eight original components of a physical bank, retaining padding. -/
noncomputable def reads (d : Bool) : List (Interaction F) :=
  (List.finRange 8).flatMap fun slot =>
    (WriteMixedHostTables.table run data (.bank d (some slot))).interactionsWith ch.toRaw

/-- The provider has sixteen sites, followed in the count by the actual heights of both banks. -/
def sites : ℕ := 16 + CommitBanks.declarationSites (WriteMixedHostTables.bankRows run false) +
  CommitBanks.declarationSites (WriteMixedHostTables.bankRows run true)

private theorem reads_length (d : Bool) :
    (reads run data d).length = CommitBanks.declarationSites (WriteMixedHostTables.bankRows run d) :=
  CommitBanks.declarationLedger_length d _ data (WriteMixedHostTables.bankLaneFits run d)

private theorem reads_sum (d : Bool) (msg : Array F) :
    balanceOf (reads run data d) msg =
      balanceOf ((CommitBanks.bankRequests d (WriteMixedHostTables.bankRows run d)).map ch.pulledValue) msg :=
  CommitBanks.declarationLedger_sum d _ data (WriteMixedHostTables.bankLaneFits run d) msg

private theorem sites_bound (preset : limits.LE (.native SP1Prime)) : sites run < SP1Prime := by
  have each (d : Bool) : CommitBanks.declarationSites (WriteMixedHostTables.bankRows run d) ≤ 8 * 2^21 := by
    apply CommitBanks.declarationSites_le
    rw [(CommitBanks.rows_origins (WriteMixedHostTables.bankRows_eq run d)).length_eq]
    exact (List.length_filterMap_le ..).trans (run.work.1.trans preset.1)
  have hard : 16 + 2 * (8 * 2^21) < SP1Prime := by decide
  have publicBank := each false
  have deferredBank := each true
  unfold sites
  omega

/-- The exact payout of the immutable source and the complete padded reader occurrences,
including empty banks and repeated declarations. -/
theorem physical_checked (preset : limits.LE (.native SP1Prime)) :
    CheckedLedger ((reads run data false ++ reads run data true) ++
      (provider run agreement data).interactionsWith ch.toRaw) (sites run) := by
  obtain ⟨_, _, providerCount, activePaid⟩ := provider_checked run agreement data
  have fixed : (CommitmentDeclaration.table (p := SP1Prime) statement).height = 16 := by
    simp only [StaticTable.height, CommitmentDeclaration.table, StaticTable.ofRows, CommitmentDeclaration.rows,
      List.length_append, List.length_ofFn]
    decide
  let ledger := (reads run data false ++ reads run data true) ++ (provider run agreement data).interactionsWith ch.toRaw
  have count : ledger.length = sites run := by
    simp only [ledger, List.length_append, reads_length, providerCount, fixed, sites]
    omega
  have signed : LogUpBalanced ledger := by
    intro msg
    have paid := activePaid msg
    simp only [requests, List.map_append, balanceOf_append] at paid
    simp only [ledger, balanceOf_append, reads_sum]
    rw [add_comm]
    exact paid
  have fit : (Balance.logUp (F := F)).fits ledger.length = true := by
    simp only [Balance.logUp, decide_eq_true_eq, ComputableRingChar.char_eq, ZMod.ringChar_zmod_n, count]
    exact sites_bound run preset
  exact ⟨count, signed, fit, Balance.logUp.balancedInteractions_of_balanced _ fit signed⟩

end SP1Clean.Export.CommitmentReaders
