import Clean.Air.Balance
import SP1Clean.Math.SP1Field

/-! # Physical count and LogUp balance of an installed channel -/

namespace SP1Clean.Export

open Circuit

/-- Exact count, signed balance, field fit and active matches for one whole physical ledger. -/
structure CheckedLedger (ledger : List (Interaction (ZMod SP1Prime))) (count : Nat) : Prop where
  /-- Physical count including zero-weight sites. -/
  size : ledger.length = count
  /-- Every encoded value has total signed multiplicity zero. -/
  signed : LogUpBalanced ledger
  /-- The entire occurrence count fits the released field. -/
  fits : (Balance.logUp (F := ZMod SP1Prime)).fits ledger.length = true
  /-- Every active occurrence has a matching occurrence of opposite sign. -/
  matched : BalancedInteractions ledger

end SP1Clean.Export
