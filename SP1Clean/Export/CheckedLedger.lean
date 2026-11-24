import ToClean.Air.MessageFilter
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

/-- Changing the order of complete physical groups preserves their count, funding and active matches. -/
theorem CheckedLedger.of_perm {xs ys : List (Interaction (ZMod SP1Prime))} {count : Nat}
    (paid : CheckedLedger xs count) (same : ys.Perm xs) : CheckedLedger ys count :=
  ⟨same.length_eq.trans paid.size, fun value => (balanceOf_perm same).trans (paid.signed value),
    same.length_eq ▸ paid.fits, BalancedInteractions.of_perm paid.matched same.symm⟩

end SP1Clean.Export
