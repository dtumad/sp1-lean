import SP1Clean.Proofs.Completeness.WriteBlockRequests
import ToClean.Air.GuardedLedger

/-! # Per-message totals on the two WRITE block ledgers

The full ledgers keep both sites of every row, including demand padding. In the signed
sum, a live placement contributes one pull per selected side and a returned allocation
word contributes one pull. The other allocation-word site contributes its actual
reader multiplicity at the immutable direct block.
-/

namespace SP1Clean.WriteEffects.Witness
open Circuit Air.Flat WriteAllocation
private abbrev F := ZMod SP1Prime

private theorem gated (gate : F) (binary : IsBool gate) (b : StreamBlock F) (msg : Array F) :
    balanceOf [blockChannel.pulledIfValue gate b] msg =
      balanceOf ((if gate = 1 then [b] else []).map blockChannel.pulledValue) msg := by
  rcases binary with rfl | rfl
  · rw [balanceOf_cons]
    simp [Channel.pulledIfValue,Interaction.signedMult,balanceOf]
  · simp
    rfl

private theorem group_row (r : Group F) (valid : r.Valid) (msg : Array F) :
    balanceOf (groupBlocks (r,1)) msg = balanceOf ((directRequests r).map blockChannel.pulledValue) msg := by
  obtain ⟨_,_,ignored,left,right,_⟩ := valid
  have binary : IsBool r.leftGate ∧ IsBool r.rightGate := by
    by_cases zero : r.previous.sink = 0
    · simp [Group.leftGate,Group.rightGate,ignored,zero,IsBool]
    · simpa [Group.leftGate,Group.rightGate,ignored,zero] using And.intro left right
  simp only [groupBlocks,directRequests,one_mul,List.map_append]
  rw [show [blockChannel.pulledIfValue r.leftGate (r.block false),blockChannel.pulledIfValue r.rightGate (r.block true)] =
    [blockChannel.pulledIfValue r.leftGate (r.block false)] ++ [blockChannel.pulledIfValue r.rightGate (r.block true)] from rfl,
    balanceOf_append,balanceOf_append,gated _ binary.1,gated _ binary.2]

/-- The full physical group table carries one unit pull for each selected side, even when
two sides in different guest words use the same block. Disabled and padded sites sum to zero. -/
theorem groupTable_demand (groups : List (Group F)) (honest : ∀ g ∈ groups, g.Valid ∧ g.HonestCoordinates)
    (data : ProverData F) (fit) (msg : Array F) :
    balanceOf ((groupTable groups data fit).interactionsWith blockChannel.toRaw) msg =
      balanceOf ((groups.flatMap directRequests).map blockChannel.pulledValue) msg := by
  rw [groupTable_blocks,WitnessGeneration.guardedRows_balanceOf]
  · clear fit
    induction groups with
    | nil => rfl
    | cons r rest ih =>
      simp only [List.flatMap_cons,List.map_append,balanceOf_append]
      rw [group_row r (honest r List.mem_cons_self).1 msg,ih (fun g h => honest g (List.mem_cons_of_mem _ h))]
  · simp only [groupBlocks,balanceOf_cons]
    simp [Channel.pulledIfValue,Interaction.signedMult,balanceOf]

private theorem hook_binary (r : Words.Row F) (valid : r.Valid) : IsBool r.hookGate := by
  rcases valid.1 with direct | direct
  · simpa [Words.Row.hookGate,direct] using (valid.2.1 0).2.1
  · simp [Words.Row.hookGate,direct,IsBool]

/-- The returned-block debit and counted direct-block credit are the two actual sites of
each generated word. Their independent physical padding contributes zero to each message. -/
theorem wordTable_demand (rows : List (Words.Row F)) (valid : ∀ r ∈ rows, r.Valid)
    (data : ProverData F) (fit) (msg : Array F) :
    balanceOf ((Words.wordTable rows data fit).interactionsWith blockChannel.toRaw) msg =
      balanceOf ((returnedRequests rows).map blockChannel.pulledValue) msg +
        balanceOf (rows.map (fun r => blockChannel.emittedValue (r.directGate*r.blockReads) r.direct)) msg := by
  rw [Words.wordTable_blocks rows valid,WitnessGeneration.guardedRows_balanceOf]
  · clear fit
    induction rows with
    | nil => simp [balanceOf,returnedRequests]
    | cons r rest ih =>
      let pull := blockChannel.pulledIfValue r.hookGate r.returned
      let push := blockChannel.emittedValue (r.directGate*r.blockReads) r.direct
      have split : Words.blockTraffic (r,1) = [pull] ++ [push] := by simp [Words.blockTraffic,pull,push]
      have next := ih (fun x h => valid x (List.mem_cons_of_mem _ h))
      have side := gated r.hookGate (hook_binary r (valid r List.mem_cons_self)) r.returned msg
      have blocks : returnedRequests (r::rest) =
          (if r.hookGate = 1 then [r.returned] else []) ++ returnedRequests rest := by
        by_cases enabled : r.hookGate = 1 <;> simp [returnedRequests,enabled]
      rw [List.flatMap_cons,split,balanceOf_append,balanceOf_append,next,blocks,List.map_append,balanceOf_append]
      change balanceOf [blockChannel.pulledIfValue r.hookGate r.returned] msg + _ + _ = _ + balanceOf ([push] ++ _) msg
      rw [side,balanceOf_append]
      ac_rfl
  · simp only [Words.blockTraffic,balanceOf_cons]
    simp [Channel.pulledIfValue,Channel.emittedValue,Interaction.signedMult,balanceOf]

end SP1Clean.WriteEffects.Witness
