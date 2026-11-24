import SP1Clean.Proofs.Operations.WriteBufferLedger
import SP1Clean.Soundness.RankedCoverage
import ToClean.Air.MessageFilter

/-! # Every aligned WRITE buffer word is demanded once

The clock-selected span and word rows retain their original activity and physical signed
receipts. Balance produces a consecutive exhaustive path, so omissions, duplications, and
disconnected additional word rows cannot survive. No word verifier supplies that order.
-/

namespace SP1Clean.WriteBuffer
open Circuit Air.Flat Soundness Soundness.RankedGrounding
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The actual two cursor interactions of a decoded physical word row. -/
def wordCursors (r : WordRow (ZMod p)) : List (Interaction (ZMod p)) :=
  [channel.pulledIfValue r.2 r.1.source, channel.pushedIfValue r.2 r.1.target]

/-- The source and exclusive-stop occurrences of one decoded physical header. -/
def spanCursors (r : SpanRow (ZMod p)) : List (Interaction (ZMod p)) :=
  [channel.pushedIfValue r.2 r.1.source, channel.pulledIfValue r.2 r.1.target]

/-- Decode canonical inputs from each original physical row's own data. -/
def wordInput (env : Environment (ZMod p)) : WordRow (ZMod p) := valueFromOffset WordRow 0 env
/-- Decode the physical span at its own witness environment. -/
def spanInput (env : Environment (ZMod p)) : SpanRow (ZMod p) := valueFromOffset SpanRow 0 env

/-- Raw word constraints and the installed Byte provider give the active row's contract. -/
theorem wordInput_valid (env : Environment (ZMod p)) (checked : wordComponent.operations.ConstraintsHold env)
    (bytes : wordComponent.operations.ChannelGuarantees Channels.byteChannel.toRaw env) :
    IsBool (wordInput env).2 ∧ ((wordInput env).2 = 1 → (wordInput env).1.Valid) := by
  have assumed : wordComponent.CircuitAssumptions env := fun _ => trivial
  apply (Component.weakSoundness assumed checked ?_).1
  rw [Operations.guarantees_iff _ _ _ (wordComponent.inChannelsOrGuarantees env)]
  intro selected member
  have classified : selected = Channels.byteChannel.toRaw ∨ selected = WriteProbe.readChannel.toRaw ∨ selected = channel.toRaw := by
    change selected ∈ [Channels.byteChannel.toRaw, channel.toRaw, WriteProbe.readChannel.toRaw] at member
    simpa [or_assoc, or_left_comm, or_comm] using member
  rcases classified with rfl | rfl | rfl
  · exact bytes
  · exact Operations.channelGuarantees_of_trivial _ (by simp [WriteProbe.readChannel, Channel.toRaw]) _ _
  · exact Operations.channelGuarantees_of_trivial _ (by simp [channel, Channel.toRaw]) _ _

/-- Raw span constraints and the installed Byte provider give the active row's contract. -/
theorem spanInput_valid (env : Environment (ZMod p)) (checked : spanComponent.operations.ConstraintsHold env)
    (bytes : spanComponent.operations.ChannelGuarantees Channels.byteChannel.toRaw env) :
    IsBool (spanInput env).2 ∧ ((spanInput env).2 = 1 → (spanInput env).1.Valid) := by
  have assumed : spanComponent.CircuitAssumptions env := fun _ => trivial
  apply (Component.weakSoundness assumed checked ?_).1
  rw [Operations.guarantees_iff _ _ _ (spanComponent.inChannelsOrGuarantees env)]
  intro selected member
  have classified : selected = Channels.byteChannel.toRaw ∨ selected = WritePacket.channel.toRaw ∨ selected = channel.toRaw := by
    change selected ∈ [Channels.byteChannel.toRaw, Channels.byteChannel.toRaw, Channels.byteChannel.toRaw,
      Channels.byteChannel.toRaw, Channels.byteChannel.toRaw, Channels.byteChannel.toRaw, WritePacket.channel.toRaw, channel.toRaw] at member
    simpa [or_assoc, or_left_comm, or_comm] using member
  rcases classified with rfl | rfl | rfl
  · exact bytes
  · exact Operations.channelGuarantees_of_trivial _ (by simp [WritePacket.channel, Channel.toRaw]) _ _
  · exact Operations.channelGuarantees_of_trivial _ (by simp [channel, Channel.toRaw]) _ _

theorem wordInput_cursor_ledger (env : Environment (ZMod p)) :
    wordComponent.operations.interactionValuesWith channel.toRaw env = wordCursors (wordInput env) := by
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((wordComponent.circuit.main (varFromOffset WordRow 0)).operations (size WordRow)).interactionValuesWith channel.toRaw env = _
  rw [word_cursors, Guarded.eval_activity]
  have dec (s : Var WordRow (ZMod p)) : ProvableStruct.eval env s.1 = (eval env s).1 := by simp only [circuit_norm]
  simp only [dec, eval_varFromOffset_valueFromOffset, wordInput, wordCursors]

theorem spanInput_cursor_ledger (env : Environment (ZMod p)) :
    spanComponent.operations.interactionValuesWith channel.toRaw env = spanCursors (spanInput env) := by
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((spanComponent.circuit.main (varFromOffset SpanRow 0)).operations (size SpanRow)).interactionValuesWith channel.toRaw env = _
  rw [span_cursors, Guarded.eval_activity]
  have dec (s : Var SpanRow (ZMod p)) : ProvableStruct.eval env s.1 = (eval env s).1 := by simp only [circuit_norm]
  simp only [dec, eval_varFromOffset_valueFromOffset, spanInput, spanCursors]

omit [Fact (2 ^ 17 < p)] in
/-- Both ends of every edge carry the same incoming clock, so full-message selection
commutes with taking all physical signed cursor interactions, including padding. -/
theorem select_clock {spans : List (SpanRow (ZMod p))} {words : List (WordRow (ZMod p))}
    (balanced : BalancedInteractions (spans.flatMap spanCursors ++ words.flatMap wordCursors))
    (clock : fields 3 (ZMod p)) :
    BalancedInteractions ((spans.filter (fun r => decide (r.1.header.clock = clock))).flatMap spanCursors ++
      (words.filter (fun r => decide (r.1.read.clock = clock))).flatMap wordCursors) := by
  let select := ProvableType.selectMessage fun (c : Cursor (ZMod p)) => decide (c.clock = clock)
  have selectSpans := selectedRows_interactions spans spanCursors (fun r => decide (r.1.header.clock = clock)) select
  have selectWords := selectedRows_interactions words wordCursors (fun r => decide (r.1.read.clock = clock)) select
  rw [selectSpans, selectWords, ← List.filter_append]
  · exact balanced.filter_messages select
  · intro r _ i member
    rcases List.mem_cons.mp member with rfl | member
    · exact ProvableType.selectMessage_toElements _ _
    · obtain rfl := List.mem_singleton.mp member
      exact ProvableType.selectMessage_toElements _ _
  · intro r _ i member
    rcases List.mem_cons.mp member with rfl | member
    · exact ProvableType.selectMessage_toElements _ _
    · obtain rfl := List.mem_singleton.mp member
      exact ProvableType.selectMessage_toElements _ _

omit [Fact (2 ^ 17 < p)] in
/-- The physical class for one header contains exactly the consecutive absolute indices
required by the header's actual u64 address and length. The path preserves every row,
and every read key is exactly eight times its index at that header's clock. -/
theorem ordered_words (s : Span (ZMod p)) (span : s.Valid) (words : List (WordRow (ZMod p)))
    (checked : ∀ r ∈ words, IsBool r.2 ∧ (r.2 = 1 → r.1.Valid))
    (balanced : BalancedInteractions (spanCursors (s, 1) ++ words.flatMap wordCursors)) :
    ∃ path, path.Perm (words.filter (fun r => @decide (r.2 = 1) (FiniteField.instDecidableEq r.2 1))) ∧
      Walk.IsWalk (fun r : WordRow (ZMod p) => (r.1.source, r.1.target)) s.source s.target path ∧
      path.map (fun r => Address.toNat r.1.index) =
        List.range' (s.header.address.toNat / 8) ((s.header.address.toNat % 8 + s.header.length.toNat + 7) / 8) ∧
      ∀ r ∈ path, r.1.read.clock = s.header.clock ∧ Address.toNat r.1.read.key = 8 * Address.toNat r.1.index := by
  let edge := fun r : WordRow (ZMod p) => (r.1.source, r.1.target)
  let active := words.filter fun r => @decide (r.2 = 1) (FiniteField.instDecidableEq r.2 1)
  have good r (m : r ∈ active) : r.1.Valid := by
    simp only [active, List.mem_filter, decide_eq_true_eq] at m
    exact (checked r m.1).2 m.2
  have ends : EndpointBalanced (↑active) edge s.source s.target := by
    have matched := (channel.gatedTransitionLedger_balanced_iff s.source s.target words Prod.snd edge
      (fun r m => (checked r m).1)).mp balanced
    simpa only [EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe, active] using matched
  obtain ⟨path, perm, walk, count, indices, _, clocks⟩ :=
    consecutive_coverage edge (fun c : Cursor (ZMod p) => Address.toNat c.index) Cursor.clock active s.source s.target ends
      (fun r m => (good r m).2.2.2.2) (fun _ _ => rfl)
  obtain ⟨_, _, _, _, _, _, _, _, start, stop⟩ := span
  change Address.toNat s.stop = Address.toNat s.first + path.length at count
  rw [start, stop] at count
  change path.map _ = List.range' (Address.toNat s.first) path.length at indices
  rw [start] at indices
  have length : path.length = (s.header.address.toNat % 8 + s.header.length.toNat + 7) / 8 := by omega
  exact ⟨path, perm, walk, by rwa [length] at indices, fun r m => ⟨clocks r m, (good r (perm.mem_iff.mp m)).2.2.2.1⟩⟩

omit [Fact (2 ^ 17 < p)] in
/-- A clock class with no active header cannot support an orphan cycle of word rows.
Zero-weight padding is retained in the signed balance premise. -/
theorem no_orphan_words (words : List (WordRow (ZMod p)))
    (checked : ∀ r ∈ words, IsBool r.2 ∧ (r.2 = 1 → r.1.Valid))
    (balanced : BalancedInteractions (words.flatMap wordCursors)) :
    (words.filter fun r => @decide (r.2 = 1) (FiniteField.instDecidableEq r.2 1)) = [] := by
  let edge := fun r : WordRow (ZMod p) => (r.1.source, r.1.target)
  let active := words.filter fun r => @decide (r.2 = 1) (FiniteField.instDecidableEq r.2 1)
  have pos r (member : r ∈ active) : Address.toNat (edge r).2.index = Address.toNat (edge r).1.index + 1 := by
    simp only [active, List.mem_filter, decide_eq_true_eq] at member
    exact ((checked r member.1).2 member.2).2.2.2.2
  have kept := balanced.filter_nonzero
  have filtered := channel.gatedPairs_filter_nonzero words Prod.snd edge (fun r m => (checked r m).1)
  unfold wordCursors at kept
  dsimp only [edge] at filtered
  rw [filtered] at kept
  apply nil_of_closed edge (fun c : Cursor (ZMod p) => Address.toNat c.index) active _ pos
  exact (channel.pairedLedger_balanced_iff _ edge).mp kept

end SP1Clean.WriteBuffer
