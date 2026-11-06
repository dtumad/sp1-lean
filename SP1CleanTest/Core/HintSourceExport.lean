import Clean.Air.Balance
import SP1CleanTest.Core.ComponentExport
import SP1Clean.Native.Operations.HintQueueSource
import SP1Clean.Native.Operations.HintQueueWordSource
import ToClean.Air.EnsembleCheck
import ToClean.Circuit.VerifierInteractions

/-! # Closed fixed-source hint export through Clean

The actual node/word providers serve public requests through Clean's existing preallocated
scheduler. Complete physical rows and zero-count occurrences remain visible to the checker
and Rust reference. Native source-queue authentication is separate from full host execution.
-/

namespace SP1CleanTest.Core.HintSourceExport

open Circuit Air.Flat SP1Clean Model.Core HintQueue
open ComponentExport (Fp)

/-- A production fixed inventory and its existing semantic channel. -/
structure Source (Row : TypeMap) [ProvableType Row] where
  /-- Literal source meanings owned by the model. -/
  table : StaticTable Fp Row
  /-- Existing consumer channel; no additional membership protocol is introduced. -/
  channel : Channel Fp Row
  /-- Static membership establishes the channel's local semantic guarantee. -/
  valid : ∀ row, table.Spec row → ∀ data, channel.Guarantees row data
  /-- Every physical row is representable by the upstream scheduler. -/
  bounded : table.height < UInt64.size

/-- The complete production node source. -/
def nodes (hints : List Bytes) : Source NodeRecord :=
  ⟨sourceTable hints, HostHintQueue.nodeChannel,
    fun record member _ => (sourceTable_sound hints record member).1,
    HostHintQueue.source_height_lt_uint64 hints⟩

/-- The complete production word source, including final padding words. -/
def words (hints : List Bytes) : Source WordRecord :=
  ⟨HostHintQueue.sourceWordInventory hints, HostHintQueue.wordChannel,
    fun record member _ => (sourceWordTable_sound hints record
      (HostHintQueue.sourceWordInventory_spec hints record member)).1,
    HostHintQueue.sourceWord_height_lt_uint64 hints⟩

variable {Row : TypeMap} [ProvableType Row]

/-- Retain the production component, fixed columns and semantic circuit. -/
def component (source : Source Row) : Component Fp :=
  source.table.payloadComponent source.channel source.valid source.bounded

/-- Every supplied record is a separate public unit request, including repeated records. -/
def verifier (source : Source Row) (n : ℕ) : Verifier.Program Fp (ProvableVector Row n) where
  Spec _ _ := True
  soundness := by intros; trivial
  main requests := Verifier.ofInteractions
    (requests.toList.map fun request => (source.channel.pulled request).toRaw)
    (by
      intro interaction member env
      obtain ⟨request, _, rfl⟩ := List.mem_map.mp member
      simp [circuit_norm, ChannelInteraction.Requirements])

/-- A closed source ensemble binds counts to the complete public request ledger. -/
def ensemble (source : Source Row) (n : ℕ) : Ensemble Fp (ProvableVector Row n) where
  tables := [component source]
  unique_names := by simp
  channels := [source.channel.toRaw]
  verifier := verifier source n
  unique_channel_names := by simp
  tables_channels := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    change [source.channel.toRaw] ⊆ _
    simp
  verifier_channels := by
    intro channel member
    rw [Verifier.Program.mem_channels_iff, Operations.channels] at member
    change channel ∈ ((verifier source n).circuitOperations.interactions.map (·.channel)) at member
    simp only [Verifier.Program.circuitOperations, Verifier.Program.operations, verifier,
      Verifier.ofInteractions_interactions, List.map_map, Function.comp_def] at member
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    exact List.mem_singleton.mpr rfl

/-- The executable relation checks all source assertions and complete counted occurrences. -/
def description (source : Source Row) (n : ℕ) : EnsembleCheck (ensemble source n) where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [ensemble, component, Component.lookups_eq, Component.rowOperations,
      StaticTable.payloadComponent, StaticTable.payloadProvider, circuit_norm]
/-- Generate the fixed inventory and counts entirely through Clean's shared scheduler. -/
def generate (source : Source Row) (requests : List (Row Fp)) :
    Except String (EnsembleWitness (ensemble source requests.length)) :=
  WitnessGeneration.generate (ensemble source requests.length)
    (2 * requests.length + 2) ⟨requests.toArray, by simp⟩ () |>.mapError toString

/-- Source-only regressions expose the actual table ledger, including every zero count. -/
def observe (source : Source Row) (record : Row Fp) : Bool × List (String × List Fp × Fp) :=
  match generate source [record] with
  | .error _ => (false, [])
  | .ok witness =>
      ((description source 1).checkWitness witness,
        witness.tables.flatMap fun table => table.interactions.map fun interaction =>
          (interaction.channel.name, interaction.msg.toList, interaction.signedMult))

/-- Uneven, aligned and empty hints exercise padding and reversed physical node identities. -/
def hints : List Bytes := [[17, 34, 51, 68, 85, 102, 119, 136, 153, 170],
  [1, 2, 3, 4, 5, 6, 7, 8], []]

/-- Emit both source kinds with two public requests, and their unused and empty-source forms. -/
def rustExports : List (String × Except String String) :=
  [("hint_nodes.rs", Backends.Plonky3.Print.ensembleToRust
      (ComponentExport.fixture (ensemble (nodes hints) 2)) (2 * 2 + 2)),
   ("hint_words.rs", Backends.Plonky3.Print.ensembleToRust
      (ComponentExport.fixture (ensemble (words hints) 2)) (2 * 2 + 2)),
   ("hint_nodes_unused.rs", Backends.Plonky3.Print.ensembleToRust
      (ComponentExport.fixture (ensemble (nodes hints) 0)) (2 * 0 + 2)),
   ("hint_words_unused.rs", Backends.Plonky3.Print.ensembleToRust
      (ComponentExport.fixture (ensemble (words hints) 0)) (2 * 0 + 2)),
   ("hint_nodes_empty.rs", Backends.Plonky3.Print.ensembleToRust
      (ComponentExport.fixture (ensemble (nodes []) 2)) (2 * 2 + 2)),
   ("hint_words_empty.rs", Backends.Plonky3.Print.ensembleToRust
      (ComponentExport.fixture (ensemble (words []) 2)) (2 * 2 + 2))]

end SP1CleanTest.Core.HintSourceExport
