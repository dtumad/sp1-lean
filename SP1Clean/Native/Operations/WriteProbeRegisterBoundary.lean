import SP1Clean.FormalModel.Contracts.WriteProbe
import SP1Clean.Semantics.Memory.MemorySnapshot
import SP1Clean.Semantics.ISA.Decode
import ToClean.Air.StaticProvider
import ToClean.Circuit.StaticTable

/-! # Verifier-fixed x12 versions at both complete shard boundaries

A WRITE probe for the incoming boundary can use the source register up to the incoming clock.
At or after the final clock it can use the target register. The two physical rows carry only
prover-owned multiplicities; both version endpoints and both words come from the verifier.
-/

namespace SP1Clean.WriteProbe

open Circuit Air.Flat Semantics Soundness.Target

variable {p : ℕ} [Fact p.Prime]

/-- x12 at the first cut, including an empty segment. -/
def incomingX12 (source : MemorySnapshot) (clock : ℕ) : Version (ZMod p) :=
  ⟨Address.ofNat 12, Address.ofNat 0, Address.ofNat clock, bitVecToWord (source.read (.reg 12))⟩

/-- x12 at the last cut. The represented time domain ends at the maximal 48-bit timestamp. -/
def outgoingX12 (target : MemorySnapshot) (clock : ℕ) : Version (ZMod p) :=
  ⟨Address.ofNat 12, Address.ofNat clock, Address.ofNat (2 ^ 48 - 1), bitVecToWord (target.read (.reg 12))⟩

/-- The immutable pair retains both occurrences, including when the boundary values agree. -/
def registerBoundaries (source target : MemorySnapshot) (first last : ℕ) : StaticTable (ZMod p) Version :=
  StaticTable.ofRows "sp1.native.write_x12_boundaries" [incomingX12 source first, outgoingX12 target last]

theorem registerBoundaries_height (source target : MemorySnapshot) (first last : ℕ) :
    (registerBoundaries (p := p) source target first last).height = 2 := by
  rfl

/-- The fixed-provider scheduler resolves demand on the actual version bus. -/
def registerBoundaryComponent (source target : MemorySnapshot) (first last : ℕ) : Component (ZMod p) :=
  (registerBoundaries source target first last).payloadComponent versionChannel (fun _ _ _ => trivial)
    (by rw [registerBoundaries_height]; decide)

/-- Any active version from an actual constrained physical provider is one of the two
boundary versions, regardless of its prover-supplied multiplicity. -/
theorem registerBoundary_authenticates (source target : MemorySnapshot) (first last : ℕ)
    (table : Table (ZMod p)) (family : table.component = registerBoundaryComponent source target first last)
    (checked : table.Constraints) :
    table.Authenticates versionChannel (fun row => row = incomingX12 source first ∨ row = outgoingX12 target last) := by
  apply ((registerBoundaries source target first last).payload_authenticates versionChannel
    (fun _ _ _ => trivial) _ table family checked).mono
  intro row member
  simpa [registerBoundaries, StaticTable.ofRows] using member

variable [Fact (2 ^ 17 < p)]

/-- Every clock matched by the incoming row of the physical table is at cut zero on the
actual timeline. Its four limbs are the immutable source register. -/
theorem incomingX12_at_cut (source : MemorySnapshot) (timeline : Timeline) (cut : ℕ)
    (representable : timeline.start 0 < 2 ^ 48)
    (covered : timeline.start cut ≤ Address.toNat (incomingX12 (p := p) source (timeline.start 0)).upper) :
    cut = 0 ∧ Word.toBitVec64 (incomingX12 (p := p) source (timeline.start 0)).value = source.read (.reg 12) := by
  change timeline.start cut ≤ Address.toNat (Address.ofNat (p := p) (timeline.start 0)) at covered
  rw [Address.toNat_ofNat _ representable] at covered
  refine ⟨?_, toBitVec64_bitVecToWord _⟩
  by_contra other
  exact (Nat.not_lt_of_le covered) (timeline.start_lt_of_lt (Nat.pos_of_ne_zero other))

/-- An in-range CPU cut matching the terminal version is the final cut and observes the
immutable target register. -/
theorem outgoingX12_at_cut (target : MemorySnapshot) (timeline : Timeline) {cut last : ℕ} (inside : cut ≤ last)
    (representable : timeline.start last < 2 ^ 48)
    (covered : Address.toNat (outgoingX12 (p := p) target (timeline.start last)).lower ≤ timeline.start cut) :
    cut = last ∧ Word.toBitVec64 (outgoingX12 (p := p) target (timeline.start last)).value = target.read (.reg 12) := by
  change Address.toNat (Address.ofNat (p := p) (timeline.start last)) ≤ timeline.start cut at covered
  rw [Address.toNat_ofNat _ representable] at covered
  refine ⟨?_, toBitVec64_bitVecToWord _⟩
  by_contra other
  exact (Nat.not_lt_of_le covered) (timeline.start_lt_of_lt (lt_of_le_of_ne inside other))

end SP1Clean.WriteProbe
