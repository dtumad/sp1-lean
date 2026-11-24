import SP1Clean.Proofs.Operations.WriteProbe
import SP1Clean.Proofs.Completeness.WriteObservationCuts

/-! # Generating observation inputs from genuine Memory versions

The encoder clips the upper endpoint to the native clock domain and discards empty
ranges. Genesis includes clock zero and the final version includes the largest clock.
-/

namespace SP1Clean.WriteProbe

open Semantics Soundness.Target Soundness.WriteObservationHistory

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- First representable integer clock strictly following any real preceding effect. -/
def firstClock (v : VersionInterval p) : ℕ :=
  (v.previous.map (fun m => MemoryMsg.timeNat m + 1)).getD 0

/-- Exclusive end, clipped at the mathematical one-past 48-bit clock domain. -/
def endClock (v : VersionInterval p) : ℕ :=
  min ((v.next.map MemoryMsg.timeNat).getD (2 ^ 48)) (2 ^ 48)

private theorem optional_window {α : Type} (time : α → ℕ) (previous next : Option α) (clock cap : ℕ)
    (bound : clock < cap) :
    (previous.all (fun m => decide (time m < clock)) && next.all (fun m => decide (clock < time m))) = true ↔
      (previous.map (fun m => time m + 1)).getD 0 ≤ clock ∧ clock < min ((next.map time).getD cap) cap := by
  cases previous <;> cases next <;> simp [lt_min_iff, bound]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
theorem coversClock_iff (v : VersionInterval p) {clock : ℕ} (bound : clock < 2 ^ 48) :
    v.coversClock clock = true ↔ firstClock v ≤ clock ∧ clock < endClock v :=
  optional_window MemoryMsg.timeNat v.previous v.next clock (2 ^ 48) bound

/-- Encode one genuine version only if its key and at least one clock are representable. -/
def encodeVersion? (snapshot : MemorySnapshot) (loc : MemLoc) (v : VersionInterval p) : Option (Version (ZMod p)) :=
  if loc.busAddress < 2 ^ 48 ∧ firstClock v < endClock v then
    some ⟨Address.ofNat loc.busAddress, Address.ofNat (firstClock v), Address.ofNat (endClock v - 1),
      v.value (bitVecToWord (snapshot.read loc))⟩
  else none

/-- The 48-bit closed range on the private interval bus is equivalent to the two actual
Memory-clock comparisons at every representable time. -/
theorem encodeVersion?_clock {snapshot : MemorySnapshot} {loc : MemLoc} {v : VersionInterval p}
    {version : Version (ZMod p)} (built : encodeVersion? snapshot loc v = some version)
    {clock : ℕ} (bound : clock < 2 ^ 48) :
    (Address.toNat version.lower ≤ clock ∧ clock ≤ Address.toNat version.upper) ↔ v.coversClock clock = true := by
  unfold encodeVersion? at built
  split at built
  · rename_i allowed
    obtain rfl := Option.some.inj built
    have ceiling : endClock v ≤ 2 ^ 48 := Nat.min_le_right ..
    have nonempty := allowed.2
    simp only [Address.toNat_ofNat _ (show firstClock v < 2 ^ 48 by omega),
      Address.toNat_ofNat _ (show endClock v - 1 < 2 ^ 48 by omega), coversClock_iff v bound]
    omega
  · contradiction

/-- Physical suppliers can offer a narrower interval when genuine read-back accesses split an
unchanged word. The key and value must still be the original payload. -/
def Version.Restricts (offered genuine : Version (ZMod p)) : Prop :=
  offered.key = genuine.key ∧ offered.value = genuine.value ∧
  Address.toNat genuine.lower ≤ Address.toNat offered.lower ∧
  Address.toNat offered.upper ≤ Address.toNat genuine.upper

omit [Fact (2 ^ 17 < p)] in
private theorem encodeVersion?_payload {snapshot : MemorySnapshot} {loc : MemLoc} {v : VersionInterval p}
    {version : Version (ZMod p)} (built : encodeVersion? snapshot loc v = some version) :
    version.key = Address.ofNat loc.busAddress ∧ version.value = v.value (bitVecToWord (snapshot.read loc)) := by
  unfold encodeVersion? at built
  split at built
  · cases Option.some.inj built
    exact ⟨rfl, rfl⟩
  · contradiction

/-- An accepted row consuming a subinterval of a real physical version returns that version's
unchanged value at its clock. The endpoint check is the one enforced by the probe circuit. -/
theorem read_of_restriction {snapshot : MemorySnapshot} {loc : MemLoc} {v : VersionInterval p}
    {genuine : Version (ZMod p)} (encoded : encodeVersion? snapshot loc v = some genuine)
    {input : Inputs (ZMod p)} (row : Spec input) (supply : input.version.Restricts genuine) :
    input.read.key = Address.ofNat loc.busAddress ∧ v.coversClock (Address.toNat input.clock) = true ∧
      input.read.value = v.value (bitVecToWord (snapshot.read loc)) := by
  obtain ⟨key, value, lower, upper⟩ := supply
  obtain ⟨_, _, _, _, clock, _, first, last⟩ := row
  obtain ⟨address, held⟩ := encodeVersion?_payload encoded
  exact ⟨key.trans address, (encodeVersion?_clock encoded (Address.toNat_lt clock)).mp
    ⟨lower.trans first, last.trans upper⟩, value.trans held⟩

/-- A genuine in-range cut constructs exactly the read that the caller requests; the
circuit's division witness is derived from the physical key. -/
theorem populate_covered (snapshot : MemorySnapshot) (loc : MemLoc) (v : VersionInterval p)
    {clock : ℕ} (bound : clock < 2 ^ 48) (covered : v.coversClock clock = true)
    (key : ValidKey loc.busAddress) (canonical : Word.isU64 (v.value (bitVecToWord (snapshot.read loc)))) :
    ∃ version, encodeVersion? snapshot loc v = some version ∧
      ProverAssumptions (populate version (Address.ofNat clock)) ∧
      (populate version (Address.ofNat clock)).read =
        ⟨Address.ofNat loc.busAddress, Address.ofNat clock, v.value (bitVecToWord (snapshot.read loc))⟩ := by
  have keyLt : loc.busAddress < 2 ^ 48 := by rcases key with eq | range; omega; exact range.2.1
  obtain ⟨first, last⟩ := (coversClock_iff v bound).mp covered
  have nonempty := first.trans_lt last
  have ceiling : endClock v ≤ 2 ^ 48 := Nat.min_le_right ..
  let version : Version (ZMod p) := ⟨Address.ofNat loc.busAddress, Address.ofNat (firstClock v),
    Address.ofNat (endClock v - 1), v.value (bitVecToWord (snapshot.read loc))⟩
  have lower : firstClock v < 2 ^ 48 := first.trans_lt bound
  have upper : endClock v - 1 < 2 ^ 48 := by omega
  refine ⟨version, by rw [encodeVersion?, ite_eq_left ⟨keyLt, nonempty⟩], ⟨?_, rfl⟩, rfl⟩
  change Address.Bounded _ ∧ ValidKey (Address.toNat (Address.ofNat (p := p) loc.busAddress)) ∧
    _ ∧ Address.Bounded _ ∧ Address.Bounded _ ∧ Address.Bounded _ ∧
    Address.toNat (Address.ofNat (p := p) (firstClock v)) ≤ Address.toNat (Address.ofNat clock) ∧
    Address.toNat (Address.ofNat (p := p) clock) ≤ Address.toNat (Address.ofNat (endClock v - 1))
  rw [Address.toNat_ofNat _ keyLt, Address.toNat_ofNat _ bound, Address.toNat_ofNat _ lower, Address.toNat_ofNat _ upper]
  exact ⟨Address.bounded_ofNat _, key, canonical, Address.bounded_ofNat _, Address.bounded_ofNat _, Address.bounded_ofNat _, first, by omega⟩

/-- Select the version at the requested physical clock. The final receipt's key and value
come only from the selected interval and the original snapshot. -/
def inputAt? (snapshot : MemorySnapshot) (rows : List (RowFacts p)) (loc : MemLoc) (clock : ℕ) :
    Option (Inputs (ZMod p)) :=
  if clock < 2 ^ 48 then do
    let v ← ((versionIntervals rows loc).filter (·.coversClock clock)).head?
    let version ← encodeVersion? snapshot loc v
    return populate version (Address.ofNat clock)
  else none

/-- On checked installed prefixes this selector produces an honest row for every legal
48-bit clock and probe key. Its returned word agrees with the actual paired Sail replay. -/
theorem installed_inputs {q : ℕ} [Fact q.Prime] [Fact (2 ^ 25 < q)] [Fact (2 ^ 17 < q)]
    {extra : List (Air.Flat.Component (ZMod q))} [Soundness.GroundingResources extra]
    {image : ProgramImage} {source : ExecutionSnapshot} {final : HostHintQueue.State (ZMod q)}
    {bankFinal : HostState} {channels : List (RawChannel (ZMod q))}
    [Soundness.HostFinalMemory.Registration image source extra Soundness.HostCallReceivers.available
      (Soundness.HostHintReadLocal.sourceResources source.host.io.hints) channels]
    {names : Soundness.HostFinalMemory.UniqueNames image source extra Soundness.HostCallReceivers.available
      (Soundness.HostHintReadLocal.sourceResources source.host.io.hints)}
    (witness : Soundness.HostHintQueueBoundary.SourceWitness image source final bankFinal extra channels names)
    (checked : witness.Constraints) (balanced : Soundness.HostHintQueueBoundary.Balanced witness) :
    ∃ (valid : image.Valid) (carrier : Soundness.HostHintReadCPU.GroundingCarrier witness),
      ∀ cut ≤ carrier.ordered.length, ∃ current, carrier.pairedTrajectory valid cut = some current ∧
        ∀ loc, ValidKey loc.busAddress → carrier.timeline.start cut < 2 ^ 48 →
          ∃ input, inputAt? source.sail.memorySnapshot (TraceGen.WriteObservations.physicalRows carrier)
              loc (carrier.timeline.start cut) = some input ∧ ProverAssumptions input ∧
            input.read.key = Address.ofNat loc.busAddress ∧ input.read.clock = Address.ofNat (carrier.timeline.start cut) ∧
            locContent current.sail loc = some input.read.value.toBitVec64 := by
  obtain ⟨valid, carrier, all⟩ := TraceGen.WriteObservations.installed_versions witness checked balanced
  refine ⟨valid, carrier, fun cut within => ?_⟩
  obtain ⟨current, reached, atClock⟩ := all cut within
  refine ⟨current, reached, fun loc key bound => ?_⟩
  have keyLt : loc.busAddress < 2 ^ 48 := by rcases key with eq | range; omega; exact range.2.1
  obtain ⟨v, selected, word, semantic⟩ := atClock loc keyLt
  have member : v ∈ ((versionIntervals (TraceGen.WriteObservations.physicalRows carrier) loc).filter
      (·.coversClock (carrier.timeline.start cut))) := selected ▸ List.mem_singleton_self _
  obtain ⟨version, encoded, honest, read⟩ := populate_covered source.sail.memorySnapshot loc v
    bound (List.mem_filter.mp member).2 key word
  refine ⟨_, by rw [inputAt?, ite_eq_left bound, selected]; simp [encoded], honest, ?_⟩
  rw [read]
  exact ⟨rfl, rfl, semantic⟩

/-- Soundness at an installed cut for any checked physical row whose interval pull is supplied
by a restriction of a genuine version. A second, forged word for that same clock is impossible.
Upstream registration and private ledger balance establish the supply used in this local join. -/
theorem installed_read_of_restriction {q : ℕ} [Fact q.Prime] [Fact (2 ^ 25 < q)] [Fact (2 ^ 17 < q)]
    {extra : List (Air.Flat.Component (ZMod q))} [Soundness.GroundingResources extra]
    {image : ProgramImage} {source : ExecutionSnapshot} {final : HostHintQueue.State (ZMod q)}
    {bankFinal : HostState} {channels : List (RawChannel (ZMod q))}
    [Soundness.HostFinalMemory.Registration image source extra Soundness.HostCallReceivers.available
      (Soundness.HostHintReadLocal.sourceResources source.host.io.hints) channels]
    {names : Soundness.HostFinalMemory.UniqueNames image source extra Soundness.HostCallReceivers.available
      (Soundness.HostHintReadLocal.sourceResources source.host.io.hints)}
    (witness : Soundness.HostHintQueueBoundary.SourceWitness image source final bankFinal extra channels names)
    (checked : witness.Constraints) (balanced : Soundness.HostHintQueueBoundary.Balanced witness) :
    ∃ (valid : image.Valid) (carrier : Soundness.HostHintReadCPU.GroundingCarrier witness),
      ∀ cut ≤ carrier.ordered.length, ∃ current, carrier.pairedTrajectory valid cut = some current ∧
        ∀ loc, loc.busAddress < 2 ^ 48 →
          ∀ v ∈ versionIntervals (TraceGen.WriteObservations.physicalRows carrier) loc, ∀ genuine,
          encodeVersion? source.sail.memorySnapshot loc v = some genuine →
          ∀ input : Inputs (ZMod q), Spec input → input.version.Restricts genuine →
            Address.toNat input.clock = carrier.timeline.start cut →
              input.read.key = Address.ofNat loc.busAddress ∧ locContent current.sail loc = some input.read.value.toBitVec64 := by
  obtain ⟨valid, carrier, all⟩ := TraceGen.WriteObservations.installed_versions witness checked balanced
  refine ⟨valid, carrier, fun cut within => ?_⟩
  obtain ⟨current, reached, atCut⟩ := all cut within
  refine ⟨current, reached, ?_⟩
  intro loc bound v member genuine encoded input row supply clock
  obtain ⟨address, covered, held⟩ := read_of_restriction encoded row supply
  obtain ⟨selected, unique, _, value⟩ := atCut loc bound
  rw [clock] at covered
  have chosen : v ∈ (versionIntervals (TraceGen.WriteObservations.physicalRows carrier) loc).filter
      (·.coversClock (carrier.timeline.start cut)) := List.mem_filter.mpr ⟨member, covered⟩
  rw [unique, List.mem_singleton] at chosen
  exact ⟨address, by rwa [held, chosen]⟩

end SP1Clean.WriteProbe
