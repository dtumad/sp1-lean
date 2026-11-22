import SP1Clean.Export.InstalledAssembly

/-! # Composing raw native shard statements

An ordered list supplies each local verifier input and its physical table heights. Each shard
is checked with its own limits. Matching complete snapshots connect the resulting paths, and
one immutable commitment statement authenticates declarations throughout the run.
-/

namespace SP1Clean.Export.InstalledAssembly

open Semantics Machine FormalModel.Shard

/-- A local input to the installed verifier, including its ordered physical heights. -/
structure LocalStatement where
  /-- Assembly for this shard's image, limits and complete boundary states. -/
  context : Context
  /-- Public input checked by this shard's verifier. -/
  header : SP1PublicIO Fp
  /-- Physical height in the installed order for each table. -/
  heights : List ℕ

/-- Check each raw statement and join complete boundaries. Distinct finite representations
of the same Sail memory can meet at a boundary. -/
def AcceptedChain (image : ProgramImage) (commitments : CommitmentStatement)
    (source : ExecutionSnapshot) : List LocalStatement → ExecutionSnapshot → Prop
  | [], target => source.equivalent target = true
  | shard :: rest, target =>
    shard.context.image = image ∧ shard.context.commitments = commitments ∧
      source.equivalent shard.context.source = true ∧
      (assembly shard.context).Statement .logUp shard.header shard.heights ∧
      AcceptedChain image commitments shard.context.target rest target

/-- Acceptance of any finite chain gives one execution over the same program and commitment
statement. The concatenated trace can exceed an individual shard's capacity. -/
theorem AcceptedChain.soundness {image : ProgramImage} {commitments : CommitmentStatement}
    {source target : ExecutionSnapshot} {shards : List LocalStatement}
    (accepted : AcceptedChain image commitments source shards target) :
    ∃ events : List ExecutionEvent, (sp1Machine SP1Prime image).Trace source.realize events target.realize ∧
      commitments.Matches events ∧ ∀ event ∈ events, HostReceiptProfile.event true event := by
  induction shards generalizing source with
  | nil =>
    have same := (ExecutionSnapshot.equivalent_iff source target).mp accepted
    exact ⟨[], trace_iff_executionPath.mpr (ExecutionPath.nil_iff.mpr same.symm),
      commitments.matches_nil, fun _ member => False.elim (List.not_mem_nil member)⟩
  | cons shard rest ih =>
    obtain ⟨imageEq, commitmentsEq, joined, raw, remaining⟩ := accepted
    obtain ⟨xs, left, declared, handlers⟩ := InstalledAssembly.soundness shard.context raw
    obtain ⟨ys, right, tailDeclared, tailHandlers⟩ := ih remaining
    rw [imageEq, ← (ExecutionSnapshot.equivalent_iff ..).mp joined] at left
    rw [commitmentsEq] at declared
    refine ⟨xs ++ ys, trace_iff_executionPath.mpr
      ((trace_iff_executionPath.mp left).append (trace_iff_executionPath.mp right)),
      (commitments.matches_append xs ys).mpr ⟨declared, tailDeclared⟩, fun event member => ?_⟩
    exact (List.mem_append.mp member).elim (handlers event) (tailHandlers event)

/-- A chain beginning at the canonical boot snapshot and ending in a stopped host supplies
a boot-to-HALT run of the checked image. Its final event is the HALT carrying the exit code. -/
theorem AcceptedChain.boot_to_halt {image : ProgramImage} {commitments : CommitmentStatement}
    {input : HostInputs} {target : ExecutionSnapshot} {shards : List LocalStatement} {exit : BitVec 32}
    (accepted : AcceptedChain image commitments (image.executionBootSnapshot input) shards target)
    (stopped : target.host.exitCode = some exit) :
    ∃ (valid : image.Valid) (beforeHalt : List ExecutionEvent) (halt : CoreSyscallEvent),
      let events := beforeHalt ++ [.syscall halt]
      BootToHalt (policy SP1Prime image) image valid input events.length target.realize exit ∧
        (sp1Machine SP1Prime image).Trace (image.executionBoot input) events target.realize ∧
        halt.rawCode = 0 ∧ halt.arg1.setWidth 32 = exit ∧ commitments.Matches events ∧
        ∀ event ∈ events, HostReceiptProfile.event true event := by
  obtain ⟨events, trace, declared, handlers⟩ := accepted.soundness
  have path := trace_iff_executionPath.mp trace
  rw [image.executionBootSnapshot_realize] at path
  obtain ⟨beforeHalt, _, halt, rfl, _, _, code, operand⟩ :=
    path.ends_in_halt (image.executionBoot_running input) stopped
  have valid : image.Valid := by
    cases shards with
    | nil =>
      have same := (ExecutionSnapshot.equivalent_iff ..).mp accepted
      rw [image.executionBootSnapshot_realize] at same
      have running := image.executionBoot_running input
      rw [same] at running
      cases running.symm.trans stopped
    | cons first rest =>
      obtain ⟨sameImage, _, _, raw, _⟩ := accepted
      obtain ⟨sourceValid, _⟩ := execution_of_statement first.context raw
      exact sameImage ▸ sourceValid.1.1
  refine ⟨valid, beforeHalt, halt, ⟨⟨_, rfl, ?_⟩, stopped⟩, trace_iff_executionPath.mpr path,
    code, operand, declared, handlers⟩
  rwa [← image.program_eq valid]

end SP1Clean.Export.InstalledAssembly
