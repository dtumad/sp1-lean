import SP1Clean.Proofs.Sail.Advance
import SP1Clean.Proofs.Sail.InstructionDecode
import SP1Clean.Semantics.Sail.SailExecuteFrame
import SP1Clean.FormalModel.ShardPreservation
import SP1Clean.FormalModel.Contracts.ResourceBoundary
import SP1Clean.Semantics.Execution.ReleaseLinks
import SP1Clean.Semantics.Resources.SixCallResources
import SP1Clean.Math.SP1Field

/-! # Two byte stores can exceed the native boundary payload only at the intermediate cut

The program stores one into writable zero RAM and then clears the same byte. An existing stdout
stream fills the incoming budget. It remains unchanged throughout and is measured symbolically.
-/

namespace SP1CleanTest.Core.BoundaryPayload
open SP1Clean SP1Clean.Semantics SP1Clean.Soundness.Target SP1Clean.Machine
open LeanRV64D LeanRV64D.Functions

private def image : ProgramImage := ⟨[(65536, 0x00110023), (65540, 0x00010023)], 65536, []⟩
private theorem valid : image.Valid := by decide
private abbrev program := image.toGuestProgram valid
private abbrev policy := FormalModel.Shard.policy SP1Prime image

private def host (length : ℕ) : HostState := { stdout := List.replicate length 0 }
private def source (length : ℕ) : ExecutionSnapshot :=
  ⟨{ registers := ((configuredState 65536).regs.insert .x1 1).insert .x2 70000, memory := image.initialMemory }, host length, 1⟩

private theorem source_pc (n : ℕ) : (source n).sail.realize.regs.get? Register.PC = some 65536 := by
  change (((configuredState 65536).regs.insert .x1 1).insert .x2 70000).get? Register.PC = some 65536
  rw [Std.ExtDHashMap.get?_insert, dite_eq_right (by decide), Std.ExtDHashMap.get?_insert, dite_eq_right (by decide)]
  exact cfgState_pc _

private theorem source_valid (length : ℕ) : ExecutionSourceValid image (source length) := by
  refine ⟨⟨valid, by decide, SailSnapshot.memorySnapshot_valid _, image.initialMemory_rom valid⟩, ?_,
    (by decide : 1 < 2 ^ 48), ?_⟩
  · exact Advance.SailConfigured.writeGPR (Advance.SailConfigured.writeGPR (cfgState_configured 65536) 1 1) 2 70000
  · change (((source length).sail.realize.regs.get? Register.PC).getD 0).toNat < 2 ^ 48
    rw [source_pc]
    decide

private theorem store_step {s : SailState} {pc : BitVec 64} {word : BitVec 32} {rs : BitVec 5}
    {value : BitVec 64} (length clk : ℕ) (cfg : SailConfigured s) (loaded : RomLoaded program s)
    (current : s.regs.get? Register.PC = some pc) (fetchWord : program.fetchWord pc = some word)
    (parsed : InstructionDecode.decode word = some (.STORE (0, .Regidx rs, .Regidx 2, 1)))
    (ordinary : word ≠ ECALL_ENC) (base : s.get_reg? 2 = some 70000) (data : s.get_reg? rs = some value) :
    ∃ next, ExecutionStep policy program ⟨s, host length, clk⟩ .ordinary ⟨next, host length, clk + 8⟩ ∧
      next.regs.get? Register.PC = some (pc + 4) ∧ next.get_reg? 2 = some 70000 ∧
      next.mem = s.mem.insert 70000 (value.extractLsb' 0 8) ∧ next.sailOutput = s.sailOutput := by
  have decode := SailDecode.instructionDecode_agrees _ _ parsed
  let effect (post : SailState) : Prop :=
    post.regs.get? Register.nextPC = some (pc + 4) ∧ post.get_reg? 2 = some 70000 ∧
      post.mem = s.mem.insert 70000 (value.extractLsb' 0 8) ∧ post.sailOutput = s.sailOutput
  obtain ⟨next, post, normal, _, result, committed, gprs, memory, output⟩ :=
    Advance.retire_of_observed_execute cfg loaded current fetchWord decode effect (by
      intro stage setup observed sameMemory sameOutput _ sequential
      have ran := Advance.execute_STORE_reaches 0 2 rs 70000 value stage setup.init setup.toValidMemConfig
        ((observed _).trans base) ((observed _).trans data) (by decide) (by decide)
      refine ⟨_, ran, configured_with_memory setup _, sequential, (observed _).trans base, ?_, sameOutput⟩
      exact congrArg (fun mem : Std.ExtHashMap ℕ (BitVec 8) => mem.insert 70000 (value.extractLsb' 0 8)) sameMemory)
  obtain ⟨nextPC, address, written, preserved⟩ := result
  refine ⟨next, .ordinary rfl ?_ normal ⟨pc, word, _, current, fetchWord, decode, ?_⟩,
    committed.trans nextPC, (gprs _).trans address, memory.trans written, output.trans preserved⟩
  · rintro ⟨pc', atPc, ecall⟩
    obtain rfl := Option.some.inj (atPc.symm.trans current)
    exact ordinary (Option.some.inj (fetchWord.symm.trans ecall))
  · apply (InstructionWrite.check_store_iff _ _ _ _ _ _ rfl).mpr
    refine ⟨70000, base, ?_⟩
    intro offset bounded
    have zero : offset = 0 := by change offset < 1 at bounded; omega
    subst offset
    decide

private abbrev firstMemory := image.initialMemory.write 70000 1
private abbrev finalMemory := firstMemory.write 70000 0

private theorem support_counts :
    (image.initialMemory.supportBelow NativeLayout.sailMemory.upper).card = 4 ∧
    (firstMemory.supportBelow NativeLayout.sailMemory.upper).card = 5 ∧
    (finalMemory.supportBelow NativeLayout.sailMemory.upper).card = 4 := by decide +kernel

private theorem payload (length : ℕ) : (host length).payloadCost = 117 + length := by
  simp [host, HostState.payloadCost, hintPayloadCost, bytePayloadCost]
  omega

/-- All resources of a finite endpoint with an unchanged carried output stream fit when its
canonical complete-boundary payload fits and the carried byte count is in range. -/
private theorem fits {snapshot : ExecutionSnapshot} {length : ℕ} (hostEq : snapshot.host = host length)
    (lengthBound : length ≤ SP1Prime - 1)
    (boundary : snapshot.resources .boundaryBytes ≤ SP1Prime - 1) :
    snapshot.resources.Fits (ResourceLimits.native SP1Prime) := by
  intro kind
  cases kind with
  | boundaryBytes => exact boundary
  | outputBytes => simpa [ExecutionSnapshot.resources, hostEq, host, ResourceLimits.ceiling, ResourceLimits.native] using lengthBound
  | events | ticks | readBytes | writeBytes | allocatedHints => exact Nat.zero_le _
  | liveHints | liveHintBytes | requests => simp [ExecutionSnapshot.resources, hostEq, host]

private theorem boundary_cost {snapshot : ExecutionSnapshot} (n count : ℕ)
    (hostEq : snapshot.host = host n) (empty : snapshot.sail.output = #[])
    (support : (snapshot.sail.memory.supportBelow NativeLayout.sailMemory.upper).card = count) :
    snapshot.resources .boundaryBytes = n + count + 125 := by
  simp [ExecutionSnapshot.resources, hostEq, empty, support, payload]
  omega

private theorem encoded {state : SailState} {pc : BitVec 64} {word : BitVec 32} {rs : BitVec 5}
    (current : state.regs.get? Register.PC = some pc) (fetched : program.fetchWord pc = some word)
    (parsed : InstructionDecode.decode word = some (.STORE (0, .Regidx rs, .Regidx 2, 1)))
    (base : state.get_reg? 2 = some 70000) : ordinaryEncodedAt program state :=
  ⟨pc, word, .STORE (0, .Regidx rs, .Regidx 2, 1), current, fetched,
    SailDecode.instructionDecode_agrees _ _ parsed, rfl, rfl, 70000, base, by decide⟩

private theorem store_link {state : SailState} {pc : BitVec 64} {word : BitVec 32} {rs : BitVec 5}
    (cfg : SailConfigured state) (current : state.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word)
    (parsed : InstructionDecode.decode word = some (.STORE (0, .Regidx rs, .Regidx 2, 1))) :
    ReleaseLinkAt program state :=
  (releaseLinkAt_iff current fetched ((SailDecode.instructionDecode_agrees _ _ parsed) state cfg)).mpr trivial

private theorem two_store_peak {program : GuestProgram} {policy : HostPolicy}
    {before mid after : ExecutionState} (first : ExecutionStep policy program before .ordinary mid)
    (second : ExecutionStep policy program mid .ordinary after)
    (a : before.resources .boundaryBytes = SP1Prime - 1) (b : mid.resources .boundaryBytes = SP1Prime)
    (c : after.resources .boundaryBytes = SP1Prime - 1) :
    executionResources policy program before [.ordinary, .ordinary] .boundaryBytes = SP1Prime := by
  rw [executionResources_cons first, executionResources_cons second]
  simp only [ResourceUsage.combine, ResourceKind.cumulative, Bool.false_eq_true, ↓reduceIte,
    a, b, c, executionResources_nil, ResourceUsage.zero]
  rfl

private structure Stores (n : ℕ) (mid target : ExecutionSnapshot) : Prop where
  first : ExecutionStep policy program (source n).realize .ordinary mid.realize
  second : ExecutionStep policy program mid.realize .ordinary target.realize
  encoded : ExecutionPath.Encoded policy program (source n).realize [.ordinary, .ordinary]
  links : ExecutionPath.ReleaseLinks policy program (source n).realize [.ordinary, .ordinary]
  clock : target.clock = 17
  pc : target.pc = 65544
  host : target.host = BoundaryPayload.host n
  middleBytes : mid.resources .boundaryBytes = n + 5 + 125
  targetBytes : target.resources .boundaryBytes = n + 4 + 125

private theorem stores (n : ℕ) : ∃ mid target, Stores n mid target := by
  have pc := source_pc n
  have base : (source n).sail.realize.get_reg? 2 = some 70000 := by
    change (((configuredState 65536).regs.insert .x1 1).insert .x2 70000).get? .x2 = some 70000
    exact Std.ExtDHashMap.get?_insert_self
  have data : (source n).sail.realize.get_reg? 1 = some 1 := by
    change (((configuredState 65536).regs.insert .x1 1).insert .x2 70000).get? .x1 = some 1
    rw [Std.ExtDHashMap.get?_insert, dite_eq_right (by decide), Std.ExtDHashMap.get?_insert_self]
  have initial := source_valid n
  obtain ⟨s1, first, pc1, base1, mem1, output1⟩ := store_step n 1 initial.configured initial.romLoaded pc
    (word := 0x00110023) rfl (rs := 1) rfl (by decide) base data
  let state1 : ExecutionState := ⟨s1, host n, 9⟩
  let mid := ExecutionSnapshot.capture state1 firstMemory
  have captured1 : mid.realize = state1 := by
    apply ExecutionSnapshot.realize_capture
    exact (image.initialMemory.toSailMemory_write _ 70000 1 (by decide)).trans mem1.symm
  have left : ExecutionPath policy program (source n).realize [.ordinary] state1 := .cons first (.nil _)
  have frame := left.frame valid (fun _ selected => selected) initial.configured initial.romLoaded
  obtain ⟨s2, second, pc2, _, mem2, output2⟩ := store_step n 9 frame.1 frame.2.1 pc1
    (word := 0x00010023) rfl (rs := 0) rfl (by decide) base1 (value := 0) (by simp [SailState.get_reg?])
  let state2 : ExecutionState := ⟨s2, host n, 17⟩
  let target := ExecutionSnapshot.capture state2 finalMemory
  have captured2 : target.realize = state2 := by
    apply ExecutionSnapshot.realize_capture
    rw [ByteMemory.toSailMemory_write _ _ _ _ (by decide : 70000 < 2 ^ 48)]
    have mem : firstMemory.toSailMemory (2 ^ 48) = s1.mem := congrArg (fun s : ExecutionState => s.sail.mem) captured1
    rw [mem]
    exact mem2.symm
  have pcFinal : target.pc = 65544 := by
    change (s2.regs.get? Register.PC).getD 0 = _
    rw [pc2]
    rfl
  refine ⟨mid, target, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, pcFinal, rfl, ?_, ?_⟩
  · rw [captured1]
    exact first
  · rw [captured1, captured2]
    exact second
  · apply (ExecutionPath.encoded_cons_iff first).mpr
    refine ⟨⟨rfl, fun _ => encoded pc (word := 0x00110023) rfl (rs := 1) rfl base⟩, ?_⟩
    exact (ExecutionPath.encoded_cons_iff second).mpr
      ⟨⟨(by decide : 9 % 8 = 1), fun _ => encoded pc1 (word := 0x00010023) rfl (rs := 0) rfl base1⟩, ExecutionPath.encoded_nil⟩
  · apply (ExecutionPath.releaseLinks_cons_iff first).mpr
    exact ⟨fun _ => store_link initial.configured pc (word := 0x00110023) rfl (rs := 1) rfl,
      ExecutionPath.releaseLinks_singleton.mpr
        (store_link frame.1 pc1 (word := 0x00010023) rfl (rs := 0) rfl)⟩
  · exact boundary_cost (snapshot := mid) n 5 rfl output1 support_counts.2.1
  · exact boundary_cost (snapshot := target) n 4 rfl (output2.trans output1) support_counts.2.2

/-- Both finite endpoints pass the native resource check, the released link condition holds,
and the nine other resource measures fit. Two normally retired, natively encoded byte stores
use one byte over the complete-boundary budget between endpoints that saturate its ceiling. -/
theorem endpoint_checks_miss_peak :
    ∃ (image : ProgramImage) (source middle target : ExecutionSnapshot),
      let limits := ResourceLimits.native SP1Prime
      let policy := FormalModel.Shard.policy SP1Prime image
      ExecutionSourceValid image source ∧
      ExecutionPath policy image.program source.realize [.ordinary] middle.realize ∧
      ExecutionPath policy image.program middle.realize [.ordinary] target.realize ∧
      ExecutionPath.Encoded policy image.program source.realize [.ordinary, .ordinary] ∧
      ExecutionPath.ReleaseLinks policy image.program source.realize [.ordinary, .ordinary] ∧
      ResourceBoundary.checkBounds limits source target = true ∧
      source.resources .boundaryBytes = SP1Prime - 1 ∧ middle.resources .boundaryBytes = SP1Prime ∧
      target.resources .boundaryBytes = SP1Prime - 1 ∧
      executionResources policy image.program source.realize [.ordinary, .ordinary] .boundaryBytes = SP1Prime ∧
      ∀ kind, kind ≠ .boundaryBytes →
        executionResources policy image.program source.realize [.ordinary, .ordinary] kind ≤ limits.ceiling kind := by
  obtain ⟨n, saturated⟩ : ∃ n : ℕ, n + 129 = SP1Prime - 1 := ⟨SP1Prime - 130, by decide⟩
  obtain ⟨mid, target, run⟩ := stores n
  have limit : n ≤ SP1Prime - 1 := by omega
  have overflow : n + 5 + 125 = SP1Prime := by omega
  have cost0 : (source n).resources .boundaryBytes = SP1Prime - 1 :=
    (boundary_cost (snapshot := source n) n 4 rfl rfl support_counts.1).trans saturated
  have cost1 := run.middleBytes.trans overflow
  have cost2 := run.targetBytes.trans saturated
  refine ⟨image, source n, mid, target, ?_⟩
  dsimp only
  rw [ProgramImage.program_eq image valid]
  refine ⟨source_valid n, .cons run.first (.nil _), .cons run.second (.nil _), run.encoded, run.links,
    (ResourceBoundary.checkBounds_iff ..).mpr ?_, cost0, cost1, cost2, ?_, ?_⟩
  · refine ⟨fits (length := n) rfl limit cost0.le, fits run.host limit cost2.le, ?_, ?_, ?_, ?_⟩
    · rw [run.clock]; exact (by decide : 1 ≤ 17)
    · rw [run.clock]; exact (by decide : 17 - 1 ≤ NativeLayout.maxShardTicks)
    · rw [run.clock]; decide
    · rw [run.pc]; decide
  · apply two_store_peak run.first run.second
    · exact (congrFun (source n).resources_realize .boundaryBytes).trans cost0
    · exact (congrFun mid.resources_realize .boundaryBytes).trans cost1
    · exact (congrFun target.resources_realize .boundaryBytes).trans cost2
  · have full : ExecutionPath policy program (source n).realize [.ordinary, .ordinary] target.realize :=
      .cons run.first (.cons run.second (.nil _))
    have allowed : ∀ e ∈ ([.ordinary, .ordinary] : List ExecutionEvent), SixCallProfile.event e := by
      intro e selected
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at selected
      subst e
      trivial
    have incoming := fits (snapshot := source n) (length := n) rfl limit cost0.le
    rw [← (source n).resources_realize] at incoming
    have ticks : executionResources policy program (source n).realize [.ordinary, .ordinary] .ticks ≤
        (ResourceLimits.native SP1Prime).ticks := by
      rw [full.resources_ticks]
      exact (by decide : 16 ≤ NativeLayout.maxShardTicks)
    have facts := SixCallProfile.resourceFacts full allowed incoming ticks
    exact fun kind checked => (facts.native_bounds kind checked).1

end SP1CleanTest.Core.BoundaryPayload
