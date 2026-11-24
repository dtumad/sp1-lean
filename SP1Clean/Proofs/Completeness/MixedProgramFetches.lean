import SP1Clean.Proofs.Completeness.FixedProgramReads
import SP1Clean.Proofs.Completeness.MixedCompiledRows
import SP1Clean.Math.SP1Field

/-! # The verifier-fixed instruction fetched by each mixed execution row

The chronological compiler already records the exact PC of each ordinary instruction and
each ECALL. Each of these PCs selects its official instruction word from the committed ROM.
The resulting complete Program messages supply the counted fixed ROM provider.
-/

namespace SP1Clean.TraceGen.MixedProgramFetches

open Circuit Air.Flat Semantics Machine FormalModel.Shard Channels Soundness.Target

private abbrev F := ZMod SP1Prime

/-- Read the original instruction address retained by the compiler. -/
def pc : MixedCompiledRow → BitVec 64
  | .ordinary r => BitVec.ofNat 64 r.routed.pc
  | .syscall _ _ call => call.pc

/-- Fetch and decode the complete Program payload at a compiled instruction's PC. -/
def fetch? (image : ProgramImage) (row : MixedCompiledRow) : Option (ProgramMsg F) := do
  let word ← image.program.fetchWord (pc row)
  ProgramTable.message? (pc row, word)

private theorem fetch_entry (image : ProgramImage) (valid : image.Valid) (decodable : image.Decodable)
    {addr : BitVec 64} {word : BitVec 32} (fetched : image.program.fetchWord addr = some word) :
    ∃ m : ProgramMsg F, ProgramTable.message? (addr,word) = some m ∧ m ∈ image.programRows := by
  rw [image.program_eq valid, GuestProgram.fetchWord, Option.map_eq_some_iff] at fetched
  obtain ⟨r, found, contents⟩ := fetched
  have address : r.1 = addr := eq_of_beq (List.find?_some (p := fun r : BitVec 64 × BitVec 32 => r.1 == addr) found)
  have same : r = (addr,word) := Prod.ext address contents
  have listed : (addr,word) ∈ image.rom := same ▸ List.mem_of_find?_eq_some found
  have built : (ProgramTable.message? (p := SP1Prime) (addr,word)).isSome := by
    rw [ProgramTable.message?,Option.isSome_map,ProgramTable.row_isSome_iff]
    exact decodable _ listed
  obtain ⟨m,decoded⟩ := Option.isSome_iff_exists.mp built
  exact ⟨m,decoded,(image.mem_programRows m).mpr ⟨_,listed,decoded⟩⟩

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent} {limits : ResourceLimits}
    (run : AdmissibleExecution limits SP1Prime image source target events) {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)

include run routed in
/-- Both event families name a genuinely committed instruction. The ordinary proof uses the
row compiler's PC equality, and the host proof uses the ECALL actually dispatched at that PC. -/
theorem row_fetch (r : MixedCompiledRow) (member : r ∈ rows) :
    ∃ m, fetch? image r = some m ∧ m ∈ image.programRows := by
  obtain ⟨allRows, same, length⟩ := admissibleExecution_routeMixedRows run
  have length : rows.length = events.length := (Option.some.inj (routed.symm.trans same)) ▸ length
  obtain ⟨cut,atRow⟩ := List.getElem?_of_mem member
  have inside := (List.getElem?_eq_some_iff.mp atRow).1
  have inEvents : cut < events.length := inside.trans_eq length
  have atEvent := List.getElem?_eq_getElem inEvents
  cases e : events[cut] with
  | ordinary =>
    rw [e] at atEvent
    obtain ⟨_,_,_,_,_,view,compiled,projected,generated,eqRow⟩ := routeMixedRows?_at routed atEvent
    obtain rfl := Option.some.inj (atRow.symm.trans eqRow)
    have coords := (compileInstructionEvent?_coordinates generated).2
    have pcEq : pc (.ordinary compiled) = view.pc := by simp [pc, coords]
    have actual := (projectSP1Transition?_components projected).2.1
    obtain ⟨m,decoded,listed⟩ := fetch_entry image run.1.1.1.1 run.1.1.1.2.1 actual
    exact ⟨m,by simp [fetch?,pcEq,actual,decoded],listed⟩
  | syscall call =>
    rw [e] at atEvent
    obtain ⟨_,_,_,_,_,eqRow⟩ := routeMixedRows?_at routed atEvent
    obtain rfl := Option.some.inj (atRow.symm.trans eqRow)
    obtain ⟨current,_,_,_,_,step,_⟩ := admissibleExecution_syscall_from_prefix run atEvent
    cases step with
    | syscall ran =>
      obtain ⟨addr,exec,_,fetched,_,_,_,rfl⟩ := HostState.step_observations ran
      obtain ⟨m,decoded,listed⟩ := fetch_entry image run.1.1.1.1 run.1.1.1.2.1 fetched
      exact ⟨m,by simpa [fetch?,pc,HostExecution.toEvent,fetched] using decoded,listed⟩

/-- Select one word per actual row in chronological order, retaining repeated fetches. -/
def messages : List (ProgramMsg F) := rows.attach.map (fun r => (fetch? image r.val).get (by
  obtain ⟨m,found,_⟩ := row_fetch run routed r.val r.property
  exact Option.isSome_iff_exists.mpr ⟨m,found⟩))

/-- The chronological fetch sequence has exactly one occurrence per event. -/
theorem messages_length : (messages run routed).length = events.length := by
  obtain ⟨_,built,len⟩ := admissibleExecution_routeMixedRows run
  simpa only [messages, List.length_map, List.length_attach] using (congrArg List.length (Option.some.inj (routed.symm.trans built))).trans len

/-- Every payload the compiler counts came from a decoded original ROM entry. -/
theorem messages_covered (m : ProgramMsg F) (used : m ∈ messages run routed) : m ∈ image.programRows := by
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp used
  obtain ⟨v,found,listed⟩ := row_fetch run routed r.val r.property
  have same := Option.some.inj ((Option.some_get (Option.isSome_iff_exists.mpr ⟨v,found⟩)).trans found)
  exact same.symm ▸ listed

/-- The physical fixed Program table for the actual mixed rows and their fetch counts. -/
def table (data : ProverData F) : Table F :=
  let ms := messages run routed
  FixedProgramProvider.Preprocessed.countedTable image
    (FixedProgramProvider.Preprocessed.fetchIndices image run.1.1.1.1 ms (messages_covered run routed)) data

/-- Its fixed layout and counted Program ledger cover every genuine semantic fetch. -/
theorem funded (data : ProverData F) :
    let rom := table run routed data
    rom.Constraints ∧ rom.Guarantees ∧ rom.length = FixedProgramProvider.Preprocessed.height (p := SP1Prime) image ∧
      LogUpBalanced (rom.interactionsWith programChannel.toRaw ++ (messages run routed).map programChannel.pulledValue) :=
  FixedProgramProvider.Preprocessed.counted_fetches image run.1.1.1.1 _ (messages_covered run routed) data

end SP1Clean.TraceGen.MixedProgramFetches
