module

public import SP1Clean.Semantics.Execution.EventExecution
public import SP1Clean.Semantics.ISA.SyscallCode

/-! # Complete syscall codes admitted by the registered host receivers

Both inventories admit the same six base handlers. The shared no-effect receiver in the
installed assembly additionally accepts VERIFY. Ordinary instructions are available in both.
-/

@[expose] public section

namespace SP1Clean.Semantics.HostReceiptProfile

/-- The six handlers available with the ENTER-only receipt. -/
def commonKinds : List SyscallKind :=
  [.halt, .enterUnconstrained, .commit, .commitDeferred, .hintLength, .hintRead]

/-- Full handler inventory selected for this registration. -/
def kinds (includeVerify : Bool) : List SyscallKind :=
  if includeVerify then .verifyProof :: commonKinds else commonKinds

/-- The complete syscall register word decodes to a registered handler. -/
def code (includeVerify : Bool) (word : BitVec 64) : Prop :=
  ∃ kind ∈ kinds includeVerify, SyscallKind.decode? word = some kind

/-- Every ordinary event is admitted. Every syscall must have its precise registered code. -/
def event (includeVerify : Bool) : Machine.ExecutionEvent → Prop
  | .ordinary => True
  | .syscall call => code includeVerify call.rawCode

/-- Common receipts are available under either registration. -/
theorem of_six (includeVerify : Bool) {word : BitVec 64} (admitted : code false word) :
    code includeVerify word := by
  obtain ⟨kind, listed, decoded⟩ := admitted
  refine ⟨kind, ?_, decoded⟩
  cases includeVerify
  · exact listed
  · exact List.mem_cons_of_mem _ listed

/-- Full-word decoding gives each admitted occurrence exactly one handler. -/
theorem code_iff_unique (includeVerify : Bool) (word : BitVec 64) :
    code includeVerify word ↔ ∃! kind, kind ∈ kinds includeVerify ∧ SyscallKind.decode? word = some kind := by
  constructor
  · rintro ⟨kind, member, decoded⟩
    exact ⟨kind, ⟨member, decoded⟩, fun _ other => Option.some.inj (other.2.symm.trans decoded)⟩
  · rintro ⟨kind, ⟨member, decoded⟩, _⟩
    exact ⟨kind, member, decoded⟩

/-- The production assembly admits exactly the seven supported calls other than WRITE. -/
theorem installed_code_iff (word : BitVec 64) :
    code true word ↔ ∃ kind, kind ≠ .write ∧ SyscallKind.decode? word = some kind := by
  have classified (kind : SyscallKind) : kind ∈ kinds true ↔ kind ≠ .write := by cases kind <;> decide
  exact exists_congr fun kind => and_congr_left' (classified kind)

/-- Neither receiver registration executes WRITE. -/
theorem ne_write {includeVerify : Bool} {word : BitVec 64} (allowed : code includeVerify word) :
    word ≠ SyscallKind.write.code := by
  obtain ⟨kind, listed, decoded⟩ := allowed
  rintro rfl
  have same : kind = .write := Option.some.inj decoded.symm
  subst kind
  cases includeVerify <;> simp [kinds, commonKinds] at listed

end SP1Clean.Semantics.HostReceiptProfile
