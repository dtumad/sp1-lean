import SP1Clean.Model.SailWrap
import Mathlib.Tactic.IntervalCases

/-! # Sequential byte memory in the generated Sail model

The upstream ArchSem interpreter owns byte reads and writes. The generated RISC-V wrappers
convert between words and little-endian byte vectors. These lemmas connect that composition to
SP1's byte memory at its supported widths, retaining the generated access classification.
-/

namespace SP1Clean.SailMem
open Sail Sail.ArchSem LeanRV64D LeanRV64D.Functions

/-- A present byte is read without changing the sequential state. -/
lemma run_readByte (addr : ℕ) (d : BitVec 8) (s : SailState)
    (h : s.mem[addr]? = some d) :
    (Sail.ArchSem.readByte addr : ArchSemSeqM exception (BitVec 8)).run s = .ok d s := by
  have h' : s.mem.get? addr = some d := h
  show (match s.mem.get? addr with
      | some v => pure v | _ => throw (Sail.Error.OutOfMemoryRange addr) : ArchSemSeqM exception (BitVec 8)).run s
    = .ok d s
  rw [h']
  rfl

/-- Consume one successful step of the upstream sequential interpreter. -/
lemma run_seq_bind_eq {α β : Type} (x : ArchSemSeqM exception α) (f : α → ArchSemSeqM exception β) (s s' : SailState) (a : α)
    (h : x.run s = .ok a s') : (x >>= f).run s = (f a).run s' := by
  show EStateM.bind x f s = f a s'
  have h' : x s = EStateM.Result.ok a s' := h
  simp only [EStateM.bind, h']

/-- Transport a byte observation along equality of its base address. -/
lemma mem_at (s : SailState) {a b : ℕ} (hab : a = b) (k : ℕ) {d : BitVec 8}
    (h : s.mem[a + k]? = some d) : s.mem[b + k]? = some d := by
  subst hab; exact h

/-- Read one byte through the upstream sequential interpreter. -/
lemma run_readBytes_one (addr : ℕ) (b : BitVec 8) (s : SailState)
    (hb : s.mem[addr]? = some b) :
    (Sail.ArchSem.readBytes 1 addr : ArchSemSeqM exception (BitVec (8 * 1))).run s = .ok b s := by
  rw [show (Sail.ArchSem.readBytes 1 addr : ArchSemSeqM exception (BitVec (8 * 1)))
      = (Sail.ArchSem.readByte addr >>= fun b => pure b) from rfl,
    run_seq_bind_eq _ _ s s b (run_readByte addr b s hb)]
  rfl

/-- Helper: peel one concrete `readBytes (w+1)` step onto an already-reduced `readBytes w`. The
`readBytes` head is unfolded by `rfl` at a **concrete** width (symbolic `n+1` would not reduce, as the
`1`-pattern overlaps), and the two byte binds are peeled with `run_seq_bind_eq`, so the resulting proof
term never inlines the hashmap compute. -/
lemma run_readBytes_eight (addr : ℕ)
    (data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ : BitVec 8) (s : SailState)
    (hmem₀ : s.mem[addr]? = some data₀) (hmem₁ : s.mem[addr + 1]? = some data₁)
    (hmem₂ : s.mem[addr + 2]? = some data₂) (hmem₃ : s.mem[addr + 3]? = some data₃)
    (hmem₄ : s.mem[addr + 4]? = some data₄) (hmem₅ : s.mem[addr + 5]? = some data₅)
    (hmem₆ : s.mem[addr + 6]? = some data₆) (hmem₇ : s.mem[addr + 7]? = some data₇) :
    (Sail.ArchSem.readBytes 8 addr : ArchSemSeqM exception (BitVec (8 * 8))).run s
      = .ok (data₇ ++ data₆ ++ data₅ ++ data₄ ++ data₃ ++ data₂ ++ data₁ ++ data₀) s := by
  have e1 : (Sail.ArchSem.readBytes 1 (addr + 7) : ArchSemSeqM exception (BitVec (8 * 1))).run s
      = .ok (data₇) s := run_readBytes_one (addr + 7) data₇ s hmem₇
  have e2 : (Sail.ArchSem.readBytes 2 (addr + 6) : ArchSemSeqM exception (BitVec (8 * 2))).run s
      = .ok (data₇ ++ data₆) s := by
    rw [show (Sail.ArchSem.readBytes 2 (addr + 6) : ArchSemSeqM exception (BitVec (8 * 2)))
        = (Sail.ArchSem.readByte (addr + 6) >>= fun b =>
            Sail.ArchSem.readBytes 1 (addr + 7) >>= fun p => pure (p.append b)) from rfl,
      run_seq_bind_eq _ _ s s data₆ (run_readByte (addr + 6) data₆ s hmem₆),
      run_seq_bind_eq _ _ s s (data₇) e1]
    rfl
  have e3 : (Sail.ArchSem.readBytes 3 (addr + 5) : ArchSemSeqM exception (BitVec (8 * 3))).run s
      = .ok (data₇ ++ data₆ ++ data₅) s := by
    rw [show (Sail.ArchSem.readBytes 3 (addr + 5) : ArchSemSeqM exception (BitVec (8 * 3)))
        = (Sail.ArchSem.readByte (addr + 5) >>= fun b =>
            Sail.ArchSem.readBytes 2 (addr + 6) >>= fun p => pure (p.append b)) from rfl,
      run_seq_bind_eq _ _ s s data₅ (run_readByte (addr + 5) data₅ s hmem₅),
      run_seq_bind_eq _ _ s s (data₇ ++ data₆) e2]
    rfl
  have e4 : (Sail.ArchSem.readBytes 4 (addr + 4) : ArchSemSeqM exception (BitVec (8 * 4))).run s
      = .ok (data₇ ++ data₆ ++ data₅ ++ data₄) s := by
    rw [show (Sail.ArchSem.readBytes 4 (addr + 4) : ArchSemSeqM exception (BitVec (8 * 4)))
        = (Sail.ArchSem.readByte (addr + 4) >>= fun b =>
            Sail.ArchSem.readBytes 3 (addr + 5) >>= fun p => pure (p.append b)) from rfl,
      run_seq_bind_eq _ _ s s data₄ (run_readByte (addr + 4) data₄ s hmem₄),
      run_seq_bind_eq _ _ s s (data₇ ++ data₆ ++ data₅) e3]
    rfl
  have e5 : (Sail.ArchSem.readBytes 5 (addr + 3) : ArchSemSeqM exception (BitVec (8 * 5))).run s
      = .ok (data₇ ++ data₆ ++ data₅ ++ data₄ ++ data₃) s := by
    rw [show (Sail.ArchSem.readBytes 5 (addr + 3) : ArchSemSeqM exception (BitVec (8 * 5)))
        = (Sail.ArchSem.readByte (addr + 3) >>= fun b =>
            Sail.ArchSem.readBytes 4 (addr + 4) >>= fun p => pure (p.append b)) from rfl,
      run_seq_bind_eq _ _ s s data₃ (run_readByte (addr + 3) data₃ s hmem₃),
      run_seq_bind_eq _ _ s s (data₇ ++ data₆ ++ data₅ ++ data₄) e4]
    rfl
  have e6 : (Sail.ArchSem.readBytes 6 (addr + 2) : ArchSemSeqM exception (BitVec (8 * 6))).run s
      = .ok (data₇ ++ data₆ ++ data₅ ++ data₄ ++ data₃ ++ data₂) s := by
    rw [show (Sail.ArchSem.readBytes 6 (addr + 2) : ArchSemSeqM exception (BitVec (8 * 6)))
        = (Sail.ArchSem.readByte (addr + 2) >>= fun b =>
            Sail.ArchSem.readBytes 5 (addr + 3) >>= fun p => pure (p.append b)) from rfl,
      run_seq_bind_eq _ _ s s data₂ (run_readByte (addr + 2) data₂ s hmem₂),
      run_seq_bind_eq _ _ s s (data₇ ++ data₆ ++ data₅ ++ data₄ ++ data₃) e5]
    rfl
  have e7 : (Sail.ArchSem.readBytes 7 (addr + 1) : ArchSemSeqM exception (BitVec (8 * 7))).run s
      = .ok (data₇ ++ data₆ ++ data₅ ++ data₄ ++ data₃ ++ data₂ ++ data₁) s := by
    rw [show (Sail.ArchSem.readBytes 7 (addr + 1) : ArchSemSeqM exception (BitVec (8 * 7)))
        = (Sail.ArchSem.readByte (addr + 1) >>= fun b =>
            Sail.ArchSem.readBytes 6 (addr + 2) >>= fun p => pure (p.append b)) from rfl,
      run_seq_bind_eq _ _ s s data₁ (run_readByte (addr + 1) data₁ s hmem₁),
      run_seq_bind_eq _ _ s s (data₇ ++ data₆ ++ data₅ ++ data₄ ++ data₃ ++ data₂) e6]
    rfl
  rw [show (Sail.ArchSem.readBytes 8 addr : ArchSemSeqM exception (BitVec (8 * 8)))
      = (Sail.ArchSem.readByte addr >>= fun b =>
          Sail.ArchSem.readBytes 7 (addr + 1) >>= fun p => pure (p.append b)) from rfl,
    run_seq_bind_eq _ _ s s data₀ (run_readByte addr data₀ s hmem₀),
    run_seq_bind_eq _ _ s s (data₇ ++ data₆ ++ data₅ ++ data₄ ++ data₃ ++ data₂ ++ data₁) e7]
  rfl

/-- Read four bytes in little-endian order. -/
lemma run_readBytes_four (addr : ℕ) (data₀ data₁ data₂ data₃ : BitVec 8) (s : SailState)
    (hmem₀ : s.mem[addr]? = some data₀) (hmem₁ : s.mem[addr + 1]? = some data₁)
    (hmem₂ : s.mem[addr + 2]? = some data₂) (hmem₃ : s.mem[addr + 3]? = some data₃) :
    (Sail.ArchSem.readBytes 4 addr : ArchSemSeqM exception (BitVec (8 * 4))).run s
      = .ok (data₃ ++ data₂ ++ data₁ ++ data₀) s := by
  have e1 : (Sail.ArchSem.readBytes 1 (addr + 3) : ArchSemSeqM exception (BitVec (8 * 1))).run s
      = .ok (data₃) s := run_readBytes_one (addr + 3) data₃ s hmem₃
  have e2 : (Sail.ArchSem.readBytes 2 (addr + 2) : ArchSemSeqM exception (BitVec (8 * 2))).run s
      = .ok (data₃ ++ data₂) s := by
    rw [show (Sail.ArchSem.readBytes 2 (addr + 2) : ArchSemSeqM exception (BitVec (8 * 2)))
        = (Sail.ArchSem.readByte (addr + 2) >>= fun b =>
            Sail.ArchSem.readBytes 1 (addr + 3) >>= fun p => pure (p.append b)) from rfl,
      run_seq_bind_eq _ _ s s data₂ (run_readByte (addr + 2) data₂ s hmem₂),
      run_seq_bind_eq _ _ s s (data₃) e1]
    rfl
  have e3 : (Sail.ArchSem.readBytes 3 (addr + 1) : ArchSemSeqM exception (BitVec (8 * 3))).run s
      = .ok (data₃ ++ data₂ ++ data₁) s := by
    rw [show (Sail.ArchSem.readBytes 3 (addr + 1) : ArchSemSeqM exception (BitVec (8 * 3)))
        = (Sail.ArchSem.readByte (addr + 1) >>= fun b =>
            Sail.ArchSem.readBytes 2 (addr + 2) >>= fun p => pure (p.append b)) from rfl,
      run_seq_bind_eq _ _ s s data₁ (run_readByte (addr + 1) data₁ s hmem₁),
      run_seq_bind_eq _ _ s s (data₃ ++ data₂) e2]
    rfl
  rw [show (Sail.ArchSem.readBytes 4 addr : ArchSemSeqM exception (BitVec (8 * 4)))
      = (Sail.ArchSem.readByte addr >>= fun b =>
          Sail.ArchSem.readBytes 3 (addr + 1) >>= fun p => pure (p.append b)) from rfl,
    run_seq_bind_eq _ _ s s data₀ (run_readByte addr data₀ s hmem₀),
    run_seq_bind_eq _ _ s s (data₃ ++ data₂ ++ data₁) e3]
  rfl

/-- Two-byte `readBytes`. -/
lemma run_readBytes_two (addr : ℕ) (data₀ data₁ : BitVec 8) (s : SailState)
    (hmem₀ : s.mem[addr]? = some data₀) (hmem₁ : s.mem[addr + 1]? = some data₁) :
    (Sail.ArchSem.readBytes 2 addr : ArchSemSeqM exception (BitVec (8 * 2))).run s
      = .ok (data₁ ++ data₀) s := by
  have e1 : (Sail.ArchSem.readBytes 1 (addr + 1) : ArchSemSeqM exception (BitVec (8 * 1))).run s
      = .ok (data₁) s := run_readBytes_one (addr + 1) data₁ s hmem₁
  rw [show (Sail.ArchSem.readBytes 2 addr : ArchSemSeqM exception (BitVec (8 * 2)))
      = (Sail.ArchSem.readByte addr >>= fun b =>
          Sail.ArchSem.readBytes 1 (addr + 1) >>= fun p => pure (p.append b)) from rfl,
    run_seq_bind_eq _ _ s s data₀ (run_readByte addr data₀ s hmem₀),
    run_seq_bind_eq _ _ s s (data₁) e1]
  rfl

private theorem sail_getElem_ofFn {α : Type} {n : Nat} (f : Fin n → α) (i : Int)
    (h : i.toNat < n) : (Vector.ofFn f)[i]'h = f ⟨i.toNat, h⟩ := by
  exact Vector.getElem_ofFn h

private theorem from_bytes_read_one (data : BitVec (8 * 1)) :
    from_bytes_le (n := 1) (bitvec_to_vecbytes data) = data := by
  simp [from_bytes_le, bitvec_to_vecbytes, forIn, forIn', IntRange.forIn',
    IntRange.forIn'.loop, Membership.mem, Sail.BitVec.slice, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange', sail_getElem_ofFn]

private theorem from_bytes_read_two (data : BitVec (8 * 2)) :
    from_bytes_le (n := 2) (bitvec_to_vecbytes data) = data := by
  simp [from_bytes_le, bitvec_to_vecbytes, forIn, forIn', IntRange.forIn',
    IntRange.forIn'.loop, Membership.mem, Sail.BitVec.slice, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange', sail_getElem_ofFn]
  ext i
  interval_cases i <;> simp
private theorem from_bytes_read_four (data : BitVec (8 * 4)) :
    from_bytes_le (n := 4) (bitvec_to_vecbytes data) = data := by
  simp [from_bytes_le, bitvec_to_vecbytes, forIn, forIn', IntRange.forIn',
    IntRange.forIn'.loop, Membership.mem, Sail.BitVec.slice, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange', sail_getElem_ofFn]
  ext i
  interval_cases i <;> simp
private theorem from_bytes_read_eight (data : BitVec (8 * 8)) :
    from_bytes_le (n := 8) (bitvec_to_vecbytes data) = data := by
  simp [from_bytes_le, bitvec_to_vecbytes, forIn, forIn', IntRange.forIn',
    IntRange.forIn'.loop, Membership.mem, Sail.BitVec.slice, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange', sail_getElem_ofFn]
  ext i
  interval_cases i <;> simp

private theorem to_bytes_write_one (data : BitVec (8 * 1)) :
    vecbytes_to_bitvec (to_bytes_le (n := 1) data) = data := by
  simp [to_bytes_le, vecbytes_to_bitvec, forIn, forIn', IntRange.forIn',
    IntRange.forIn'.loop, Membership.mem, vectorInit, vectorUpdate,
    Sail.BitVec.extractLsb, BitVec.extractLsb, ← Vector.foldl_toList,
    Vector.set!_eq_setIfInBounds, List.set]
private theorem to_bytes_write_two (data : BitVec (8 * 2)) :
    vecbytes_to_bitvec (to_bytes_le (n := 2) data) = data := by
  simp [to_bytes_le, vecbytes_to_bitvec, forIn, forIn', IntRange.forIn',
    IntRange.forIn'.loop, Membership.mem, vectorInit, vectorUpdate,
    Sail.BitVec.extractLsb, BitVec.extractLsb, ← Vector.foldl_toList,
    Vector.set!_eq_setIfInBounds, List.replicate_succ, List.set]
  ext i
  interval_cases i <;> simp
private theorem to_bytes_write_four (data : BitVec (8 * 4)) :
    vecbytes_to_bitvec (to_bytes_le (n := 4) data) = data := by
  simp [to_bytes_le, vecbytes_to_bitvec, forIn, forIn', IntRange.forIn',
    IntRange.forIn'.loop, Membership.mem, vectorInit, vectorUpdate,
    Sail.BitVec.extractLsb, BitVec.extractLsb, ← Vector.foldl_toList,
    Vector.set!_eq_setIfInBounds, List.replicate_succ, List.set]
  ext i
  interval_cases i <;> simp
private theorem to_bytes_write_eight (data : BitVec (8 * 8)) :
    vecbytes_to_bitvec (to_bytes_le (n := 8) data) = data := by
  simp [to_bytes_le, vecbytes_to_bitvec, forIn, forIn', IntRange.forIn',
    IntRange.forIn'.loop, Membership.mem, vectorInit, vectorUpdate,
    Sail.BitVec.extractLsb, BitVec.extractLsb, ← Vector.foldl_toList,
    Vector.set!_eq_setIfInBounds, List.replicate_succ, List.set]
  ext i
  interval_cases i <;> simp

/-- The generated read request interprets to the upstream byte reader and its byte-vector
conversion. The result is left folded so symbolic memory maps never enter kernel computation. -/
private theorem run_read_ram_of_bytes (access : MemoryAccessType mem_payload)
    (paddr : BitVec 64) (width : Nat) (data : BitVec (8 * width)) (s : SailState)
    (h : (Sail.ArchSem.readBytes width paddr.toNat : ArchSemSeqM exception _).run s = .ok data s) :
    runSail (read_ram read_kind.Read_plain access (physaddr.Physaddr paddr) width false) s =
      .ok (from_bytes_le (bitvec_to_vecbytes data), ()) s := by
  unfold read_ram
  simp only [pure_bind, Bool.false_eq_true, ite_false]
  unfold runSail
  rw [interpretSailEffects_bind]
  simp only [LeanRV64D.ArchSem.sail_mem_read, PreSail.sail_mem_read, interpretSailEffects,
    FreeM.liftM, interpretInstructionEffect, Mem_request.toArchSem,
    show (0 != (0 : Nat)) = false from rfl, Function.comp_apply,
    Bool.false_eq_true, ite_false, pure_bind, bind_assoc]
  change ((Sail.ArchSem.readBytes width paddr.toNat : ArchSemSeqM exception _) >>= fun value =>
    pure (from_bytes_le (bitvec_to_vecbytes value), ())).run s = _
  rw [run_seq_bind_eq _ _ s s data h]
  rfl

/-- Read one byte through the generated RAM interface. -/
lemma run_read_ram_one (access : MemoryAccessType mem_payload) (paddr : BitVec 64) (data₀ : BitVec 8) (s : SailState)
    (hmem₀ : s.mem[paddr.toNat]? = some data₀) :
    runSail (read_ram read_kind.Read_plain access (physaddr.Physaddr paddr) 1 false
        : SailM (BitVec (8 * 1) × Unit)) s
      = .ok (data₀, ()) s := by
  have hrb := run_readBytes_one paddr.toNat data₀ s hmem₀
  simpa only [from_bytes_read_one] using
    run_read_ram_of_bytes access paddr 1 (data₀) s hrb

/-- Read two bytes through the generated RAM interface. -/
lemma run_read_ram_two (access : MemoryAccessType mem_payload) (paddr : BitVec 64) (data₀ data₁ : BitVec 8) (s : SailState)
    (hmem₀ : s.mem[paddr.toNat]? = some data₀) (hmem₁ : s.mem[paddr.toNat + 1]? = some data₁) :
    runSail (read_ram read_kind.Read_plain access (physaddr.Physaddr paddr) 2 false
        : SailM (BitVec (8 * 2) × Unit)) s
      = .ok (data₁ ++ data₀, ()) s := by
  have hrb := run_readBytes_two paddr.toNat data₀ data₁ s hmem₀ hmem₁
  simpa only [from_bytes_read_two] using
    run_read_ram_of_bytes access paddr 2 (data₁ ++ data₀) s hrb

/-- Read four bytes through the generated RAM interface. -/
lemma run_read_ram_four (access : MemoryAccessType mem_payload) (paddr : BitVec 64) (data₀ data₁ data₂ data₃ : BitVec 8) (s : SailState)
    (hmem₀ : s.mem[paddr.toNat]? = some data₀) (hmem₁ : s.mem[paddr.toNat + 1]? = some data₁)
    (hmem₂ : s.mem[paddr.toNat + 2]? = some data₂) (hmem₃ : s.mem[paddr.toNat + 3]? = some data₃) :
    runSail (read_ram read_kind.Read_plain access (physaddr.Physaddr paddr) 4 false
        : SailM (BitVec (8 * 4) × Unit)) s
      = .ok (data₃ ++ data₂ ++ data₁ ++ data₀, ()) s := by
  have hrb := run_readBytes_four paddr.toNat data₀ data₁ data₂ data₃ s hmem₀ hmem₁ hmem₂ hmem₃
  simpa only [from_bytes_read_four] using
    run_read_ram_of_bytes access paddr 4 (data₃ ++ data₂ ++ data₁ ++ data₀) s hrb

/-- Read eight bytes through the generated RAM interface. -/
lemma run_read_ram_eight (access : MemoryAccessType mem_payload) (paddr : BitVec 64)
    (data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ : BitVec 8) (s : SailState)
    (hmem₀ : s.mem[paddr.toNat]? = some data₀) (hmem₁ : s.mem[paddr.toNat + 1]? = some data₁)
    (hmem₂ : s.mem[paddr.toNat + 2]? = some data₂) (hmem₃ : s.mem[paddr.toNat + 3]? = some data₃)
    (hmem₄ : s.mem[paddr.toNat + 4]? = some data₄) (hmem₅ : s.mem[paddr.toNat + 5]? = some data₅)
    (hmem₆ : s.mem[paddr.toNat + 6]? = some data₆) (hmem₇ : s.mem[paddr.toNat + 7]? = some data₇) :
    runSail (read_ram read_kind.Read_plain access (physaddr.Physaddr paddr) 8 false
        : SailM (BitVec (8 * 8) × Unit)) s
      = .ok (data₇ ++ data₆ ++ data₅ ++ data₄ ++ data₃ ++ data₂ ++ data₁ ++ data₀, ()) s := by
  have hrb := run_readBytes_eight paddr.toNat data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ s hmem₀ hmem₁ hmem₂ hmem₃ hmem₄ hmem₅ hmem₆ hmem₇
  simpa only [from_bytes_read_eight] using
    run_read_ram_of_bytes access paddr 8 (data₇ ++ data₆ ++ data₅ ++ data₄ ++ data₃ ++ data₂ ++ data₁ ++ data₀) s hrb

/-- Interpret the generated write request using the upstream sequential byte writer. -/
theorem run_write_ram_eq (access : MemoryAccessType mem_payload) (paddr : BitVec 64) (width : Nat)
    (data : BitVec (8 * width)) (s : SailState) :
    runSail (write_ram write_kind.Write_plain access (physaddr.Physaddr paddr) width
      data ()) s =
    ((Sail.ArchSem.writeBytes paddr.toNat (vecbytes_to_bitvec (to_bytes_le data))
      : ArchSemSeqM exception PUnit) >>= fun _ => pure true).run s := by
  unfold write_ram
  simp only [pure_bind]
  unfold runSail
  rw [interpretSailEffects_bind]
  simp only [LeanRV64D.ArchSem.sail_mem_write, PreSail.sail_mem_write, interpretSailEffects,
    FreeM.liftM, interpretInstructionEffect, Mem_request.toArchSem,
    show (0 != (0 : Nat)) = false from rfl,
    Bool.false_eq_true, ite_false, bind_assoc]
  rfl

/-- Write one byte through the generated RAM interface. -/
lemma run_write_ram_one (access : MemoryAccessType mem_payload) (paddr : BitVec 64) (data : BitVec 8) (s : SailState) :
    runSail (write_ram write_kind.Write_plain access (physaddr.Physaddr paddr) 1 data ()) s
      = .ok true { s with mem := (s.mem.insert paddr.toNat (BitVec.ofNat 8 data.toNat)) } := by
  rw [run_write_ram_eq, to_bytes_write_one]
  simp [Sail.ArchSem.writeBytes, Sail.ArchSem.writeByte, List.ofFn, Fin.foldr, Fin.foldr.loop,
    BitVec.extractLsb',
    bind, Bind.bind, EStateM.bind, EStateM.pure, EStateM.run, pure, Pure.pure,
    modify, modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet,
    EStateM.modifyGet]

/-- Write two bytes through the generated RAM interface. -/
lemma run_write_ram_two (access : MemoryAccessType mem_payload) (paddr : BitVec 64) (data : BitVec 16) (s : SailState) :
    runSail (write_ram write_kind.Write_plain access (physaddr.Physaddr paddr) 2 data ()) s
      = .ok true { s with mem := ((s.mem.insert paddr.toNat (BitVec.ofNat 8 data.toNat)).insert
          (paddr.toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))) } := by
  rw [run_write_ram_eq, to_bytes_write_two]
  simp [Sail.ArchSem.writeBytes, Sail.ArchSem.writeByte, List.ofFn, Fin.foldr, Fin.foldr.loop,
    BitVec.extractLsb',
    bind, Bind.bind, EStateM.bind, EStateM.pure, EStateM.run, pure, Pure.pure,
    modify, modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet,
    EStateM.modifyGet]

/-- Write four bytes through the generated RAM interface. -/
lemma run_write_ram_four (access : MemoryAccessType mem_payload) (paddr : BitVec 64) (data : BitVec 32) (s : SailState) :
    runSail (write_ram write_kind.Write_plain access (physaddr.Physaddr paddr) 4 data ()) s
      = .ok true { s with mem := ((((s.mem.insert paddr.toNat
          (BitVec.ofNat 8 data.toNat)).insert
          (paddr.toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))).insert
          (paddr.toNat + 2) (BitVec.ofNat 8 (data.toNat >>> 16))).insert
          (paddr.toNat + 3) (BitVec.ofNat 8 (data.toNat >>> 24))) } := by
  rw [run_write_ram_eq, to_bytes_write_four]
  simp [Sail.ArchSem.writeBytes, Sail.ArchSem.writeByte, List.ofFn, Fin.foldr, Fin.foldr.loop,
    BitVec.extractLsb',
    bind, Bind.bind, EStateM.bind, EStateM.pure, EStateM.run, pure, Pure.pure,
    modify, modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet,
    EStateM.modifyGet]

/-- Write eight bytes through the generated RAM interface. -/
lemma run_write_ram_eight (access : MemoryAccessType mem_payload) (paddr : BitVec 64) (data : BitVec 64) (s : SailState) :
    runSail (write_ram write_kind.Write_plain access (physaddr.Physaddr paddr) 8 data ()) s
      = .ok true { s with mem := ((((((((s.mem.insert paddr.toNat
          (BitVec.ofNat 8 data.toNat)).insert
          (paddr.toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))).insert
          (paddr.toNat + 2) (BitVec.ofNat 8 (data.toNat >>> 16))).insert
          (paddr.toNat + 3) (BitVec.ofNat 8 (data.toNat >>> 24))).insert
          (paddr.toNat + 4) (BitVec.ofNat 8 (data.toNat >>> 32))).insert
          (paddr.toNat + 5) (BitVec.ofNat 8 (data.toNat >>> 40))).insert
          (paddr.toNat + 6) (BitVec.ofNat 8 (data.toNat >>> 48))).insert
          (paddr.toNat + 7) (BitVec.ofNat 8 (data.toNat >>> 56))) } := by
  rw [run_write_ram_eq, to_bytes_write_eight]
  simp [Sail.ArchSem.writeBytes, Sail.ArchSem.writeByte, List.ofFn, Fin.foldr, Fin.foldr.loop,
    BitVec.extractLsb',
    bind, Bind.bind, EStateM.bind, EStateM.pure, EStateM.run, pure, Pure.pure,
    modify, modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet,
    EStateM.modifyGet]

/-- Announcing a write has no state effect in the upstream sequential interpretation. -/
lemma run_write_ram_ea (access : MemoryAccessType mem_payload) (paddr : physaddr)
    (width : Nat) (s : SailState) :
    runSail (write_ram_ea write_kind.Write_plain access paddr width) s = .ok () s := by
  cases paddr
  rfl

end SP1Clean.SailMem
