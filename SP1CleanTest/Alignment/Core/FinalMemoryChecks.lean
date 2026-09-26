import SP1Clean.Soundness.FinalMemoryCheckSoundness
import SP1Clean.Soundness.FinishedChannels
import SP1Clean.Model.SP1Field
import ToClean.Air.EnsembleExport

/-! # Complete outgoing Memory assembly regression

The fixture executes the installed verifier, finalizers, target validators, and actual Byte/Range
providers. Every channel is registered and balanced, including Memory and final ordering. The
auxiliary Memory provider supplies zero-clock records: this checks the boundary subsystem, not
an execution from the source snapshot. Mixed execution grounding authenticates those records.
-/

namespace SP1CleanTest.Alignment.Core.FinalMemoryChecks

open Circuit Air.Flat SP1Clean SP1Clean.Soundness SP1Clean.Model.Core

private abbrev Fp := ZMod SP1Prime
private abbrev Row := ℕ × List Fp
private abbrev Ledger := List (String × List Fp × Fp)

private def source : MemorySnapshot := ⟨Vector.replicate 32 0, ⟨[]⟩⟩
private def target : MemorySnapshot :=
  ⟨source.registers.set 1 123, ⟨[(65536, 9), (65543, 17)]⟩⟩

private def auxiliary : List (Component Fp) :=
  ⟨MemoryProviderChip.circuit⟩ :: (sp1ProviderTables (p := SP1Prime)).take 23

private def assembly (target : MemorySnapshot) :=
  Soundness.FinalMemoryChecks.ensemble source target auxiliary []

/-- The real provider family satisfies the static interface used by the soundness theorem. -/
theorem resourceInterface : Soundness.FinalMemoryChecks.Interface auxiliary := by
  have members (component : Component Fp) (member : component ∈ auxiliary) :
      component ∈ (sp1Ensemble (p := SP1Prime)).allTables := by
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    rcases List.mem_cons.mp member with rfl | provider
    · rw [sp1ProviderTables_explicit]
      simp
    · exact List.mem_of_mem_take provider
  have silence : auxiliary.all (fun component =>
      !(component.circuit.channels.map RawChannel.name).contains "SP1FinalRegisterValue" &&
      !(component.circuit.channels.map RawChannel.name).contains "SP1FinalRamValue" &&
      !(component.circuit.channels.map RawChannel.name).contains "SP1FinalMemoryChange") = true := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro component member env checked
    exact sp1_component_finished_requirements component (members component member)
      Channels.byteChannel.toRaw (by simp [Channels.byteChannel, Channels.stateChannel,
        Channels.memoryChannel, Channel.toRaw]) env checked
  · intro ram component member used
    have silent := List.all_eq_true.mp silence component member
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    cases ram <;> simp only [FinalMemoryValue.channel, Channel.toRaw, Bool.false_eq_true, ↓reduceIte] at present <;>
      rw [present] at silent <;> simp at silent
  · intro component member used
    have silent := List.all_eq_true.mp silence component member
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    change (component.circuit.channels.map RawChannel.name).contains "SP1FinalMemoryChange" = true at present
    rw [present] at silent
    simp at silent

private def word (value : ℕ) : Word Fp := Target.bitVecToWord (BitVec.ofNat 64 value)

private def record (address value : ℕ) : Channels.MemoryMsg Fp :=
  ⟨0, 0, (word address)[0], (word address)[1], (word address)[2], word value⟩

private def registers := record 1 123
private def ram := record 65536 (target.memory.readWord 65536).toNat

private def finalizer (index previous : ℕ) (record : Channels.MemoryMsg Fp) : Row :=
  (index, (toElements (OrderedMemoryProvider.populate record previous
    (Word.toNat (MemoryBoundary.address record)))).toList)

private def memory (record : Channels.MemoryMsg Fp) : Row :=
  (5, (toElements (⟨record.clk_high, record.clk_low, record.addr0, record.addr1,
    record.addr2, record.value, 1⟩ : MemoryProviderChip.Inputs Fp)).toList)

private def registerCheck (record : Channels.MemoryMsg Fp) (selected : Fp) : Row :=
  (3, (toElements (⟨record, selected⟩ : FinalRegisterCheck.Inputs Fp)).toList)

private def ramCheck (record : Channels.MemoryMsg Fp) (selected : Fp) : Row :=
  (4, (toElements (⟨⟨record, InitialMemoryRead.populate target.memory
    (Word.toNat (MemoryBoundary.address record))⟩, selected⟩ : FinalRamCheck.Inputs Fp)).toList)

private def terminal (previous : ℕ) : Row :=
  (2, (toElements (OrderedBoundaryEnd.populate (word previous)
    (OrderedMemoryEnsemble.endKey (p := SP1Prime)))).toList)

private def rows : List Row :=
  [finalizer 0 0 registers, finalizer 1 2 ram, terminal 65537,
    registerCheck registers 1, ramCheck ram 1, memory registers, memory ram]

private def evaluate (target : MemorySnapshot) (component : Component Fp) (inputs : List Fp) :
    Bool × Ledger :=
  let program := component.circuit.main component.rowInputVar
  let env := (program.proverEnvironment (ProverHint.empty Fp) inputs).toEnvironment
  let operations := (program.operations component.rowOffset).toFlat
  let registers := FiniteLookup.ofStatic (target.registerTable (p := SP1Prime))
  let memory := FiniteLookup.ofStatic (target.memory.fixedTable (p := SP1Prime) (2 ^ 48))
  let fixed := [{ registers with table := { registers.table with name := "sp1.native.target_registers" } },
    { memory with table := { memory.table with name := "sp1.native.target_memory" } }]
  let valid := inputs.length == component.rowOffset && operations.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup lookup => fixed.any fun table => lookup.table.name == table.table.name &&
        table.rows.any (fun row => row.toArray == (lookup.entry.map env).toArray)
    | .witness .. | .interact .. => true
  (valid, (FlatOperation.interactions operations).map fun interaction =>
    (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult))

private def evaluateRow (target : MemorySnapshot) (row : Row) : Bool × Ledger :=
  match (assembly target).tables[row.1]? with
  | none => (false, [])
  | some component => evaluate target component row.2

private def byteProvider (entry : String × List Fp × Fp) : Option Row :=
  if entry.1 != "SP1Byte" || entry.2.2 == 0 then none else
  match entry.2.1 with
  | [opcode, a, b, c] =>
    if opcode == 3 then some (6, [b, c, -entry.2.2])
    else if opcode == 4 then some (11, [b, c, -entry.2.2])
    else if opcode == 5 then some (7, [b, -entry.2.2])
    else if opcode == 6 && b.val < 17 then some (12 + b.val, [a, -entry.2.2])
    else some (29, [])
  | _ => some (29, [])

private def check (target : MemorySnapshot) (rows : List Row) (supplyBytes : Bool := true) : Bool :=
  let initial := evaluate target (assembly target).verifierTable [] :: rows.map (evaluateRow target)
  let providers := if supplyBytes then (initial.flatMap Prod.snd).filterMap byteProvider else []
  let evaluated := initial ++ providers.map (evaluateRow target)
  let ledger := evaluated.flatMap Prod.snd
  evaluated.all Prod.fst && decide (ledger.length < SP1Prime) &&
    ledger.all fun (name, message, _) =>
      ((assembly target).channels.map RawChannel.name).contains name &&
        ((ledger.filter fun entry => entry.1 == name && entry.2.1 == message).map (·.2.2)).sum == 0

/-- Changed register and sparse RAM pass the complete installed boundary AIR. -/
theorem completeAcceptance : check target rows = true := by native_decide

/-- Empty identity inventories still retain the canonical ordering terminal and its Byte closure. -/
theorem emptyIdentity : check source [terminal 0] = true := by native_decide

/-- Complete-record matching, Boolean selection, target coverage, Byte closure, and final order
are all enforced by the same accepted witness. -/
theorem rejectsMutations :
    [check target (rows.filter (fun row => row.1 != 4)),
     check target (rows ++ [ramCheck ram 1]),
     check target (rows.map fun row => if row.1 == 3 then registerCheck registers 0 else row),
     check target (rows.map fun row => if row.1 == 3 then registerCheck registers 2 else row),
     check target (rows.map fun row => if row.1 == 4 then ramCheck { ram with clk_low := 1 } 1 else row),
     check { target with registers := target.registers.set 31 17 } rows,
     check { target with memory := target.memory.write 65544 1 } rows,
     check { target with memory := target.memory.write 65543 18 } rows,
     check target rows false,
     check target (rows.filter (fun row => row.1 != 2)),
     check target (rows.filter (fun row => row.1 != 5))] = List.replicate 11 false := by
  native_decide

end SP1CleanTest.Alignment.Core.FinalMemoryChecks
