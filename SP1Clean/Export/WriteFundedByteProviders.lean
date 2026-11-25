import SP1Clean.Export.WriteGeneratedByteClients

/-! # Funding and installing the full native Byte bus

The original and observer tables determine their physical reads first. Those exact reads
then populate all 23 provider slots. Every provider keeps its generated cells through
canonical data replacement and native read-back decoration.
-/

namespace SP1Clean.Export.WriteFundedByteProviders
open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard Channels WriteSourceRegistry
open ByteProviderDemand WriteByteProviderInstallation
private abbrev F := ZMod SP1Prime
private abbrev bus := (byteChannel (p := SP1Prime)).toRaw
variable {image : ProgramImage} {initial final : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image initial final events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial initial.realize events = some rows)
    (finish : HostHintQueue.State F) (data : ProverData F) (hint : ProverHint F) (header : SP1PublicIO F)
    (packets : List WriteObservations.Packet)
    (reads : List (Interaction F)) (serve : ∀ i ∈ reads, i.mult ≠ 0 → ByteServable (messageKey i.msg))

private abbrev bank := ofReaders image initial final finish data reads serve
private noncomputable abbrev supervisor := WriteGeneratedByteClients.supervisor run routed finish data hint header packets (bank finish data reads serve)
private abbrev generated := ByteProviderDemand.table (requested reads) (readerCount reads) (requested_servable reads serve) data

private theorem cells (pos : Fin 23) :
    ((supervisor run routed finish data hint header packets reads serve).tables.map Table.table)[32 + pos.val]? = some (generated data reads serve (provider pos)).table := by
  let rest := bank (image := image) (initial := initial) (final := final) finish data reads serve
  let controls := WriteMixedControlTables.install run routed data rest
  let fixed := WriteMixedFixedResources.install run routed data hint packets controls
  let host := WriteMixedHostTables.install run.1 data fixed
  let i : Fin ((base image initial final finish).tables.drop 6).length :=
    ⟨26 + pos.val,by rw [List.length_drop,base_length]; omega⟩
  have eq : 6 + i.val = 32 + pos.val := by dsimp only [i]; omega
  have ⟨notSource,notHost,notFixed,notControl⟩ := window image initial final finish pos
  rw [← eq] at notSource notHost notFixed notControl
  have old := WriteMixedSourceTables.remaining_arrays image initial final finish rows (HintReadTransfers.history image initial events)
    (WriteMixedSourceTables.heights run routed) data hint host (MixedMemoryHistory.stream image initial events rows)
    (WriteBoundaryBuild.demandKeys events packets) (MixedMemoryHistory.canonical run.1 routed) header i notSource
  have paid : (host i notSource).1 = generated data reads serve (provider pos) := by
    dsimp only [host,WriteMixedHostTables.install]
    split
    · dsimp only [fixed,WriteMixedFixedResources.install]
      split
      · dsimp only [controls,WriteMixedControlTables.install]
        split
        · exact remaining_at image initial final finish _ _ _ data pos i eq _ _ _ _
        · rename_i _ h; rw [notControl] at h; cases h
      · rename_i _ h; rw [notFixed] at h; cases h
    · rename_i _ h; rw [notHost] at h; cases h
  rwa [paid,eq] at old

attribute [local irreducible] base WriteGeneratedByteClients.supervisor

/-- Every physical original provider has the ledger of its exact funded bucket. -/
theorem payout :
    let w := supervisor run routed finish data hint header packets reads serve
    (WriteByteLedger.providers w).flatMap (·.interactionsWith bus) =
      supply (requested reads) (readerCount reads) (requested_servable reads serve) data := by
  intro w
  have size : w.tables.length = 98 := w.same_length.symm.trans (base_length ..)
  apply congrArg List.flatten
  change ((WriteByteLedger.providers w).map (·.interactionsWith bus)) =
    ((all.map (generated data reads serve)).map (·.interactionsWith bus))
  apply List.ext_getElem
  · simp only [WriteByteLedger.providers,List.length_map,List.length_take,List.length_drop,size]
    decide
  intro j hj _
  let pos : Fin 23 := ⟨j,by simp only [WriteByteLedger.providers,List.length_map,List.length_take,List.length_drop,size] at hj; omega⟩
  let k := 32 + pos.val
  have inside : k < w.tables.length := by rw [size]; dsimp only [k]; omega
  let actual := w.tables[k]'inside
  have located : w.tables[k]? = some actual := List.getElem?_eq_getElem inside
  have comp := congrArg (fun cs : List (Component F) => cs[k]?) w.tables_map_component
  rw [List.getElem?_map,located,Option.map_some,registered image initial final finish pos] at comp
  have rowsAt := cells run routed finish data hint header packets reads serve pos
  change (w.tables.map Table.table)[k]? = _ at rowsAt
  rw [List.getElem?_map,located,Option.map_some] at rowsAt
  simp only [WriteByteLedger.providers,List.getElem_map,List.getElem_take,List.getElem_drop]
  change actual.interactionsWith bus = (generated data reads serve (provider pos)).interactionsWith bus
  apply Table.interactionsWith_eq_of_rows _ _ _ (Option.some.inj rowsAt)
  have original : (generated data reads serve (provider pos)).component = ByteProviderDemand.component (provider pos) := rfl
  rw [Option.some.inj comp,original]

/-- The actual installed Byte ledger balances at every message. Its exact unweighted count
includes all 12 public sites, all 75 client tables, the observer suffix and each padded provider bucket. -/
theorem full (limbs : header.LimbBounds) (suffix : List (Table F)) (reg : suffix.map Table.component = WriteObservationAssembly.tables initial final)
    (observer : WriteByteConsumers.Reads (suffix.flatMap (·.interactionsWith bus))) :
    let input := WriteGeneratedByteClients.demand run routed finish data hint header packets suffix
    let typed := WriteGeneratedByteClients.reads run routed finish data hint header packets limbs suffix observer
    let w := supervisor run routed finish data hint header packets input (fun i mem => (typed i mem).2)
    let ledger := (WriteObservationAssembly.build w suffix reg).interactionsWith bus
    LogUpBalanced ledger ∧ ledger.length = input.length + (all.map fun id => WitnessGeneration.demandHeight (keys (requested input) id).length).sum := by
  intro input typed w ledger
  let servable := fun i (mem : i ∈ input) => (typed i mem).2
  have actual : WriteByteLedger.demand w suffix = input := WriteGeneratedByteClients.demand_eq run routed finish data hint header packets _ suffix
  have same := WriteByteLedger.split w suffix reg
  rw [actual,payout run routed finish data hint header packets input servable] at same
  have onBus := WriteByteLedger.on_byte w suffix
  rw [actual] at onBus
  have signed := funded_readers data input onBus (fun i mem => (typed i mem).1) servable
  exact ⟨fun msg => (balanceOf_perm same).trans (signed.1 msg),same.length_eq.trans signed.2⟩

end SP1Clean.Export.WriteFundedByteProviders
