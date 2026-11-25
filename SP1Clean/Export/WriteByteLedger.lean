import SP1Clean.Export.WriteByteConsumers
import SP1Clean.Export.WriteByteProviderInstallation
import SP1Clean.Export.WriteObservationBuild

/-! # Byte demand and supply on the installed native ledger

The 23 original providers form the interval starting at supervisor position 32. Splitting
that interval out of the full ledger preserves every verifier, supervisor and observation
site, including padding and multiple occurrences of the same message.
-/

namespace SP1Clean.Export.WriteByteLedger
open Circuit Air.Flat Semantics Soundness Channels WriteSourceRegistry ByteProviderDemand
private abbrev F := ZMod SP1Prime
private abbrev bus := (byteChannel (p := SP1Prime)).toRaw
variable {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}
variable (w : EnsembleWitness (base image source target finish))

/-- All original physical reader tables in verifier order. -/
def clients : List (Table F) := w.tables.take 32 ++ w.tables.drop 55

/-- The 23 actual provider slots in the supervisor. -/
def providers : List (Table F) := (w.tables.drop 32).take 23

/-- Actual Byte pulls requested by the verifier, every original client and the native
observation extension. This list is the input to the provider tally. -/
noncomputable def demand (suffix : List (Table F)) : List (Interaction F) :=
  w.verifierInteractionsWith bus ++ (clients w ++ suffix).flatMap (·.interactionsWith bus)

/-- All nonprovider interactions lie on the selected channel, independently of any
assumption on the prover data. -/
theorem on_byte (suffix : List (Table F)) : ∀ i ∈ demand w suffix, i.channel = bus := by
  intro i seen
  rcases List.mem_append.mp seen with seen | seen
  · obtain ⟨a,member,rfl⟩ := List.mem_map.mp seen
    exact Operations.channel_eq_of_mem_interactionsWith member
  · obtain ⟨t,_,member⟩ := List.mem_flatMap.mp seen
    exact t.channel_eq_of_mem_interactionsWith member

/-- Restoring the literal provider window recovers the complete installed Byte ledger
up to permutation, including all registered suffix tables. -/
theorem split (suffix : List (Table F)) (registered : suffix.map Table.component = WriteObservationAssembly.tables source target) :
    ((WriteObservationAssembly.build w suffix registered).interactionsWith bus).Perm
      (demand w suffix ++ (providers w).flatMap (·.interactionsWith bus)) := by
  rw [WriteObservationAssembly.build_ledger,installSources_ledger _ _ (by
    intro eq; exact Bool.noConfusion (congrArg (fun c => c.name == "SP1Byte") eq))]
  have parts (ts : List (Table F)) :
      ts = ts.take 32 ++ ((ts.drop 32).take 23 ++ ts.drop 55) := by
    have tail := List.take_append_drop 23 (ts.drop 32)
    rw [List.drop_drop] at tail
    rw [show 55 = 32+23 by decide,tail,List.take_append_drop]
  have reorder {α : Type} (publicRows first supplied last observer : List α) :
      (((publicRows ++ (first ++ (supplied ++ last))) ++ observer)).Perm
        ((publicRows ++ ((first ++ last) ++ observer)) ++ supplied) := by
    simp only [List.append_assoc]
    simpa only [List.append_assoc] using
      ((List.perm_append_comm (l₁ := supplied) (l₂ := last ++ observer)).append_left first).append_left publicRows
  change ((w.verifierInteractionsWith bus ++ w.tables.flatMap (·.interactionsWith bus)) ++ _).Perm _
  conv_lhs => rw [parts w.tables]
  simp only [demand,clients,providers,List.flatMap_append]
  exact reorder ..

/-- The exact unweighted cost of the reader ledger counts disabled physical rows and
the complete public verifier as well as the observation suffix. -/
theorem demand_length (suffix : List (Table F)) :
    (demand w suffix).length = ((base image source target finish).verifierOperations.interactionsWith bus).length +
      ((clients w ++ suffix).map fun t => t.length * t.component.channelWidth bus).sum := by
  simp only [demand,EnsembleWitness.verifierInteractionsWith,Operations.interactionValuesWith,
    List.length_append,List.length_flatMap,List.length_map,Table.interactionsWith_length]

/-- A generated provider window closes the complete native Byte ledger against the
physical read tally and gives its exact occurrence count. -/
theorem funded (suffix : List (Table F)) (registered : suffix.map Table.component = WriteObservationAssembly.tables source target)
    (reads : WriteByteConsumers.Reads (demand w suffix)) (data : ProverData F)
    (installed : (providers w).flatMap (·.interactionsWith bus) =
      supply (requested (demand w suffix)) (readerCount (demand w suffix))
        (requested_servable _ (fun i member => (reads i member).2)) data) :
    let actual := (WriteObservationAssembly.build w suffix registered).interactionsWith bus
    LogUpBalanced actual ∧ actual.length = (demand w suffix).length +
      (all.map fun id => WitnessGeneration.demandHeight (keys (requested (demand w suffix)) id).length).sum := by
  have same := split w suffix registered
  rw [installed] at same
  have paid := funded_readers data (demand w suffix) (on_byte w suffix)
    (fun i seen => (reads i seen).1) (fun i seen => (reads i seen).2)
  exact ⟨fun msg => (balanceOf_perm same).trans (paid.1 msg),same.length_eq.trans paid.2⟩

end SP1Clean.Export.WriteByteLedger
