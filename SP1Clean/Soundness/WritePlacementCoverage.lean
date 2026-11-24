import SP1Clean.Native.Operations.WriteGroup
import SP1Clean.Soundness.Walk
import SP1Clean.Math.SP1Field

/-! # Covering every byte position in a physical placement walk -/

namespace SP1Clean.WriteEffects
open Soundness
private abbrev F := ZMod SP1Prime

/-- Integer movements of the two cursors as derived from a genuine plan, aligned
authenticated guest key, and the checked field constraints. -/
structure Group.Movements (g : Group F) : Prop where
  /-- Number of selected lanes fits this guest word. -/
  fits : g.plan.first.val + g.plan.size.val ≤ 8
  /-- The first selected guest byte follows the address at the previous cursor. -/
  first : Address.toNat g.octets.key + g.plan.first.val = Address.toNat g.previous.address + 1
  /-- The guest address advances by exactly the number of selected lanes. -/
  address : Address.toNat g.next.address = Address.toNat g.previous.address + g.plan.size.val
  /-- The logical byte position advances by the same count. -/
  position : Address.toNat g.next.position = Address.toNat g.previous.position + g.plan.size.val

/-- Nonempty rows advance the guest cursor without wrapping even at a limb boundary. -/
theorem Group.movements {g : Group F} (v : g.Valid) (bounded : Address.Bounded g.octets.key)
    {first size offset : Nat} (plan : g.plan = .ofNat first size offset) (fits : first + size ≤ 8) (live : g.plan.nonempty = 1) :
    g.Movements := by
  have modulus : 8 < SP1Prime := by decide
  have positive : 0 < size := by
    by_contra! h
    have zero : size = 0 := Nat.eq_zero_of_le_zero h
    exact zero_ne_one (by simpa only [plan,SlicePlan.ofNat,zero,ite_true] using live : (0 : F) = 1)
  have f : g.plan.first.val = first := by rw [plan]; exact ZMod.val_natCast_of_lt (by omega)
  have s : g.plan.size.val = size := by rw [plan]; exact ZMod.val_natCast_of_lt (by omega)
  have a := v.1.2.2.2.2.1.2.2.2
  have b := v.1.2.2.2.2.2.1.2.2.2
  have one : Address.toNat (#v[1,0,0] : fields 3 F) = 1 := by decide
  change Address.toNat (Address.offset g.octets.key g.plan.first) = Address.toNat g.previous.address + _ at a
  rw [one,plan] at a
  change Address.toNat (Address.offset g.octets.key (first : F)) = _ at a
  rw [Address.toNat_offset _ bounded first (by omega)] at a
  change Address.toNat g.next.position = Address.toNat g.previous.position + Address.toNat (#v[g.plan.size,0,0] : fields 3 F) at b
  have sz : Address.toNat (#v[g.plan.size,0,0] : fields 3 F) = size := by simp [Address.toNat,circuit_norm,s]
  refine ⟨by omega,by omega,?_,by rwa [sz,← s] at b⟩
  change Address.toNat (Address.offset g.octets.key g.plan.last) = _
  rw [s,plan]
  change Address.toNat (Address.offset g.octets.key ((first+size-1 : Nat) : F)) = _
  rw [Address.toNat_offset _ bounded _ (by omega)]
  omega

/-- Each logical position before the path endpoint has an actual placement lane at the
corresponding guest address, with the incoming clock, sink, and owner. -/
theorem placement_lane {groups : List (Group F)} {start finish : Placement F}
    (walk : Walk.IsWalk (fun g : Group F => (g.previous,g.next)) start finish groups)
    (moves : ∀ g ∈ groups, g.Movements) (k : Nat)
    (lo : Address.toNat start.position ≤ k) (hi : k < Address.toNat finish.position) :
    ∃ g ∈ groups, g.previous.clock = start.clock ∧ g.previous.sink = start.sink ∧ g.previous.owner = start.owner ∧
      ∃ j : Fin 8, j.val < g.plan.size.val ∧ Address.toNat g.previous.position + j.val = k ∧
        Address.toNat g.octets.key + g.plan.first.val + j.val = Address.toNat start.address + 1 + (k - Address.toNat start.position) := by
  induction groups generalizing start with
  | nil =>
    change start = finish at walk
    subst start
    omega
  | cons g tail ih =>
    obtain ⟨origin,rest⟩ := walk
    change g.previous = start at origin
    subst start
    obtain ⟨fits,first,address,position⟩ := moves g List.mem_cons_self
    by_cases inside : k < Address.toNat g.next.position
    · let j : Fin 8 := ⟨k - Address.toNat g.previous.position,by omega⟩
      refine ⟨g,List.mem_cons_self,rfl,rfl,rfl,j,?_,?_,?_⟩ <;> dsimp only [j] <;> omega
    · obtain ⟨other,mem,clock,sink,owner,j,small,atPosition,atGuest⟩ := ih rest (fun x m => moves x (List.mem_cons_of_mem _ m)) (Nat.le_of_not_gt inside)
      change _ = Address.toNat g.next.address + 1 + (k - Address.toNat g.next.position) at atGuest
      exact ⟨other,List.mem_cons_of_mem _ mem,clock,sink,owner,j,small,atPosition,by omega⟩

end SP1Clean.WriteEffects
