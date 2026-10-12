module
import Purelib.Data.Nat.Addition
import Purelib.Data.Nat.Multiplication
import Purelib.Data.List.Filter
import Purelib.Tactic.Ring
import Purelib.Data.List.Reverse
import Purelib.Data.List.Map
import Purelib.Data.List.Pairwise
import Purelib.Data.List.Append

import Purelib.Data.List.Membership

open Purelib.Data.List

/-!
# Structural finite-list lemmas

The upstream statements replaced here concern only structural recursion over
displayed finite lists.  Their current proof routes use generic simplifier or
extensionality infrastructure that reaches `Quot.sound`.  These versions keep
the same mathematical content while exposing the finite recursion directly.
-/

public section

namespace Purelib.Data.List.Nodup

universe u v w

variable {Alpha : Type u} {Beta : Type v} {Gamma : Type w}

/-- A singleton finite list has no repeated entries. -/
theorem nodup_singleton (value : Alpha) : [value].Nodup :=
  Pairwise.pairwise_singleton (fun left right : Alpha => left ≠ right) value

/-- Appending two duplicate-free lists preserves duplicate-freeness when their members
are disjoint.

The supplied cross-list inequality excludes every possible repeat involving one entry
from each list; each input's own retained Nodup proof excludes internal repeats. -/
theorem nodup_append {left right : List Alpha}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (cross : ∀ leftValue ∈ left, ∀ rightValue ∈ right,
      leftValue ≠ rightValue) :
    (left ++ right).Nodup :=
  Pairwise.pairwise_append leftNodup rightNodup cross

-- This original published theorem retains its qualified Nodup.List name.
-- The previous file-wide duplicate-namespace exception is narrowed to this API.
/-- An injective function maps a duplicate-free finite list to a duplicate-free list. -/
theorem nodup_map_of_injective {function : Alpha → Beta}
    (injective : Function.Injective function) :
    ∀ {values : List Alpha}, values.Nodup → (values.map function).Nodup
  | [], _ => List.Pairwise.nil
  | head :: tail, nodup => by
      rcases List.pairwise_cons.mp nodup with ⟨headFresh, tailNodup⟩
      apply List.pairwise_cons.mpr
      refine ⟨?_, nodup_map_of_injective injective tailNodup⟩
      intro mapped mappedMember equal
      rcases Map.mem_map.mp mappedMember with
        ⟨source, sourceMember, sourceEqual⟩
      apply headFresh source sourceMember
      apply injective
      exact equal.trans sourceEqual.symm

/-- A duplicate-free subcollection cannot exceed its displayed carrier's length.

The supplied containment transports each actual occurrence into the original
carrier. Removing one selected occurrence retains a duplicate-free carrier
for the remaining source tail. -/
theorem nodup_length_le_of_mem :
    ∀ {selected : List Alpha}, selected.Nodup →
      ∀ {carrier : List Alpha}, carrier.Nodup →
        (∀ value ∈ selected, value ∈ carrier) →
          selected.length ≤ carrier.length
  | [], _, _, _, _ => Nat.zero_le _
  | head :: tail, selectedNodup, carrier, carrierNodup, contained => by
      rcases Membership.split_of_mem
          (contained head List.mem_cons_self) with
        ⟨before, after, carrierSplit⟩
      have reducedCarrier : (before ++ after).Nodup := by
        apply Pairwise.pairwise_remove_middle (middle := head)
        rw [← carrierSplit]
        exact carrierNodup
      have tailContained :
          ∀ value ∈ tail, value ∈ before ++ after := by
        intro value valueMember
        have carrierMember := contained value
          (List.mem_cons_of_mem head valueMember)
        rw [carrierSplit] at carrierMember
        rcases Membership.mem_append.mp carrierMember with beforeMember | restMember
        · exact Membership.mem_append.mpr (Or.inl beforeMember)
        · cases restMember with
          | head =>
              exact False.elim
                ((List.pairwise_cons.mp selectedNodup).1 head valueMember rfl)
          | tail _ suffixMember =>
              exact Membership.mem_append.mpr (Or.inr suffixMember)
      have tailBound := Purelib.Data.List.Nodup.nodup_length_le_of_mem
        (List.pairwise_cons.mp selectedNodup).2
        reducedCarrier tailContained
      rw [Append.length_append] at tailBound
      rw [carrierSplit, List.length_cons, Append.length_append,
        List.length_cons]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.add_le_add_right tailBound 1
end Purelib.Data.List.Nodup

end

namespace Purelib.Data.List.Nodup

/-- Reversing a retained list preserves the absence of repeated entries.

The reversed tail is followed by the original head. Its source absence
certificate excludes that head from every retained tail occurrence. -/
public theorem reverse {Alpha : Type} : {entries : List Alpha} → entries.Nodup → entries.reverse.Nodup
  | [], _ => .nil
  | head :: tail, unique => by
      rw [Reverse.reverse_cons]
      refine nodup_append (reverse (List.pairwise_cons.mp unique).2)
        (nodup_singleton head) ?_
      intro first firstMember last lastMember equal
      have same := equal.trans (Membership.mem_singleton.mp lastMember)
      exact (List.pairwise_cons.mp unique).1 _ ((Reverse.mem_reverse _).mp firstMember) same.symm

/-- Equal images identify members of a list whose mapped entries have no duplicates.

Both arguments belong to the original list. Its mapped list has no repeated
entries, so equality of the two images forces equality of the arguments. -/
public theorem eq_of_map_eq_of_mem {α β : Type} (map : α → β) {items : List α}
    (unique : (items.map map).Nodup) {first last : α} (firstMember : first ∈ items) (lastMember : last ∈ items)
    (equal : map first = map last) : first = last := by
  induction items with
  | nil => exact (List.not_mem_nil firstMember).elim
  | cons head tail ih =>
      have parts := List.pairwise_cons.mp unique
      rcases Membership.mem_cons.mp firstMember with same | firstMember
      · subst first
        rcases Membership.mem_cons.mp lastMember with same | lastMember
        · exact same.symm
        · exact (parts.1 _ (Map.mem_map_of_mem lastMember) equal).elim
      · rcases Membership.mem_cons.mp lastMember with same | lastMember
        · subst last
          exact (parts.1 _ (Map.mem_map_of_mem firstMember) equal.symm).elim
        · exact ih parts.2 firstMember lastMember

end Purelib.Data.List.Nodup

namespace Purelib.Data.List.Nodup

/-- Equal retained bounded readings of a duplicate-free list identify their indices.

Both natural positions carry their original length bounds. Structural recursion
uses the distinct head and retained tail certificate without selecting a new
occurrence or recomputing the list. -/
public theorem getElem_index_injective {Item : Type} {values : List Item}
    (distinct : values.Nodup) {left right : Nat}
    (leftBound : left < values.length) (rightBound : right < values.length)
    (equal : values[left]'leftBound = values[right]'rightBound) : left = right := by
  induction values generalizing left right with
  | nil => exact (Nat.not_lt_zero left leftBound).elim
  | cons head tail ih =>
      have facts := List.pairwise_cons.mp distinct
      cases left with
      | zero =>
          cases right with
          | zero => rfl
          | succ right =>
              have member : head ∈ tail := by
                change head = tail[right]'(Nat.lt_of_succ_lt_succ rightBound) at equal
                rw [equal]
                exact List.getElem_mem _
              exact (facts.1 _ member rfl).elim
      | succ left =>
          cases right with
          | zero =>
              have member : head ∈ tail := by
                change tail[left]'(Nat.lt_of_succ_lt_succ leftBound) = head at equal
                rw [← equal]
                exact List.getElem_mem _
              exact (facts.1 _ member rfl).elim
          | succ right =>
              exact congrArg Nat.succ (ih facts.2
                (Nat.lt_of_succ_lt_succ leftBound) (Nat.lt_of_succ_lt_succ rightBound) equal)

end Purelib.Data.List.Nodup

section
namespace Purelib.Data.List.Nodup
open Purelib.Data.List
open Purelib.Data.Nat
open scoped Purelib.Data.Nat Purelib.Data.List.Membership

/-- A finite duplicate-free list closed under a fixed-point-free involution has even length.

The constructive recursion removes each head together with its retained mate, producing an explicit half-length witness.
-/
public theorem
  fixedPointFreeInvolution_length_even
  {Alpha : Type*}
    (eqDecidable : DecidableEq Alpha) (involution : Alpha → Alpha)
    (values : List Alpha) (nodup : values.Nodup)
    (closed : ∀ value ∈ values, involution value ∈ values)
    (involutive : ∀ value ∈ values, involution (involution value) = value)
    (fixedPointFree : ∀ value ∈ values, involution value ≠ value) :
    ∃ half : Nat, values.length = half + half := by
  letI : DecidableEq Alpha := eqDecidable
  cases values with
  | nil => exact ⟨0, rfl⟩
  | cons head tail =>
      let mate := involution head
      let remainder := tail.filter fun value => value ≠ mate
      have headMember : head ∈ head :: tail := List.mem_cons_self
      have mateMember : mate ∈ head :: tail := closed head headMember
      have mateDifferent : mate ≠ head := fixedPointFree head headMember
      have mateTail : mate ∈ tail := by
        rcases Membership.mem_cons.mp mateMember with mateHead | member
        · exact False.elim (mateDifferent mateHead)
        · exact member
      have tailNodup : tail.Nodup := (List.pairwise_cons.mp nodup).2
      have remainderNodup : remainder.Nodup := Filter.pairwise_filter _ tailNodup
      have remainderClosed :
          ∀ value ∈ remainder, involution value ∈ remainder := by
        intro value member
        have memberData := Filter.mem_filter.mp member
        have valueTail : value ∈ tail := memberData.1
        have valueDifferentMate : value ≠ mate :=
          of_decide_eq_true memberData.2
        have valueMember : value ∈ head :: tail :=
          List.mem_cons_of_mem head valueTail
        have imageMember := closed value valueMember
        have imageDifferentHead : involution value ≠ head := by
          intro imageHead
          apply valueDifferentMate
          calc
            value = involution (involution value) :=
              (involutive value valueMember).symm
            _ = involution head := congrArg involution imageHead
            _ = mate := rfl
        have imageTail : involution value ∈ tail := by
          rcases Membership.mem_cons.mp imageMember with imageHead | member
          · exact False.elim (imageDifferentHead imageHead)
          · exact member
        apply Filter.mem_filter.mpr
        constructor
        · exact imageTail
        · apply decide_eq_true
          intro imageMate
          have headEqual : value = head := by
            calc
              value = involution (involution value) :=
                (involutive value valueMember).symm
              _ = involution mate := congrArg involution imageMate
              _ = head := by
                exact involutive head headMember
          exact (List.pairwise_cons.mp nodup).1 value valueTail headEqual.symm
      have remainderInvolutive :
          ∀ value ∈ remainder, involution (involution value) = value := by
        intro value member
        exact involutive value
          (List.mem_cons_of_mem head (Filter.mem_filter.mp member).1)
      have remainderFixedPointFree :
          ∀ value ∈ remainder, involution value ≠ value := by
        intro value member
        exact fixedPointFree value
          (List.mem_cons_of_mem head (Filter.mem_filter.mp member).1)
      have remainderShorter : remainder.length < (head :: tail).length :=
        Nat.lt_succ_of_le (Filter.length_filter_le _ _)
      have induction :=
        Purelib.Data.List.Nodup.fixedPointFreeInvolution_length_even
        eqDecidable involution remainder remainderNodup remainderClosed
        remainderInvolutive remainderFixedPointFree
      rcases induction with ⟨half, halfEquation⟩
      have remainderLength : remainder.length + 1 = tail.length :=
        Filter.filter_ne_target_length_add_one eqDecidable mate tailNodup
          mateTail
      refine ⟨half + 1, ?_⟩
      rw [List.length_cons, ← remainderLength, halfEquation]
      ring1
termination_by values.length
decreasing_by
  simp_all only [List.length_cons]
  exact Nat.lt_succ_of_le (Filter.length_filter_le _ _)

/-- A contained duplicate-free list of equal length contains every carrier entry.

Both lists are duplicate-free and equality is decidable; adding any missing carrier value would exceed the finite length
bound. -/
public theorem
  mem_of_nodup_contained_length_eq
  {Alpha : Type*}
    (eqDecidable : DecidableEq Alpha)
    {selected carrier : List Alpha} (selectedNodup : selected.Nodup)
    (carrierNodup : carrier.Nodup)
    (contained : ∀ value ∈ selected, value ∈ carrier)
    (lengthEqual : selected.length = carrier.length)
    {value : Alpha} (valueMember : value ∈ carrier) : value ∈ selected := open Purelib in by
  letI : DecidableEq Alpha := eqDecidable
  by_cases selectedMember : value ∈ selected
  · exact selectedMember
  · have extendedNodup : (value :: selected).Nodup := by
      apply List.pairwise_cons.mpr
      constructor
      · intro other otherMember equal
        exact selectedMember (equal ▸ otherMember)
      · exact selectedNodup
    have extendedContained : ∀ other ∈ value :: selected, other ∈ carrier := by
      intro other member
      rcases Membership.mem_cons.mp member with equal | selectedOther
      · exact equal ▸ valueMember
      · exact contained other selectedOther
    have bound := Data.List.Nodup.nodup_length_le_of_mem extendedNodup
      carrierNodup extendedContained
    rw [List.length_cons, lengthEqual] at bound
    exact False.elim (Nat.not_succ_le_self carrier.length bound)

end Purelib.Data.List.Nodup
end
