module

public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Membership
import Mathlib.Order.Basic

/-!
# Rational-key sorting of retained payloads

Insertion compares the supplied rational keys and retains the stored payload
when keys coincide. Structural membership and strict ordering certificates
follow the same finite insertion and tail-sorting operations.
-/

namespace Purelib.Data.List.Sort.RationalKey.Basic

open Purelib.Data.Rat.Fraction
open Purelib.Data.List
open Purelib.Data.List.Sort.RationalKey

public section

universe u
variable {Alpha : Type u} (key : Alpha → Purelib.Data.Rat.Fraction.Rational)

/-- Insert a payload by rational key, retaining the stored payload at an equal key.

Strict comparison chooses insertion before the head or recursion after it. If neither
key is smaller, the existing head and tail are retained unchanged. -/
@[expose] def insert (entry : Alpha) : List Alpha → List Alpha
  | [] => [entry]
  | head :: tail =>
      if key entry < key head then entry :: head :: tail
      else if key head < key entry then head :: Basic.insert entry tail
      else head :: tail

/-- Every payload after key-based insertion is newly inserted or an input member.

The actual comparison branch either retains the input or inserts the supplied
payload. Membership constructors retain its selected finite occurrence. -/
theorem mem_insert {entry value : Alpha} {entries : List Alpha} (member : value ∈ Basic.insert key entry entries) :
    value = entry ∨ value ∈ entries := by
  induction entries with
  | nil => exact Or.inl (Membership.mem_singleton.mp member)
  | cons head tail ih =>
      unfold Basic.insert at member
      split at member
      · exact Membership.mem_cons.mp member
      · split at member
        · rcases Membership.mem_cons.mp member with equal | inTail
          · exact Or.inr (Membership.mem_cons.mpr (Or.inl equal))
          · rcases ih inTail with equal | original
            · exact Or.inl equal
            · exact Or.inr (List.mem_cons_of_mem _ original)
        · exact Or.inr member

/-- Key-based insertion preserves the input keys together with the inserted key.

Both membership directions follow the selected insertion branch. Equal keys
retain the input payload while identifying its key with the supplied key. -/
theorem keys_insert (entry : Alpha) (entries : List Alpha) (coordinate : Rational) :
    coordinate ∈ (Basic.insert key entry entries).map key ↔ coordinate = key entry ∨ coordinate ∈ entries.map key := by
  induction entries with
  | nil =>
      constructor
      · intro member
        exact Or.inl (Membership.mem_singleton.mp member)
      · intro member
        cases member with
        | inl equal => exact Membership.mem_singleton.mpr equal
        | inr impossible => nomatch impossible
  | cons head tail ih =>
      unfold Basic.insert
      split
      · constructor
        · intro member
          exact Membership.mem_cons.mp member
        · intro member
          exact Membership.mem_cons.mpr member
      · rename_i notBefore
        split
        · constructor
          · intro member
            cases Membership.mem_cons.mp member with
            | inl equal =>
                exact Or.inr (Membership.mem_cons.mpr (Or.inl equal))
            | inr retained =>
                cases ih.mp retained with
                | inl equal => exact Or.inl equal
                | inr original =>
                    exact Or.inr (Membership.mem_cons.mpr (Or.inr original))
          · intro member
            cases member with
            | inl equal =>
                exact Membership.mem_cons.mpr (Or.inr (ih.mpr (Or.inl equal)))
            | inr retained =>
                cases Membership.mem_cons.mp retained with
                | inl equal => exact Membership.mem_cons.mpr (Or.inl equal)
                | inr original =>
                    exact Membership.mem_cons.mpr (Or.inr (ih.mpr (Or.inr original)))
        · rename_i notAfter
          have equal : key entry = key head :=
            le_antisymm (le_of_not_gt notAfter) (le_of_not_gt notBefore)
          constructor
          · intro member
            exact Or.inr member
          · intro member
            cases member with
            | inl selected =>
                exact Membership.mem_cons.mpr (Or.inl (selected.trans equal))
            | inr retained => exact retained

/-- Insertion by rational key preserves strict pairwise key ordering.

The stored payload is retained when its key equals the inserted key, so equality
introduces no duplicate key into the ordered list. -/
theorem pairwise_insert (entry : Alpha) {entries : List Alpha}
    (ordered : entries.Pairwise (fun left right => key left < key right)) :
    (Basic.insert key entry entries).Pairwise (fun left right => key left < key right) := by
  induction entries with
  | nil => exact List.Pairwise.cons (fun _ member => by nomatch member) List.Pairwise.nil
  | cons head tail ih =>
      rcases List.pairwise_cons.mp ordered with ⟨headBefore, tailOrdered⟩
      unfold Basic.insert
      split
      · rename_i before
        apply List.Pairwise.cons _ ordered
        intro value member
        rcases Membership.mem_cons.mp member with equal | inTail
        · rw [equal]
          exact before
        · exact before.trans (headBefore value inTail)
      · split
        · rename_i after
          apply List.Pairwise.cons _ (ih tailOrdered)
          intro value member
          rcases Basic.mem_insert key member with equal | inTail
          · rw [equal]
            exact after
          · exact headBefore value inTail
        · exact ordered

/-- Sort retained payloads by rational key while removing repeated keys.

Recursively sort the tail and insert the head, retaining an already stored tail
payload at equal keys. Every retained payload is an original input value. -/
@[expose] def sort : List Alpha → List Alpha
  | [] => []
  | head :: tail => Basic.insert key head (Basic.sort tail)

/-- The key-sorted payload list has strictly increasing rational keys.

Structural tail sorting and key insertion retain pairwise strict comparison
of the selected payloads, including removal of repeated keys. -/
theorem pairwise_sort (entries : List Alpha) :
    (Basic.sort key entries).Pairwise (fun left right => key left < key right) := by
  induction entries with
  | nil => exact List.Pairwise.nil
  | cons head tail ih => exact Basic.pairwise_insert key head ih

/-- Sorting and removing repeated rational keys preserves the displayed keys.

Structural insertion gives both membership directions while retaining the
input values. Equal keys remove a repeated payload without losing its key. -/
theorem keys_sort (entries : List Alpha) (coordinate : Rational) :
    coordinate ∈ (Basic.sort key entries).map key ↔ coordinate ∈ entries.map key := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      constructor
      · intro member
        cases (Basic.keys_insert key head (Basic.sort key tail) coordinate).mp member with
        | inl equal => exact Membership.mem_cons.mpr (Or.inl equal)
        | inr retained => exact Membership.mem_cons.mpr (Or.inr (ih.mp retained))
      · intro member
        apply (Basic.keys_insert key head (Basic.sort key tail) coordinate).mpr
        cases Membership.mem_cons.mp member with
        | inl equal => exact Or.inl equal
        | inr retained => exact Or.inr (ih.mpr retained)

/-- Every payload in the key-sorted result belongs to the original input list.

The algorithm retains actual input values when sorting and removing equal keys, so
any data carried by the selected payload remains unchanged. -/
theorem mem_sort {entries : List Alpha} {entry : Alpha} (member : entry ∈ Basic.sort key entries) : entry ∈ entries :=
  by
  induction entries with
  | nil => exact member
  | cons head tail ih =>
      rcases Basic.mem_insert key member with equal | original
      · exact Membership.mem_cons.mpr (Or.inl equal)
      · exact List.mem_cons_of_mem _ (ih original)

end

end Purelib.Data.List.Sort.RationalKey.Basic
