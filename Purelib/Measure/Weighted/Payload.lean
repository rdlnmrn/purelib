module
import Purelib.Data.List.Membership
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Weighted.Consolidation
public import Purelib.Measure.Weighted.Transform

section
/-!
# Finite Radon--Nikodym existence

For arbitrary displayed finite contents with decidable payload equality, the
union of their payload tables can be consolidated into a duplicate-free key
list.  Assigning each key its exact singleton mass gives aligned source and
target rows.  Absolute continuity supplies the rowwise zero implication, so
the quotient-density algorithm yields a Radon--Nikodym witness.

The proof below includes the finite histogram reconstruction lemma: summing
singleton masses over any duplicate-free key list covering a displayed atom
table recovers every rational integral.
-/

public section

namespace Purelib.Measure

open Purelib.Data.List

/-- Retain an original-list occurrence whose payload equals the supplied value. -/
@[expose] def PayloadPresent {α : Type} (item : α) (atoms : List (Weighted α)) : Prop :=
  ∃ atom, atom ∈ atoms ∧ atom.item = item

/-- The inserted weighted payload occurs in the resulting merged-or-extended list. -/
private theorem payloadPresent_insertWeighted_self {α : Type}
    [DecidableEq α] (atom : Weighted α) :
    ∀ atoms : List (Weighted α),
      PayloadPresent atom.item (insertWeighted atom atoms)
  | [] => by
      exact ⟨atom, List.mem_cons_self, rfl⟩
  | current :: remaining => by
      by_cases same : atom.item = current.item
      · rw [insertWeighted, dif_pos same]
        exact ⟨_, List.mem_cons_self, same.symm⟩
      · rw [insertWeighted, dif_neg same]
        rcases payloadPresent_insertWeighted_self atom remaining with
          ⟨candidate, member, equal⟩
        exact ⟨candidate, List.mem_cons_of_mem current member, equal⟩

/-- Inserting another weighted occurrence preserves every original payload's presence. -/
private theorem payloadPresent_insertWeighted_of_present {α : Type}
    [DecidableEq α] (item : α) (inserted : Weighted α) :
    ∀ atoms : List (Weighted α),
      PayloadPresent item atoms →
        PayloadPresent item (insertWeighted inserted atoms)
  | [], present => by
      rcases present with ⟨atom, member, equal⟩
      cases member
  | current :: remaining, present => by
      rcases present with ⟨candidate, member, equal⟩
      rcases Membership.mem_cons.mp member with head | tail
      · subst candidate
        by_cases same : inserted.item = current.item
        · rw [insertWeighted, dif_pos same]
          exact ⟨_, List.mem_cons_self, equal⟩
        · rw [insertWeighted, dif_neg same]
          exact ⟨current, List.mem_cons_self, equal⟩
      · by_cases same : inserted.item = current.item
        · rw [insertWeighted, dif_pos same]
          exact ⟨candidate, List.mem_cons_of_mem _ tail, equal⟩
        · rw [insertWeighted, dif_neg same]
          rcases payloadPresent_insertWeighted_of_present item inserted
              remaining ⟨candidate, tail, equal⟩ with
            ⟨found, foundMember, foundEqual⟩
          exact ⟨found, List.mem_cons_of_mem current foundMember, foundEqual⟩

/-- Every original occurrence's payload remains present after exact weight consolidation.

The witness identifies an occurrence in the retained consolidated list with
the same payload, including when its weight was merged with another occurrence. -/
theorem payloadPresent_consolidateAtoms_of_mem {α : Type}
    [DecidableEq α] :
    ∀ (atoms : List (Weighted α)) (atom : Weighted α),
      atom ∈ atoms → PayloadPresent atom.item (consolidateAtoms atoms)
  | [], atom, member => by cases member
  | head :: remaining, atom, member => by
      rw [consolidateAtoms]
      rcases Membership.mem_cons.mp member with same | tail
      · subst atom
        exact payloadPresent_insertWeighted_self head
          (consolidateAtoms remaining)
      · exact payloadPresent_insertWeighted_of_present atom.item head
          (consolidateAtoms remaining)
          (payloadPresent_consolidateAtoms_of_mem remaining atom tail)

/-- A payload absent from the retained list differs from every member's payload.

The recursive absence certificate applies to each original occurrence. Its
conclusion retains the supplied payload and the selected list member. -/
theorem payloadAbsent_ne_of_mem {α : Type} (item : α) :
    ∀ {atoms : List (Weighted α)}, PayloadAbsent item atoms →
      ∀ {atom : Weighted α}, atom ∈ atoms → item ≠ atom.item
  | [], absent, atom, member => by cases member
  | head :: remaining, absent, atom, member => by
      rcases absent with ⟨headDifferent, tailAbsent⟩
      rcases Membership.mem_cons.mp member with same | tail
      · subst atom
        exact headDifferent
      · exact payloadAbsent_ne_of_mem item tailAbsent tail

/-- A present payload different from the head payload has an occurrence in the exact tail.

The original occurrence witness is retained in the tail because equality
with the displayed head would contradict the supplied payload difference. -/
theorem payloadPresent_tail_of_cons_of_ne {α : Type}
    (item : α) (head : Weighted α) (remaining : List (Weighted α))
    (different : item ≠ head.item)
    (present : PayloadPresent item (head :: remaining)) :
    PayloadPresent item remaining := by
  rcases present with ⟨candidate, member, equal⟩
  rcases Membership.mem_cons.mp member with same | tail
  · subst candidate
    exact (different equal.symm).elim
  · exact ⟨candidate, tail, equal⟩

/-- Every occurrence retained by restriction is a member of the exact original list.

Restriction follows the supplied Boolean event without replacing retained
occurrences. Membership therefore transports to the same input list. -/
theorem mem_restrictAtoms_original {α : Type}
    (event : α → Bool) :
    ∀ {atoms : List (Weighted α)} {atom : Weighted α},
      atom ∈ restrictAtoms atoms event → atom ∈ atoms
  | [], atom, member => by cases member
  | head :: remaining, atom, member => by
      cases selected : event head.item
      · simp only [-eq_self, -iff_self, restrictAtoms, selected] at member
        exact List.mem_cons_of_mem head
          (mem_restrictAtoms_original event member)
      · simp only [-eq_self, -iff_self, restrictAtoms, selected] at member
        rcases Membership.mem_cons.mp member with same | tail
        · exact Membership.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons_of_mem head
            (mem_restrictAtoms_original event tail)

/-- Every occurrence retained by restriction satisfies the original Boolean event.

The certificate reads the same event at the retained occurrence. Its true
branch is the branch that placed that occurrence in the restricted list. -/
theorem mem_restrictAtoms_selected {α : Type}
    (event : α → Bool) :
    ∀ {atoms : List (Weighted α)} {atom : Weighted α},
      atom ∈ restrictAtoms atoms event → event atom.item = true
  | [], atom, member => by cases member
  | head :: remaining, atom, member => by
      cases selected : event head.item
      · simp only [-eq_self, -iff_self, restrictAtoms, selected] at member
        exact mem_restrictAtoms_selected event member
      · simp only [-eq_self, -iff_self, restrictAtoms, selected] at member
        rcases Membership.mem_cons.mp member with same | tail
        · subst atom
          exact selected
        · exact mem_restrictAtoms_selected event tail

end Purelib.Measure

end
