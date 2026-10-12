module

import Purelib.Data.List.Membership
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Nat.Defs

section
public section

/-!
# Multiplicity in displayed lists

Recursive occurrence and absence certificates retain the original finite list. Natural multiplicities use its supplied
decidable equality and preserve every repeated occurrence.
-/

namespace Purelib.Data.List

open Purelib.Data

/-- Count the occurrences of one payload in a displayed finite list.

Use the supplied decidable equality at each head and add its indicator to the
recursively computed tail count. -/
@[expose] def countItem {α : Type} [DecidableEq α] : List α → α → Nat
  | [], _ => 0
  | item :: remaining, target =>
      (if item = target then 1 else 0) + Purelib.Data.List.countItem remaining target

/-- Certify by finite recursion that every listed payload differs from the target.

The empty list is absent vacuously. A nonempty list retains inequality of its head
and an absence certificate for its tail. -/
@[expose] def SampleAbsent {α : Type} (target : α) : List α → Prop
  | [] => True
  | item :: remaining =>
      item ≠ target ∧ Purelib.Data.List.SampleAbsent target remaining

/-- Express occurrence of a target payload by finite recursive disjunction.

A nonempty list contains the target when its head equals it or its retained tail
contains it. The empty list contains no target. -/
@[expose] def SampleContains {α : Type} (target : α) : List α → Prop
  | [] => False
  | item :: remaining =>
      item = target ∨ Purelib.Data.List.SampleContains target remaining

/-- Recursive occurrence evidence gives ordinary membership in the same finite list. -/
theorem sampleContains_mem {α : Type} (target : α) :
    ∀ {samples : List α}, List.SampleContains target samples → target ∈ samples
  | [], contains => contains.elim
  | item :: remaining, contains => by
      rcases contains with equal | tailContains
      · exact Membership.mem_cons.mpr (Or.inl equal.symm)
      · exact Membership.mem_cons.mpr (Or.inr
          (Purelib.Data.List.sampleContains_mem target tailContains))

/-- The multiplicity of a payload in a concatenation is the sum of its two
multiplicities. -/
theorem countItem_append {α : Type} [DecidableEq α]
    (left right : List α) (target : α) :
    List.countItem (left ++ right) target =
      List.countItem left target + List.countItem right target := by
  induction left with
  | nil => exact (Nat.zero_add (List.countItem right target)).symm
  | cons item remaining inductionHypothesis =>
      change ((if item = target then 1 else 0) + List.countItem (remaining ++ right) target) =
        ((if item = target then 1 else 0) + List.countItem remaining target) + List.countItem right target
      rw [inductionHypothesis, Nat.add_assoc]

/-- A payload's multiplicity cannot exceed the length of the finite sample list. -/
theorem countItem_le_length {α : Type} [DecidableEq α]
    (samples : List α) (target : α) :
    List.countItem samples target ≤ samples.length := by
  induction samples with
  | nil => exact Nat.le_refl 0
  | cons item remaining inductionHypothesis =>
      by_cases equal : item = target
      · rw [List.countItem, if_pos equal, Nat.one_add]
        exact Nat.succ_le_succ inductionHypothesis
      · rw [List.countItem, if_neg equal, Nat.zero_add]
        exact Nat.le_trans inductionHypothesis (Nat.le_succ _)

/-- Recursive absence evidence forces the target payload's multiplicity to zero. -/
theorem countItem_eq_zero_of_sampleAbsent
    {α : Type} [DecidableEq α] (target : α) :
    ∀ samples : List α, List.SampleAbsent target samples →
      List.countItem samples target = 0 := by
  intro samples
  induction samples with
  | nil => intro absent; rfl
  | cons item remaining inductionHypothesis =>
      intro absent
      rw [List.countItem, if_neg absent.1, Nat.zero_add]
      exact inductionHypothesis absent.2

/-- Recursive occurrence evidence makes the target payload's multiplicity strictly
positive. -/
theorem countItem_pos_of_sampleContains
    {α : Type} [DecidableEq α] (target : α) :
    ∀ samples : List α, List.SampleContains target samples →
      0 < List.countItem samples target := by
  intro samples
  induction samples with
  | nil => intro contains; exact contains.elim
  | cons item remaining inductionHypothesis =>
      intro contains
      by_cases equal : item = target
      · rw [List.countItem, if_pos equal, Nat.one_add]
        exact Nat.zero_lt_succ _
      · rw [List.countItem, if_neg equal, Nat.zero_add]
        rcases contains with same | tail
        · exact (equal same).elim
        · exact inductionHypothesis tail

/-- Decidable equality splits a displayed list into occurrence or absence evidence for a
target.

Inspect each retained head and recurse on the finite tail, returning the
corresponding recursive certificate without choosing an abstract occurrence. -/
theorem sampleContains_or_sampleAbsent
    {α : Type} [DecidableEq α] (target : α) :
    ∀ samples : List α,
      List.SampleContains target samples ∨ List.SampleAbsent target samples
  | [] => Or.inr trivial
  | item :: remaining => by
      by_cases equal : item = target
      · exact Or.inl (Or.inl equal)
      · rcases Purelib.Data.List.sampleContains_or_sampleAbsent target remaining with
          tailContains | tailAbsent
        · exact Or.inl (Or.inr tailContains)
        · exact Or.inr ⟨equal, tailAbsent⟩

/-- Recursive occurrence and recursive absence cannot hold for the same target and list. -/
theorem sampleContains_not_sampleAbsent
    {α : Type} (target : α) :
    ∀ samples : List α,
      List.SampleContains target samples → ¬List.SampleAbsent target samples
  | [], contains => contains.elim
  | item :: remaining, contains => by
      intro absent
      rcases contains with equal | tailContains
      · exact absent.1 equal
      · exact Purelib.Data.List.sampleContains_not_sampleAbsent target remaining
          tailContains absent.2
end Purelib.Data.List

end
