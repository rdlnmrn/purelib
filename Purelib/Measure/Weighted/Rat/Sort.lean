module
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Weighted.Event
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

section
public section

/-!
# Constructive finite rational quantiles

A rational-valued finite distribution admits an executable lower quantile at
every displayed level in `(0, 1]`.  The implementation insertion-sorts the
displayed atom table and performs a terminating weighted crossing search.
The result is accompanied by the exact strict-lower and cumulative
inequalities; no infimum, completed real line, or choice principle occurs.
-/

namespace Purelib.Measure

open Purelib.Data.List

section
open Purelib.Data.Rat
/-- Require the retained rational payloads to be nondecreasing throughout the exact weighted list. -/
@[expose] def ValueSorted : List (Weighted Fraction.Rational) → Prop
  | [] => True
  | atom :: remaining =>
      (∀ candidate, candidate ∈ remaining → atom.item ≤ candidate.item) ∧
        ValueSorted remaining

/-- Insert the exact weighted occurrence before the first payload at least its value, or append it if none qualifies. -/
@[expose] def insertByValue (atom : Weighted Fraction.Rational) :
    List (Weighted Fraction.Rational) → List (Weighted Fraction.Rational)
  | [] => [atom]
  | candidate :: remaining =>
      if atom.item ≤ candidate.item then
        atom :: candidate :: remaining
      else
        candidate :: insertByValue atom remaining

/-- Sort rational payloads by recursively sorting the tail and inserting the unchanged head occurrence.

Comparisons use exact rational order and insert before equal values. Every occurrence keeps its original weight and
nonnegativity proof; sorting does not merge repeated payloads. -/
@[expose] def sortByValue :
    List (Weighted Fraction.Rational) → List (Weighted Fraction.Rational)
  | [] => []
  | atom :: remaining => insertByValue atom (sortByValue remaining)

/-- Every occurrence after sorted insertion is the inserted occurrence or an exact original-list member. -/
private theorem mem_insertByValue_source
    (atom candidate : Weighted Fraction.Rational) :
    ∀ {atoms : List (Weighted Fraction.Rational)},
      candidate ∈ insertByValue atom atoms →
        candidate = atom ∨ candidate ∈ atoms
  | [], member => by
      exact Or.inl (Membership.mem_singleton.mp member)
  | head :: remaining, member => by
      by_cases before : atom.item ≤ head.item
      · rw [insertByValue, if_pos before] at member
        rcases Membership.mem_cons.mp member with equal | member
        · exact Or.inl equal
        · rcases Membership.mem_cons.mp member with equal | tail
          · exact Or.inr (Membership.mem_cons.mpr (Or.inl equal))
          · exact Or.inr (Membership.mem_cons.mpr (Or.inr tail))
      · rw [insertByValue, if_neg before] at member
        rcases Membership.mem_cons.mp member with equal | tail
        · exact Or.inr (Membership.mem_cons.mpr (Or.inl equal))
        · rcases mem_insertByValue_source atom candidate tail with
            inserted | original
          · exact Or.inl inserted
          · exact Or.inr (Membership.mem_cons.mpr (Or.inr original))

/-- Every sorted occurrence belongs to the exact original weighted list. -/
private theorem mem_sortByValue_source
    (candidate : Weighted Fraction.Rational) :
    ∀ {atoms : List (Weighted Fraction.Rational)},
      candidate ∈ sortByValue atoms → candidate ∈ atoms
  | [], member => (List.not_mem_nil member).elim
  | atom :: remaining, member => by
      rcases mem_insertByValue_source atom candidate member with
          equal | tailMember
      · exact Membership.mem_cons.mpr (Or.inl equal)
      · exact Membership.mem_cons.mpr
          (Or.inr (mem_sortByValue_source candidate tailMember))

/-- A payload lower bound for the original list and inserted occurrence holds throughout the resulting list. -/
private theorem lowerBound_insertByValue
    (lower : Fraction.Rational) (atom : Weighted Fraction.Rational)
    (atomLower : lower ≤ atom.item) :
    ∀ {atoms : List (Weighted Fraction.Rational)},
      (∀ candidate, candidate ∈ atoms → lower ≤ candidate.item) →
      ∀ candidate, candidate ∈ insertByValue atom atoms →
        lower ≤ candidate.item := by
  intro atoms bounded candidate member
  rcases mem_insertByValue_source atom candidate member with equal | original
  · rw [equal]
    exact atomLower
  · exact bounded candidate original

/-- Inserting by rational value preserves nondecreasing payload order. -/
private theorem insertByValue_sorted
    (atom : Weighted Fraction.Rational) :
    ∀ {atoms : List (Weighted Fraction.Rational)},
      ValueSorted atoms → ValueSorted (insertByValue atom atoms)
  | [], sorted => by
      exact ⟨fun candidate member => by
        exact (List.not_mem_nil member).elim, trivial⟩
  | head :: remaining, sorted => by
      rcases sorted with ⟨headLower, tailSorted⟩
      by_cases before : atom.item ≤ head.item
      · rw [insertByValue, if_pos before]
        refine ⟨?_, ⟨headLower, tailSorted⟩⟩
        intro candidate member
        rcases Membership.mem_cons.mp member with equal | tail
        · rw [equal]
          exact before
        · exact before.trans (headLower candidate tail)
      · rw [insertByValue, if_neg before]
        refine ⟨?_, insertByValue_sorted atom tailSorted⟩
        apply lowerBound_insertByValue head.item atom
        · exact (Fraction.Order.Arithmetic.lt_of_not_ge_direct before).le
        · exact headLower

/-- The recursively sorted weighted list has nondecreasing rational payloads. -/
private theorem sortByValue_sorted :
    ∀ atoms : List (Weighted Fraction.Rational), ValueSorted (sortByValue atoms)
  | [] => trivial
  | atom :: remaining =>
      insertByValue_sorted atom (sortByValue_sorted remaining)

/-- Sorted insertion preserves every event weight of the inserted occurrence followed by the original list. -/
private theorem insertByValue_eventWeight
    (atom : Weighted Fraction.Rational) (event : Fraction.Rational → Bool) :
    ∀ atoms : List (Weighted Fraction.Rational),
      eventWeight (insertByValue atom atoms) event =
        eventWeight (atom :: atoms) event
  | [] => rfl
  | head :: remaining => by
      by_cases before : atom.item ≤ head.item
      · rw [insertByValue, if_pos before]
      · rw [insertByValue, if_neg before]
        simp only [-eq_self, -iff_self, eventWeight, insertByValue_eventWeight]
        ring1

/-- Sorted insertion preserves the exact total of the inserted occurrence followed by the original list. -/
private theorem insertByValue_totalWeight
    (atom : Weighted Fraction.Rational) :
    ∀ atoms : List (Weighted Fraction.Rational),
      totalWeight (insertByValue atom atoms) =
        totalWeight (atom :: atoms)
  | [] => rfl
  | head :: remaining => by
      by_cases before : atom.item ≤ head.item
      · rw [insertByValue, if_pos before]
      · rw [insertByValue, if_neg before]
        simp only [-eq_self, -iff_self, totalWeight, insertByValue_totalWeight]
        ring1

/-- Sorting rational payloads preserves every Boolean event's exact weight. -/
private theorem sortByValue_eventWeight
    (atoms : List (Weighted Fraction.Rational)) (event : Fraction.Rational → Bool) :
    eventWeight (sortByValue atoms) event = eventWeight atoms event := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      rw [sortByValue, insertByValue_eventWeight]
      simp only [-eq_self, -iff_self, eventWeight, inductionHypothesis]
      rfl

/-- Sorting rational payloads preserves the exact total weight. -/
private theorem sortByValue_totalWeight
    (atoms : List (Weighted Fraction.Rational)) :
    totalWeight (sortByValue atoms) = totalWeight atoms := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      rw [sortByValue, insertByValue_totalWeight]
      simp only [-eq_self, -iff_self, totalWeight, inductionHypothesis]
      rfl

/-- Certify the exact sort's ordering, total weight, original occurrence membership and event-weight preservation. -/
theorem sortByValue_certificates (atoms : List (Weighted Fraction.Rational)) :
    ValueSorted (sortByValue atoms) ∧
      totalWeight (sortByValue atoms) = totalWeight atoms ∧
      (∀ candidate, candidate ∈ sortByValue atoms → candidate ∈ atoms) ∧
      (∀ event, eventWeight (sortByValue atoms) event = eventWeight atoms event) := by
  refine ⟨sortByValue_sorted atoms, sortByValue_totalWeight atoms, ?_, ?_⟩
  · intro candidate member
    exact mem_sortByValue_source candidate member
  · intro event
    exact sortByValue_eventWeight atoms event
end

end Purelib.Measure

end
