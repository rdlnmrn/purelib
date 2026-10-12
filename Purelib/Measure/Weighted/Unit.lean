module
import Purelib.Algebra.NatCast
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction

import Purelib.Data.List.Event
public import Purelib.Data.List.Multiplicity
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Sampling.Statistic
import Purelib.Measure.Distribution.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Measure.Weighted.Operations

section
public section

/-!
# Finite counting and empirical measures

A displayed sample list gives an exact rational counting content.  When its
length is explicitly positive, uniform normalization gives an exact empirical
distribution.  Probabilities are selected natural counts divided by the
displayed finite sample size.
-/

namespace Purelib.Measure

open Purelib.Algebra

open Purelib.Data.List

open Purelib in
/-- Attach unit rational weight to every original sample occurrence in its retained list order. -/
@[expose] def unitAtoms {α : Type} : List α → List (Measure.Weighted α)
  | [] => []
  | item :: remaining =>
      ⟨item, 1, by decide⟩ :: unitAtoms remaining

/-- Attaching unit weights preserves the exact sample count. -/
theorem unitAtoms_length {α : Type} (samples : List α) :
    (unitAtoms samples).length = samples.length := by
  induction samples with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, unitAtoms, List.length_cons, inductionHypothesis]
      rfl

/-- Attaching unit weights preserves concatenation of the exact sample lists. -/
theorem unitAtoms_append {α : Type} (left right : List α) :
    unitAtoms (left ++ right) = unitAtoms left ++ unitAtoms right := by
  induction left with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, List.cons_append, unitAtoms, List.cons_append,
        inductionHypothesis]
      rfl

open Purelib.Data.Rat in
/-- The total unit weight equals the rational cast of the original sample length. -/
theorem totalWeight_unitAtoms {α : Type} (samples : List α) :
    totalWeight (unitAtoms samples) = (samples.length : Fraction.Rational) := by
  induction samples with
  | nil =>
      simp only [-eq_self, -iff_self, unitAtoms, totalWeight, List.length_nil, Nat.cast_zero]
      rfl
  | cons item remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, unitAtoms, totalWeight, List.length_cons,
        inductionHypothesis, Nat.cast_succ]
      ring1

open Purelib in
/-- Every unit-weighted occurrence retains a payload present in the exact original sample list. -/
theorem unitAtoms_member_sampleContains {α : Type}
    (candidate : Measure.Weighted α) :
    ∀ {samples : List α}, candidate ∈ unitAtoms samples →
      Data.List.SampleContains candidate.item samples
  | [], member => (List.not_mem_nil member).elim
  | item :: remaining, member => by
      change candidate ∈ ⟨item, 1, by decide⟩ :: unitAtoms remaining at member
      rcases Membership.mem_cons.mp member with equal | tailMember
      · have itemEqual :=
          congrArg (fun row : Measure.Weighted α => row.item) equal
        exact Or.inl itemEqual.symm
      · exact Or.inr
          (unitAtoms_member_sampleContains candidate tailMember)

open Purelib in
open Purelib.Data.Rat in
/-- An event's total unit weight equals the rational cast of its exact finite sample count. -/
theorem eventWeight_unitAtoms {α : Type} (samples : List α)
    (event : α → Bool) :
    eventWeight (unitAtoms samples) event =
      (Data.List.countEvent samples event : Fraction.Rational) := by
  induction samples with
  | nil =>
      simp only [-eq_self, -iff_self, unitAtoms, eventWeight, Data.List.countEvent, Nat.cast_zero]
      rfl
  | cons item remaining inductionHypothesis =>
      cases selected : event item with
      | false =>
          change (match event item with | true => (1 : Fraction.Rational) | false => 0) +
            eventWeight (unitAtoms remaining) event =
              ((if event item = true then 1 else 0) + Data.List.countEvent remaining event : Nat)
          rw [selected]
          change 0 + eventWeight (unitAtoms remaining) event =
            ((0 + Data.List.countEvent remaining event : Nat) : Fraction.Rational)
          rw [inductionHypothesis, NatCast.add, Nat.cast_zero, zero_add]
      | true =>
          change (match event item with | true => (1 : Fraction.Rational) | false => 0) +
            eventWeight (unitAtoms remaining) event =
              ((if event item = true then 1 else 0) + Data.List.countEvent remaining event : Nat)
          rw [selected]
          change 1 + eventWeight (unitAtoms remaining) event =
            ((1 + Data.List.countEvent remaining event : Nat) : Fraction.Rational)
          rw [inductionHypothesis, NatCast.add, Nat.cast_one]

open Purelib.Data.Rat in
/-- Unit-weighted integration equals the exact original sample sum. -/
theorem expectationWeight_unitAtoms {α : Type} (samples : List α)
    (value : α → Fraction.Rational) :
    Distribution.expectationWeight (unitAtoms samples) value =
      sumValues samples value := by
  induction samples with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, unitAtoms, Distribution.expectationWeight,
        sumValues, inductionHypothesis, one_mul]
      rfl
end Purelib.Measure

end
