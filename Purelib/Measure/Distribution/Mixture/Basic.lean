module

import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Weighted.Operations
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Explicit finite rational mixtures

A mixing coefficient is displayed rational data in `[0,1]`.  A mixture is
formed by scaling two finite atom tables and concatenating them, so all laws
below are exact finite-list calculations.
-/

namespace Purelib.Measure

open Purelib.Data

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retain a rational mixing coefficient with certificates that it lies between zero and one. -/
structure MixingWeight where
  /-- The exact rational coefficient assigned to the first component. -/ coefficient : Fraction.Rational
  /-- The retained coefficient is nonnegative. -/ nonnegative : 0 ≤ coefficient
  /-- The retained coefficient is at most one. -/ atMostOne : coefficient ≤ 1

constructive_injectivity MixingWeight

namespace MixingWeight

open Purelib.Data.Rat

section
open Purelib.Data.Rat
/-- Subtract the retained coefficient from one to obtain the complementary mixing weight. -/
@[expose] def complement (weight : MixingWeight) : Fraction.Rational :=
  1 - weight.coefficient

/-- The complement of a retained mixing coefficient is nonnegative. -/
theorem complement_nonnegative (weight : MixingWeight) :
    0 ≤ weight.complement :=
  Fraction.Order.Arithmetic.sub_nonneg_direct weight.atMostOne

end

/-- The retained coefficient and its complement sum to one. -/
theorem coefficient_add_complement (weight : MixingWeight) :
    weight.coefficient + weight.complement = 1 := by
  unfold complement
  ring1

/-- Use the complementary coefficient as the mixing weight, retaining its interval certificates. -/
@[expose] def swap (weight : MixingWeight) : MixingWeight where
  coefficient := weight.complement
  nonnegative := weight.complement_nonnegative
  atMostOne := by
    unfold complement
    exact Fraction.Order.Arithmetic.sub_le_iff_le_add_direct.mpr (by
      have translated := Fraction.Order.Arithmetic.add_le_add_right_direct
        (weight.nonnegative) (1 : Fraction.Rational)
      calc
        (1 : Fraction.Rational) = 0 + (1 : Fraction.Rational) := (Fraction.zero_add _).symm
        _ ≤ _ + (1 : Fraction.Rational) := translated
        _ = (1 : Fraction.Rational) + _ := Fraction.add_comm _ _)

/-- Swapping a mixing weight selects its original complementary coefficient. -/
@[simp] theorem swap_coefficient (weight : MixingWeight) :
    weight.swap.coefficient = weight.complement := rfl

/-- The complement of a swapped mixing weight is its original coefficient. -/
@[simp] theorem swap_complement (weight : MixingWeight) :
    weight.swap.complement = weight.coefficient := by
  unfold swap complement
  ring1

end MixingWeight

namespace Distribution

/-- Concatenate the original left and right occurrence lists after scaling by the retained coefficient and its
complement.

Keep both occurrence orders and all repetitions. Their original unit-total certificates and the coefficient identity
certify the resulting distribution's unit total. -/
@[expose] def mixture {α : Type} (left right : Distribution α)
    (weight : MixingWeight) : Distribution α where
  atoms :=
    scaleAtoms weight.coefficient weight.nonnegative left.atoms ++
      scaleAtoms weight.complement weight.complement_nonnegative right.atoms
  total_one := by
    rw [totalWeight_append, totalWeight_scaleAtoms,
      totalWeight_scaleAtoms, left.total_one, right.total_one,
      mul_one, mul_one, weight.coefficient_add_complement]

/-- A mixture retains exactly the sum of the two input occurrence counts. -/
theorem mixture_atoms_length {α : Type} (left right : Distribution α)
    (weight : MixingWeight) :
    (left.mixture right weight).atoms.length =
      left.atoms.length + right.atoms.length := by
  simp only [-eq_self, -iff_self, mixture, List.Append.length_append, scaleAtoms_length]
  rfl

/-- A mixture's event probability is the retained weighted sum of the two original event probabilities. -/
theorem mixture_probability {α : Type} (left right : Distribution α)
    (weight : MixingWeight) (event : α → Bool) :
    (left.mixture right weight).probability event =
      weight.coefficient * left.probability event +
        weight.complement * right.probability event := by
  unfold mixture probability
  rw [eventWeight_append, eventWeight_scaleAtoms, eventWeight_scaleAtoms]

open Purelib.Data.Rat in
/-- A mixture's observable expectation is the retained weighted sum of the two original expectations. -/
theorem mixture_expectation {α : Type} (left right : Distribution α)
    (weight : MixingWeight) (value : α → Fraction.Rational) :
    (left.mixture right weight).expectation value =
      weight.coefficient * left.expectation value +
        weight.complement * right.expectation value := by
  unfold mixture expectation
  rw [expectationWeight_append, expectationWeight_scaleAtoms,
    expectationWeight_scaleAtoms]

/-- Swapping the two input distributions and complementing the coefficient preserves every event probability. -/
theorem mixture_swap_probability {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (event : α → Bool) :
    (left.mixture right weight).probability event =
      (right.mixture left weight.swap).probability event := by
  rw [left.mixture_probability right weight,
    right.mixture_probability left weight.swap]
  simp only [-eq_self, -iff_self, MixingWeight.swap_coefficient, MixingWeight.swap_complement]
  ring1

open Purelib.Data.Rat
/-- Swapping the two input distributions and complementing the coefficient preserves every observable expectation. -/
theorem mixture_swap_expectation {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (value : α → Fraction.Rational) :
    (left.mixture right weight).expectation value =
      (right.mixture left weight.swap).expectation value := by
  rw [left.mixture_expectation right weight,
    right.mixture_expectation left weight.swap]
  simp only [-eq_self, -iff_self, MixingWeight.swap_coefficient, MixingWeight.swap_complement]
  ring1

/-- Mixture variance equals the weighted component variances plus the coefficient-product times squared separation of
component means. -/
theorem mixture_variance {α : Type} (left right : Distribution α)
    (weight : MixingWeight) (value : α → Fraction.Rational) :
    (left.mixture right weight).variance value =
      weight.coefficient * left.variance value +
        weight.complement * right.variance value +
        weight.coefficient * weight.complement *
          (left.expectation value - right.expectation value) ^ 2 := by
  rw [(left.mixture right weight).variance_eq_secondMoment_sub_sq,
    left.variance_eq_secondMoment_sub_sq,
    right.variance_eq_secondMoment_sub_sq,
    left.mixture_expectation right weight,
    left.mixture_expectation right weight]
  unfold MixingWeight.complement
  ring1

end Distribution

end Purelib.Measure
