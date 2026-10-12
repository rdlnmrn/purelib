module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Riemann.Normalization.InverseRootComparison
public import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.Ring
public import Purelib.Riemann.Normalization.InverseRootPolynomial
meta import Purelib.Elab.ConstructiveInjectivity

@[expose] public section

/-!
# Computed sign alignment of finite inverse-root models

At a shared rational point, exact squared-norm comparison selects one of the
two signs of a second inverse-root model.  Its discrepancy is bounded by the
sum of the two residual budgets, relative to the first model's norm.  No exact
root or assumed agreement of sheet labels is used.  This is pointwise overlap
data; constancy along an edge and consistency around mesh cycles are separate.
-/

namespace Purelib.Riemann.Normalization.InverseModelOverlap

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical

section
open Purelib.Data
/-- Small inverse-root residual gives normalized value quadrance at least one third. -/
theorem normalized_value_lower {parameter value : Gaussian}
    (small : normSq (1 - parameter * value ^ 2) ≤ 1 / 16) :
    (1 / 3 : Coordinate) ≤ normSq parameter * normSq value ^ 2 := by
  have lower := Gaussian.Norm.Bounds.half_normSq_sub_le_normSq_sub (1 : Gaussian) (1 - parameter * value ^ 2)
  have identity : (1 : Gaussian) - (1 - parameter * value ^ 2) = parameter * value ^ 2 := by ring1
  rw [identity, Gaussian.Norm.Basic.normSq_mul, Gaussian.Power.normSq_pow, Gaussian.Norm.Basic.normSq_one] at lower
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at lower
  exact (show (1 / 3 : Coordinate) ≤ 1 / 2 - 1 / 16 by decide +kernel).trans
    ((Rat.Fraction.Order.Arithmetic.sub_le_sub_left_direct small _).trans lower)

/-- A value with inverse-root residual quadrance at most 1/16 is nonzero. -/
theorem inverse_value_ne_zero {parameter value : Gaussian}
    (small : normSq (1 - parameter * value ^ 2) ≤ 1 / 16) : value ≠ 0 := by
  intro zero
  have lower := normalized_value_lower small
  have zeroNorm : normSq parameter * normSq value ^ 2 = 0 := by rw [zero, Gaussian.Basic.Canonical.normSq_zero]; ring1
  rw [zeroNorm] at lower
  exact (not_lt_of_ge lower) (by decide : (0 : Coordinate) < 1 / 3)

end

set_option genInjectivity false in
/-- A cached choice of candidate sign with its exact value and nearest-sign comparison.

The retained Boolean and readback select either the original candidate or its negation; the chosen distance is no
greater than the opposite-sign distance. -/
structure SignAlignment (reference candidate : Gaussian) where
  /-- The retained bit selecting negation of the candidate. -/ flip : Bool
  /-- The cached sign-adjusted candidate value. -/ value : Gaussian
  /-- The cached value is the candidate with the retained sign choice applied. -/ value_eq : value = if flip then
    -candidate else candidate
  /-- The selected value is at least as close to the reference as its opposite. -/ nearest : normSq (reference - value)
    ≤ normSq (reference + value)

constructive_injectivity SignAlignment

namespace SignAlignment

variable {reference candidate : Gaussian}

/-- Compare exact rational quadrances and cache the nearest candidate sign. -/
def build (reference candidate : Gaussian) : SignAlignment reference candidate :=
  if nearest : normSq (reference - candidate) ≤ normSq (reference + candidate) then
    ⟨false, candidate, rfl, nearest⟩
  else
    ⟨true, -candidate, rfl, by
      have sum : reference - (-candidate) = reference + candidate := by ring1
      have difference : reference + (-candidate) = reference - candidate := by ring1
      rw [sum, difference]
      exact (le_of_not_ge nearest)⟩

/-- The sign-adjusted candidate has the same square as the original candidate. -/
theorem square_eq (alignment : SignAlignment reference candidate) : alignment.value ^ 2 = candidate ^ 2 := by
  rw [alignment.value_eq]
  cases alignment.flip
  · rfl
  · change (-candidate) ^ 2 = candidate ^ 2
    ring1

section
open Purelib.Data
/-- The sign-adjusted candidate has the same quadrance as the original candidate.

The retained flip selects the original candidate or its negation. Gaussian
quadrance is unchanged under that exact negation in the selected branch. -/
theorem norm_eq (alignment : SignAlignment reference candidate) : normSq alignment.value = normSq candidate := by
  rw [alignment.value_eq]
  cases alignment.flip with
  | false => exact Eq.refl _
  | true => exact Gaussian.Basic.Canonical.normSq_neg candidate

/-- The opposite-sign sum has quadrance at least the reference quadrance. -/
theorem sum_norm_lower (alignment : SignAlignment reference candidate) :
    normSq reference ≤ normSq (reference + alignment.value) := by
  apply Rat.Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2) ?_ (by decide)
  calc
    _ ≤ 2 * (normSq reference + normSq alignment.value) := by
      exact (by ring1 : normSq reference * 2 = 2 * normSq reference).trans_le
        (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (le_add_of_nonneg_right (Gaussian.Basic.Canonical.normSq_nonneg alignment.value)) (by decide))
    _ = normSq (reference - alignment.value) + normSq (reference + alignment.value) := by
      simp only [normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im]
      ring1
    _ ≤ normSq (reference + alignment.value) + normSq (reference + alignment.value) :=
      add_le_add alignment.nearest le_rfl
    _ = _ := by ring1

/-- The two retained inverse-root residuals bound the normalized nearest-sign discrepancy.

Factoring the difference of squares and using the opposite-sign lower bound gives twice the sum of residual allowances.
-/
theorem normalized_distance_le (alignment : SignAlignment reference candidate)
    {parameter : Gaussian} {leftError rightError : Coordinate}
    (leftResidual : normSq (1 - parameter * reference ^ 2) ≤ leftError)
    (rightResidual : normSq (1 - parameter * candidate ^ 2) ≤ rightError) :
    normSq parameter * normSq reference * normSq (reference - alignment.value) ≤
      2 * (leftError + rightError) := by
  have factor : parameter * ((reference - alignment.value) * (reference + alignment.value)) =
      (1 - parameter * alignment.value ^ 2) - (1 - parameter * reference ^ 2) := by ring1
  calc
    _ ≤ normSq parameter * normSq (reference + alignment.value) * normSq (reference - alignment.value) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct alignment.sum_norm_lower
          (Gaussian.Basic.Canonical.normSq_nonneg _))
        (Gaussian.Basic.Canonical.normSq_nonneg _)
    _ = normSq (parameter * ((reference - alignment.value) * (reference + alignment.value))) := by
      rw [Gaussian.Basic.Canonical.normSq_mul, Gaussian.Basic.Canonical.normSq_mul]
      ring1
    _ = normSq ((1 - parameter * alignment.value ^ 2) - (1 - parameter * reference ^ 2)) := congrArg normSq factor
    _ ≤ 2 * (normSq (1 - parameter * alignment.value ^ 2) + normSq (1 - parameter * reference ^ 2)) := by
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
        Gaussian.Norm.Bounds.normSq_sub_le_two (1 - parameter * alignment.value ^ 2) (1 - parameter * reference ^ 2)
    _ ≤ 2 * (rightError + leftError) := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (by rw [alignment.square_eq]; exact rightResidual) leftResidual) (by decide)
    _ = _ := by ring1

/-- The selected discrepancy is bounded by six times combined residual allowance times reference quadrance.

The reference residual allowance is at most 1/16; the estimate decreases with the two finite residual budgets. -/
theorem distance_le (alignment : SignAlignment reference candidate)
    {parameter : Gaussian} {leftError rightError : Coordinate}
    (leftResidual : normSq (1 - parameter * reference ^ 2) ≤ leftError)
    (rightResidual : normSq (1 - parameter * candidate ^ 2) ≤ rightError)
    (leftSmall : leftError ≤ 1 / 16) :
    normSq (reference - alignment.value) ≤ 6 * (leftError + rightError) * normSq reference := by
  have lower := normalized_value_lower (leftResidual.trans leftSmall)
  have normalized : (1 : Coordinate) ≤ 3 * (normSq parameter * normSq reference ^ 2) := by
    calc
      _ = 3 * (1 / 3 : Coordinate) := by decide
      _ ≤ _ := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lower (by decide)
  calc
    _ = normSq (reference - alignment.value) * 1 := by ring1
    _ ≤ normSq (reference - alignment.value) * (3 * (normSq parameter * normSq reference ^ 2)) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct normalized (Gaussian.Basic.Canonical.normSq_nonneg
        _)
    _ = (3 * normSq reference) * (normSq parameter * normSq reference * normSq (reference - alignment.value)) := by
      ring1
    _ ≤ (3 * normSq reference) * (2 * (leftError + rightError)) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (alignment.normalized_distance_le leftResidual rightResidual)
        (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Gaussian.Basic.Canonical.normSq_nonneg _))
    _ = _ := by ring1

/-- Under both 1/16 residual bounds, the selected candidate sign is strictly closer. -/
theorem distance_lt_opposite (alignment : SignAlignment reference candidate)
    {parameter : Gaussian} {leftError rightError : Coordinate}
    (leftResidual : normSq (1 - parameter * reference ^ 2) ≤ leftError)
    (rightResidual : normSq (1 - parameter * candidate ^ 2) ≤ rightError)
    (leftSmall : leftError ≤ 1 / 16) (rightSmall : rightError ≤ 1 / 16) :
    normSq (reference - alignment.value) < normSq (reference + alignment.value) := by
  have nonzero := inverse_value_ne_zero (leftResidual.trans leftSmall)
  have allowance : 6 * (leftError + rightError) ≤ (3 / 4 : Coordinate) :=
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add leftSmall rightSmall)
      (by decide)).trans_eq (by decide +kernel : (6 : Coordinate) * (1 / 16 + 1 / 16) = 3 / 4)
  calc
    _ ≤ 6 * (leftError + rightError) * normSq reference := alignment.distance_le leftResidual rightResidual leftSmall
    _ ≤ (3 / 4 : Coordinate) * normSq reference :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct allowance (Gaussian.Basic.Canonical.normSq_nonneg
        _)
    _ < 1 * normSq reference := Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      (by decide) (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using Gaussian.Norm.Basic.normSq_pos nonzero)
    _ = normSq reference := by ring1
    _ ≤ _ := alignment.sum_norm_lower

end

/-- Every valid nearest-sign certificate selects the same bit under the retained small residual bounds.

Both residual bounds are at most one sixteenth for the same parameter and
candidate. Opposite flip bits would contradict the strict nearest-sign distance. -/
theorem flip_unique (first second : SignAlignment reference candidate)
    {parameter : Gaussian} {leftError rightError : Coordinate}
    (leftResidual : normSq (1 - parameter * reference ^ 2) ≤ leftError)
    (rightResidual : normSq (1 - parameter * candidate ^ 2) ≤ rightError)
    (leftSmall : leftError ≤ 1 / 16) (rightSmall : rightError ≤ 1 / 16) : first.flip = second.flip := by
  by_cases same : first.flip = second.flip
  · exact same
  · have opposite : second.value = -first.value := by
      rw [first.value_eq, second.value_eq]
      cases leftFlip : first.flip <;> cases rightFlip : second.flip
      · exact (same (leftFlip.trans rightFlip.symm)).elim
      · exact Eq.refl _
      · change candidate = -(-candidate)
        ring1
      · exact (same (leftFlip.trans rightFlip.symm)).elim
    have nearest := second.nearest
    rw [opposite] at nearest
    have difference : reference - (-first.value) = reference + first.value := by ring1
    have sum : reference + (-first.value) = reference - first.value := by ring1
    rw [difference, sum] at nearest
    exact ((not_lt_of_ge nearest) (first.distance_lt_opposite leftResidual rightResidual leftSmall rightSmall)).elim

end SignAlignment

namespace Model

/-- Restrict an inverse-root model to a contained box while reusing both polynomial caches.

The value, residual and budget remain unchanged; containment transports the pointwise residual proof. -/
def restrictTo {polynomial : Polynomial} {outer inner : Box} (model : Model polynomial outer)
    (refines : inner.Refines outer) : Model polynomial inner where
  value := model.value
  residual := model.residual
  residual_eq := model.residual_eq
  bound := model.bound
  bound_nonnegative := model.bound_nonnegative
  bound_small := model.bound_small
  residualBound := fun point inside => model.residualBound point (refines.contains inside)

end Model

set_option genInjectivity false in
/-- Cached evaluations of two inverse-root models with a retained nearest-sign certificate.

Both evaluation equations refer to the same rational point and the original model polynomial caches. -/
structure OverlapSample {polynomial : Polynomial} {leftBox rightBox : Box}
    (left : Model polynomial leftBox) (right : Model polynomial rightBox) (point : Gaussian) where
  /-- The cached evaluation of the original left model. -/ leftValue : Gaussian
  /-- The left cache equals the left model polynomial at the retained point. -/ leftValue_eq : leftValue =
    left.value.eval point
  /-- The cached evaluation of the original right model. -/ rightValue : Gaussian
  /-- The right cache equals the right model polynomial at the retained point. -/ rightValue_eq : rightValue =
    right.value.eval point
  /-- The retained nearest-sign comparison of the two cached evaluations. -/ alignment : SignAlignment leftValue
    rightValue

constructive_injectivity OverlapSample

namespace OverlapSample

variable {polynomial : Polynomial} {leftBox rightBox : Box}
  {left : Model polynomial leftBox} {right : Model polynomial rightBox} {point : Gaussian}

/-- Evaluate both retained model polynomials once and cache their nearest-sign comparison. -/
def build (left : Model polynomial leftBox) (right : Model polynomial rightBox) (point : Gaussian) :
    OverlapSample left right point :=
  let leftValue := left.value.eval point
  let rightValue := right.value.eval point
  ⟨leftValue, rfl, rightValue, rfl, SignAlignment.build leftValue rightValue⟩

/-- At a shared interior point, the cached overlap discrepancy satisfies the relative residual bound. -/
theorem distance_le (sample : OverlapSample left right point)
    (leftInside : leftBox.Contains point) (rightInside : rightBox.Contains point) :
    normSq (sample.leftValue - sample.alignment.value) ≤
      6 * (left.bound + right.bound) * normSq sample.leftValue := by
  apply sample.alignment.distance_le (parameter := polynomial.eval point) ?_ ?_ left.bound_small
  · rw [sample.leftValue_eq, ← left.residual_eq]
    exact left.residualBound point leftInside
  · rw [sample.rightValue_eq, ← right.residual_eq]
    exact right.residualBound point rightInside

/-- At a shared interior point, the retained overlap sign is strictly closer than its opposite. -/
theorem distance_lt_opposite (sample : OverlapSample left right point)
    (leftInside : leftBox.Contains point) (rightInside : rightBox.Contains point) :
    normSq (sample.leftValue - sample.alignment.value) < normSq (sample.leftValue + sample.alignment.value) := by
  apply sample.alignment.distance_lt_opposite (parameter := polynomial.eval point) ?_ ?_ left.bound_small
    right.bound_small
  · rw [sample.leftValue_eq, ← left.residual_eq]
    exact left.residualBound point leftInside
  · rw [sample.rightValue_eq, ← right.residual_eq]
    exact right.residualBound point rightInside

open Purelib.Data in
/-- A common Gaussian numerator preserves the relative cached overlap bound. -/
theorem coefficient_distance_le (sample : OverlapSample left right point)
    (leftInside : leftBox.Contains point) (rightInside : rightBox.Contains point) (numerator : Gaussian) :
    normSq (numerator * sample.leftValue - numerator * sample.alignment.value) ≤
      6 * (left.bound + right.bound) * normSq (numerator * sample.leftValue) := by
  have identity : numerator * sample.leftValue - numerator * sample.alignment.value =
      numerator * (sample.leftValue - sample.alignment.value) := by ring1
  rw [identity, Gaussian.Basic.Canonical.normSq_mul, Gaussian.Basic.Canonical.normSq_mul]
  exact (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (sample.distance_le leftInside rightInside) (Gaussian.Basic.Canonical.normSq_nonneg _)).trans_eq (by ring1)

end OverlapSample

end Purelib.Riemann.Normalization.InverseModelOverlap
