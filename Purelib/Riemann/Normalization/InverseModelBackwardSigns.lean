module
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Riemann.Normalization.InverseModelRefinementSigns
import Purelib.Tactic.Ring
public import Purelib.Riemann.Normalization.InverseModelOverlapCocycle

open Purelib.Data.Rat.Fraction.Order

@[expose] public section

/-!
# Recover the sign of an already retained coarse polynomial

A Newton correction moves by at most one sixty-fourth of the squared norm
of its input. This sharper, one-sided estimate transfers agreement with a
cocycle-ready model backwards through two corrections. Existing primitive
requests may therefore keep index zero or one: the comparison does not
rebuild their polynomial data merely to satisfy the cocycle index floor.
-/

section

open Purelib.Data.Rat

open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial

namespace Purelib.Riemann.Normalization.InverseModelBackwardSigns

open Purelib.Data in
/-- A candidate within the reference norm is nearer to the reference than to its negative. -/
private theorem
  nearest_of_close
    {reference candidate : Gaussian}
    (close : normSq (reference - candidate) ≤ normSq reference) :
    normSq (reference - candidate) ≤ normSq (reference + candidate) := by
  apply Arithmetic.le_of_add_le_add_right_direct (c := normSq (reference - candidate))
  calc
    _ = 2 * normSq (reference - candidate) := by ring1
    _ ≤ 2 * normSq reference := Arithmetic.mul_le_mul_of_nonneg_left_direct close (by decide)
    _ ≤ 2 * (normSq reference + normSq candidate) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (le_add_of_nonneg_right (normSq_nonneg _)) (by decide)
    _ = _ := by
      simp only [normSq, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im];
      ring1

end Purelib.Riemann.Normalization.InverseModelBackwardSigns

section

variable {polynomial : Polynomial} {box otherBox : Box}

namespace Purelib.Riemann.Normalization.InverseModelBackwardSigns.Model

open Purelib.Riemann in
open Purelib.Data in
open Purelib.Polynomial in
/-- One Newton correction moves by at most one sixty-fourth of the original squared norm.

The point lies in the model box, where the retained residual bound controls the exact correction factor. -/
private theorem
  step_distance_le
    (model : Model polynomial box) {point : Gaussian} (inside : box.Contains point) :
    normSq (model.value.eval point - model.step.value.eval point) ≤ (1 / 64 : Fraction.Rational) * normSq
      (model.value.eval point) := by
  have correctionEq : model.step.value.eval point = model.value.eval point * (1 + half * model.residual.eval point) :=
    by
    dsimp only [InverseRootPolynomial.Model.step]
    rewrite [eval_mul, eval_add,
      eval_constant, eval_scale]
    exact Eq.refl _
  rw [correctionEq]
  have difference : model.value.eval point - model.value.eval point * (1 + half * model.residual.eval point) =
      -(model.value.eval point * (half * model.residual.eval point)) := by ring1
  rw [difference, normSq_neg, normSq_mul,
    normSq_mul, show normSq half = (1 / 4 : Fraction.Rational) by decide]
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      ((model.residualBound point inside).trans model.bound_small) (by decide : (0 : Fraction.Rational) ≤ 1 / 4))
    (normSq_nonneg _)).trans_eq (by
      rw [show (1 / 4 : Fraction.Rational) * (1 / 16) = 1 / 64 by decide +kernel]
      ring1)

open Purelib.Riemann in
open Purelib.Data in
/-- Transport agreement with an overlap-ready model back across one retained Newton step.

At a point in both model boxes, the correction's small displacement preserves nearestness without executing an
additional refinement. -/
theorem
  nearest_before_step
    (model : Model polynomial box) (other : OverlapReady polynomial otherBox)
    {point : Gaussian} (inside : box.Contains point) (otherInside : otherBox.Contains point)
    (nearest : normSq (model.step.value.eval point - other.model.value.eval point) ≤
      normSq (model.step.value.eval point + other.model.value.eval point)) :
    normSq (model.value.eval point - other.model.value.eval point) ≤
      normSq (model.value.eval point + other.model.value.eval point) := by
  let reference := model.value.eval point
  let middle := model.step.value.eval point
  let candidate := other.model.value.eval point
  have firstDistance : normSq (reference - middle) ≤ (1 / 64 : Fraction.Rational) * normSq reference :=
    step_distance_le model inside
  let alignment : SignAlignment middle candidate := ⟨false, candidate, rfl, nearest⟩
  have distance := alignment.distance_le (parameter := polynomial.eval point)
    (leftError := model.step.bound) (rightError := other.model.bound)
    (by rw [← model.step.residual_eq]; exact model.step.residualBound point inside)
    (by rw [← other.model.residual_eq]; exact other.model.residualBound point otherInside) model.step.bound_small
  have stepSmall : model.step.bound ≤ (1 / 64 : Fraction.Rational) := by
    change model.bound / 4 ≤ 1 / 64
    apply (Field.div_le_iff_pos (by decide : (0 : Fraction.Rational) < 4)).mpr
    exact model.bound_small.trans_eq (by decide +kernel : (1 / 16 : Fraction.Rational) = (1 / 64) * 4)
  have secondDistance : normSq (middle - candidate) ≤ (15 / 128 : Fraction.Rational) * normSq middle :=
    distance.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add stepSmall other.small) (by
        decide)).trans_eq
        (by decide +kernel : (6 : Fraction.Rational) * (1 / 64 + 1 / 256) = 15 / 128))
          (normSq_nonneg _))
  have middleNorm : normSq middle ≤ 3 * normSq reference := by
    have identity : (reference - middle) - reference = -middle := by ring1
    have bound := Gaussian.Norm.Bounds.normSq_sub_le_two (reference - middle) reference
    rw [Gaussian.Norm.Basic.normSq_eq_canonical, Gaussian.Norm.Basic.normSq_eq_canonical,
      Gaussian.Norm.Basic.normSq_eq_canonical] at bound
    rw [identity, normSq_neg] at bound
    calc
      _ ≤ 2 * (normSq (reference - middle) + normSq reference) := bound
      _ ≤ 2 * ((1 / 64 : Fraction.Rational) * normSq reference + normSq reference) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add firstDistance le_rfl) (by decide)
      _ = (2 * (1 / 64 + 1) : Fraction.Rational) * normSq reference := by ring1
      _ ≤ _ := Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel)
        (normSq_nonneg _)
  apply nearest_of_close
  calc
    _ ≤ 2 * (normSq (reference - middle) + normSq (middle - candidate)) := by
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
    _ ≤ 2 * ((1 / 64 : Fraction.Rational) * normSq reference + (15 / 128 : Fraction.Rational) * normSq middle)
      :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add firstDistance secondDistance) (by
        decide)
    _ ≤ 2 * ((1 / 64 : Fraction.Rational) * normSq reference + (15 / 128 : Fraction.Rational) * (3 * normSq
      reference)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add le_rfl (Arithmetic.mul_le_mul_of_nonneg_left_direct middleNorm
          (by decide +kernel))) (by decide)
    _ = (2 * (1 / 64 + (15 / 128) * 3) : Fraction.Rational) * normSq reference := by ring1
    _ = (47 / 64 : Fraction.Rational) * normSq reference := by
      rw [show (2 : Fraction.Rational) * (1 / 64 + (15 / 128) * 3) = 47 / 64 by decide +kernel]
    _ ≤ 1 * normSq reference := Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel)
      (normSq_nonneg _)
    _ = _ := by ring1

end Purelib.Riemann.Normalization.InverseModelBackwardSigns.Model

end

namespace Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial.OverlapReady

open Purelib.Riemann in
/-- Recover the original model's sheet agreement from agreement after two Newton steps.

The other model retains its overlap-ready bound and the point lies in both boxes; two backward comparisons preserve the
original cached polynomial. -/
theorem
  nearest_before_two_steps
  {polynomial : Polynomial} {leftBox rightBox : Box}
    (left : OverlapReady polynomial leftBox) (right : Model polynomial rightBox) {point : Gaussian}
    (leftInside : leftBox.Contains point) (rightInside : rightBox.Contains point)
    (nearest : normSq (left.model.value.eval point - right.step.step.value.eval point) ≤
      normSq (left.model.value.eval point + right.step.step.value.eval point)) :
    normSq (left.model.value.eval point - right.value.eval point) ≤ normSq (left.model.value.eval point +
      right.value.eval point) := by
  let reverse : SignAlignment (left.model.value.eval point) (right.step.step.value.eval point) :=
    ⟨false, right.step.step.value.eval point, rfl, nearest⟩
  have middle := (InverseModelBackwardSigns.Model.nearest_before_step right.step) left rightInside
    leftInside (InverseModelRefinementSigns.SignAlignment.reverse reverse).nearest
  have first := (InverseModelBackwardSigns.Model.nearest_before_step right) left rightInside leftInside
    middle
  let forward : SignAlignment (right.value.eval point) (left.model.value.eval point) :=
    ⟨false, left.model.value.eval point, rfl, first⟩
  exact (InverseModelRefinementSigns.SignAlignment.reverse forward).nearest

end Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial.OverlapReady

end

-- Keep the original public theorem owner available to namespace openings.
