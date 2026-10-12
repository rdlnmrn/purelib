module

import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.SampleCarrier
public import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

/-!
# Progressive finite integration with Gaussian coefficients

This is the period-facing integration kernel.  Every model is still a finite
list of rationally parameterized cells, but its local polynomial coefficients
are Gaussian rationals.  Hence a cell can approximate a genuinely complex
coefficient before multiplication by the complex path displacement.
-/

namespace Purelib.Integration.Program.Gaussian.Basic
namespace RefinementProgram

open Purelib.Approximation.Rational in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Integration.Program in
set_option genInjectivity false in
/-- A retained model sequence whose samples add two original program samples and whose allowances satisfy their combined
geometric bound. -/
structure SumModels (left right :
  Gaussian.Basic.RefinementProgram) where
  /-- The retained path-model sequence for the original pair of programs. -/ model : Nat -> Basic.PathModel
  /-- Each retained model sample equals the sum of the original two program samples. -/ integral_eq : forall index,
    (model index).integralSample =
      (left.model index).integralSample + (right.model index).integralSample
  /-- Each model allowance obeys quarter-radius decay at twice the sum of the original error scales. -/ aggregate_le :
    forall index,
    (model index).aggregateAllowance <=
      Geometric.Basic.quarterRadius
        (2 * (left.errorScale + right.errorScale)) index

constructive_injectivity SumModels

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Program in
/-- Build the sum program from the exact retained sum models and both original refinement programs.

The error and center bounds are twice the sum of the respective original bounds; the supplied models keep their exact
sample and allowance certificates. -/
@[expose] def add (left right :
  Gaussian.Basic.RefinementProgram) (models : SumModels left right) :
    Gaussian.Basic.RefinementProgram where
  model := models.model
  errorScale := 2 * (left.errorScale + right.errorScale)
  errorScale_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg left.errorScale_nonneg right.errorScale_nonneg)
  modelAllowance_le := models.aggregate_le
  later_close := by
    intro earlier later order
    rw [models.integral_eq, models.integral_eq]
    have identity :
        ((left.model later).integralSample +
              (right.model later).integralSample) -
            ((left.model earlier).integralSample +
              (right.model earlier).integralSample) =
          ((left.model later).integralSample -
              (left.model earlier).integralSample) +
            ((right.model later).integralSample -
              (right.model earlier).integralSample) := by
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im] <;> ring1
    rw [identity]
    calc
      Basic.Canonical.normSq
          (((left.model later).integralSample -
              (left.model earlier).integralSample) +
            ((right.model later).integralSample -
              (right.model earlier).integralSample)) <=
          2 *
            (Basic.Canonical.normSq ((left.model later).integralSample -
                (left.model earlier).integralSample) +
              Basic.Canonical.normSq ((right.model later).integralSample -
                (right.model earlier).integralSample)) :=
        by simpa only [Norm.Basic.normSq_eq_canonical] using
          Norm.Bounds.normSq_add_le_two ((left.model later).integralSample - (left.model earlier).integralSample)
            ((right.model later).integralSample - (right.model earlier).integralSample)
      _ <= 2 *
            (Geometric.Basic.quarterRadius left.errorScale earlier +
              Geometric.Basic.quarterRadius right.errorScale earlier) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add (left.later_close order) (right.later_close order))
          (by decide)
      _ = Geometric.Basic.quarterRadius
            (2 * (left.errorScale + right.errorScale)) earlier := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
  centerBound := 2 * (left.centerBound + right.centerBound)
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg left.centerBound_nonneg right.centerBound_nonneg)
  sample_bounded := by
    intro index
    rw [models.integral_eq]
    have scalar := Norm.Bounds.normSq_add_le_two
      (left.model index).integralSample (right.model index).integralSample
    rw [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (left.sample_bounded index)
          (right.sample_bounded index)) (by decide))

open Purelib.Integration.Program in
/-- Every retained sum-program sample equals the sum of the two original stage samples. -/
@[simp] theorem add_integralSample (left right :
  Gaussian.Basic.RefinementProgram)
    (models : SumModels left right) (index : Nat) :
    ((add left right models).model index).integralSample =
      (left.model index).integralSample +
        (right.model index).integralSample :=
  models.integral_eq index

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Program in
/-- Build exact single-cell carriers for products of the two original program samples.

The geometric error keeps both error-times-opposite-center contributions, while the center bound is the product of the
two original bounds. -/
@[expose] def multiply (left right :
  Gaussian.Basic.RefinementProgram) : Gaussian.Basic.RefinementProgram where
  model := fun index => Gaussian.Basic.RefinementProgram.productSamplePath (left.model index) (right.model index)
  errorScale := 2 *
    (left.errorScale * right.centerBound +
      left.centerBound * right.errorScale)
  errorScale_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          left.errorScale_nonneg right.centerBound_nonneg)
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          left.centerBound_nonneg right.errorScale_nonneg))
  modelAllowance_le := by
    intro index
    rw [Gaussian.Basic.RefinementProgram.productSamplePath_aggregateAllowance]
    exact Geometric.Basic.quarterRadius_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (by decide : (0 : Fraction.Rational) <= 2)
        (add_nonneg
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            left.errorScale_nonneg right.centerBound_nonneg)
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            left.centerBound_nonneg right.errorScale_nonneg))) index
  later_close := by
    intro earlier later order
    let leftLater := (left.model later).integralSample
    let leftEarlier := (left.model earlier).integralSample
    let rightLater := (right.model later).integralSample
    let rightEarlier := (right.model earlier).integralSample
    have productIdentity :
        leftLater * rightLater - leftEarlier * rightEarlier =
          (leftLater - leftEarlier) * rightLater +
            leftEarlier * (rightLater - rightEarlier) := by
      apply Basic.ext <;>
        simp only [leftLater, leftEarlier, rightLater, rightEarlier,
          Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.add_re, Basic.add_im] <;>
        ring1
    have firstBound :
        Basic.Canonical.normSq (leftLater - leftEarlier) * Basic.Canonical.normSq rightLater <=
          Geometric.Basic.quarterRadius left.errorScale earlier *
            right.centerBound := by
      calc
        Basic.Canonical.normSq (leftLater - leftEarlier) * Basic.Canonical.normSq rightLater <=
            Geometric.Basic.quarterRadius left.errorScale earlier *
              Basic.Canonical.normSq rightLater :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (left.later_close order) (Basic.Canonical.normSq_nonneg rightLater)
        _ <= Geometric.Basic.quarterRadius left.errorScale earlier *
              right.centerBound :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (right.sample_bounded later)
            (Geometric.Basic.quarterRadius_nonneg
              left.errorScale_nonneg earlier)
    have secondBound :
        Basic.Canonical.normSq leftEarlier * Basic.Canonical.normSq (rightLater - rightEarlier) <=
          left.centerBound *
            Geometric.Basic.quarterRadius right.errorScale earlier := by
      calc
        Basic.Canonical.normSq leftEarlier * Basic.Canonical.normSq (rightLater - rightEarlier) <=
            Basic.Canonical.normSq leftEarlier *
              Geometric.Basic.quarterRadius right.errorScale earlier :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (right.later_close order) (Basic.Canonical.normSq_nonneg leftEarlier)
        _ <= left.centerBound *
              Geometric.Basic.quarterRadius right.errorScale earlier :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (left.sample_bounded earlier)
            (Geometric.Basic.quarterRadius_nonneg
              right.errorScale_nonneg earlier)
    rw [Gaussian.Basic.RefinementProgram.productSamplePath_integralSample,
      Gaussian.Basic.RefinementProgram.productSamplePath_integralSample,
      productIdentity]
    calc
      Basic.Canonical.normSq ((leftLater - leftEarlier) * rightLater +
          leftEarlier * (rightLater - rightEarlier)) <=
          2 *
            (Basic.Canonical.normSq ((leftLater - leftEarlier) * rightLater) +
              Basic.Canonical.normSq (leftEarlier * (rightLater - rightEarlier))) :=
        by simpa only [Norm.Basic.normSq_eq_canonical] using
          Norm.Bounds.normSq_add_le_two ((leftLater - leftEarlier) * rightLater) (leftEarlier * (rightLater -
            rightEarlier))
      _ = 2 *
            (Basic.Canonical.normSq (leftLater - leftEarlier) * Basic.Canonical.normSq rightLater +
              Basic.Canonical.normSq leftEarlier * Basic.Canonical.normSq (rightLater - rightEarlier)) := by
        rw [Basic.Canonical.normSq_mul, Basic.Canonical.normSq_mul]
      _ <= 2 *
            (Geometric.Basic.quarterRadius left.errorScale earlier *
                right.centerBound +
              left.centerBound *
                Geometric.Basic.quarterRadius right.errorScale earlier) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstBound secondBound) (by decide)
      _ = Geometric.Basic.quarterRadius
            (2 *
              (left.errorScale * right.centerBound +
                left.centerBound * right.errorScale)) earlier := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
  centerBound := left.centerBound * right.centerBound
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct left.centerBound_nonneg
      right.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [Gaussian.Basic.RefinementProgram.productSamplePath_integralSample, Basic.Canonical.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct
      (left.sample_bounded index) (right.sample_bounded index)
      (Basic.Canonical.normSq_nonneg (right.model index).integralSample)
      left.centerBound_nonneg

open Purelib.Integration.Program in
/-- Every product-program sample equals the product of the two exact original stage samples. -/
@[simp] theorem multiply_integralSample (left right
  : Gaussian.Basic.RefinementProgram)
    (index : Nat) :
    ((multiply left right).model index).integralSample =
      (left.model index).integralSample *
        (right.model index).integralSample :=
  Gaussian.Basic.RefinementProgram.productSamplePath_integralSample _ _
end RefinementProgram

end Purelib.Integration.Program.Gaussian.Basic

end
