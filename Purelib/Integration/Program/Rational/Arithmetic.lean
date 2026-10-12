module

import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Rational.Path.Basic
public import Purelib.Integration.Polynomial.Rational.Path.Scale
public import Purelib.Integration.Program.Rational.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Polynomial.Rational.Path.Allowance
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

/-!
# General certified integration by finite path refinements

An integrand is supplied operationally: at each natural refinement it returns
one finite path of rational polynomial cell models and finite rational sample
certificates.  The integration program sums the exact polynomial cell
integrals.  A rational geometric modulus and a finite later-refinement
certificate turn those displayed sums into an ordinary productive CCL name.

There is no measure, completed partition, function-as-an-infinite-set, or
infinitesimal.  The only universal refinements are natural-number calls to the
supplied finite program.
-/

namespace Purelib.Integration.Program.Rational
section RefinementProgram

open Purelib.Data.Gaussian in
/-- The squared norm of the original Gaussian sum is at most twice the sum of the original squared norms. -/
private theorem Arithmetic.canonicalNormSqAddLeTwo (left right :
  Basic.Canonical) :
    Basic.Canonical.normSq (left + right) ≤ 2 * (Basic.Canonical.normSq left + Basic.Canonical.normSq right) := by
  simpa only [Norm.Basic.normSq_eq_canonical] using Norm.Bounds.normSq_add_le_two left right

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Scaling the original Gaussian value multiplies its squared norm by the rational factor squared. -/
private theorem Arithmetic.canonicalNormSqScale (factor : Fraction.Rational)
  (point : Basic.Canonical) :
    Basic.Canonical.normSq (Scale.scale factor point) = factor ^ 2 * Basic.Canonical.normSq point := by
  simpa only [Norm.Basic.normSq_eq_canonical] using Scale.normSq_scale factor point

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Rational.Path in
open Purelib.Integration.Program.Rational in
/-- Scale every original rational-polynomial model's integrand by the retained rational factor.

The squared factor scales both error and center bounds; all sample and allowance certificates use the same exact
original stage models. -/
@[expose] def Basic.RefinementProgram.scale (factor : Fraction.Rational)
  (program : Basic.RefinementProgram) :
    Basic.RefinementProgram :=
  { model := fun index => (program.model index).scaleIntegrand factor
    errorScale := factor ^ 2 * program.errorScale
    errorScale_nonneg :=
      Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.sq_nonneg_direct factor)
        program.errorScale_nonneg
    modelAllowance_le := by
      intro index
      rw [Basic.PathModel.aggregateAllowance_scaleIntegrand,
        Geometric.Basic.quarterRadius_eq_mul_pow]
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (program.modelAllowance_le index)
            (Fraction.Order.Arithmetic.sq_nonneg_direct factor)
      rw [Geometric.Basic.quarterRadius_eq_mul_pow] at scaled
      simpa only [Fraction.Field.mul_assoc] using scaled
    later_close := by
      intro earlier later order
      rw [Basic.PathModel.integralSample_scaleIntegrand,
        Basic.PathModel.integralSample_scaleIntegrand]
      have identity :
          Scale.scale factor
                (program.model later).integralSample -
              Scale.scale factor
                (program.model earlier).integralSample =
            Scale.scale factor
              ((program.model later).integralSample -
                (program.model earlier).integralSample) := by
        apply Basic.ext <;>
          simp only [Scale.scale_re,
            Scale.scale_im, Basic.sub_re, Basic.sub_im] <;> ring1
      rw [identity, Arithmetic.canonicalNormSqScale,
        Geometric.Basic.quarterRadius_eq_mul_pow]
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (program.later_close order)
            (Fraction.Order.Arithmetic.sq_nonneg_direct factor)
      rw [Geometric.Basic.quarterRadius_eq_mul_pow] at scaled
      simpa only [Fraction.Field.mul_assoc] using scaled
    centerBound := factor ^ 2 * program.centerBound
    centerBound_nonneg :=
      Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.sq_nonneg_direct factor)
        program.centerBound_nonneg
    sample_bounded := by
      intro index
      rw [Basic.PathModel.integralSample_scaleIntegrand,
        Arithmetic.canonicalNormSqScale]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (program.sample_bounded index)
          (Fraction.Order.Arithmetic.sq_nonneg_direct factor) }

open Purelib.Data.Rat in
open Purelib.Integration.Program.Rational in
/-- The scaled program model is the original stage model with its integrand scaled by the retained factor. -/
@[simp] theorem Basic.RefinementProgram.scale_model (factor :
  Fraction.Rational)
    (program : Basic.RefinementProgram) (index : Nat) :
    (Basic.RefinementProgram.scale factor program).model index =
      (program.model index).scaleIntegrand factor :=
  rfl

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Rational.Path in
open Purelib.Integration.Program.Rational in
/-- The scaled stage sample is the exact rational scaling of the original stage sample. -/
theorem Basic.RefinementProgram.scale_integralSample (factor :
  Fraction.Rational)
    (program : Basic.RefinementProgram) (index : Nat) :
    ((Basic.RefinementProgram.scale factor program).model index).integralSample =
      Scale.scale factor
        (program.model index).integralSample :=
  Basic.PathModel.integralSample_scaleIntegrand factor (program.model index)

open Purelib.Approximation.Rational in
open Purelib.Integration.Polynomial.Rational.Path in
open Purelib.Integration.Program.Rational in
set_option genInjectivity false in
/-- A retained model sequence realizing the samplewise sum of two original rational programs.

Its exact sample equalities and aggregate allowances use the two original model sequences and twice their combined error
scale. -/
structure Basic.RefinementProgram.SumModels (left right :
  Basic.RefinementProgram) where
  /-- The retained path-model sequence realizing the original pair's sample sum. -/ model : Nat → Basic.PathModel
  /-- Each retained model sample equals the two original samples' sum. -/ integral_eq : ∀ index,
    (model index).integralSample =
      (left.model index).integralSample + (right.model index).integralSample
  /-- Each retained sum model satisfies the combined geometric allowance bound. -/ aggregate_le : ∀ index,
    (model index).aggregateAllowance ≤
      Geometric.Basic.quarterRadius
        (2 * (left.errorScale + right.errorScale)) index

constructive_injectivity Basic.RefinementProgram.SumModels

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Program.Rational in
/-- Build the sum program from the two original rational programs and retained sum models.

The returned program reuses the supplied models, with error and center scales twice the sums of the respective original
scales. -/
@[expose] def Basic.RefinementProgram.add (left right :
  Basic.RefinementProgram) (models : Basic.RefinementProgram.SumModels left right) :
    Basic.RefinementProgram :=
  { model := models.model
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
                (right.model earlier).integralSample)) ≤
            2 *
              (Basic.Canonical.normSq ((left.model later).integralSample -
                  (left.model earlier).integralSample) +
                Basic.Canonical.normSq ((right.model later).integralSample -
                  (right.model earlier).integralSample)) :=
          Arithmetic.canonicalNormSqAddLeTwo _ _
        _ ≤ 2 *
              (Geometric.Basic.quarterRadius
                  left.errorScale earlier +
                Geometric.Basic.quarterRadius
                  right.errorScale earlier) :=
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
      exact (Arithmetic.canonicalNormSqAddLeTwo _ _).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add (left.sample_bounded index)
            (right.sample_bounded index)) (by decide)) }

open Purelib.Integration.Program.Rational in
/-- Every retained sum-program sample equals the sum of the two exact original stage samples. -/
@[simp] theorem Basic.RefinementProgram.add_integralSample (left right :
  Basic.RefinementProgram)
    (models : Basic.RefinementProgram.SumModels left right) (index : Nat) :
    ((Basic.RefinementProgram.add left right models).model index).integralSample =
      (left.model index).integralSample +
        (right.model index).integralSample :=
  models.integral_eq index
end RefinementProgram

end Purelib.Integration.Program.Rational

end
