module
public import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Cell.Source.Polynomial
public import Purelib.Polynomial.Ascending.Gaussian.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Antiderivative
import Purelib.Polynomial.Ascending.Gaussian.Integral
import Purelib.Data.List.Reverse
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.RationalEmbedding

/-!
# Original Gaussian polynomial samples in source-linked enclosures

The original ascending Gaussian coefficient table is converted to the
existing dense primitive certificate. Exact evaluation and antiderivative
readbacks identify its endpoint increment with the original unit cell's
integral sample; the source-frontier theorem proves its admission.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Continuous

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian.Dense
open Purelib.Polynomial.Dense.Gaussian.Primitive

/-- The original Gaussian polynomial's real reading at a rational unit parameter. -/
@[expose] def source (polynomial : Ascending.Gaussian.CoefficientPolynomial)
    (point : Fraction.Rational) : Fraction.Rational :=
  (Ascending.Gaussian.Evaluation.eval polynomial (RationalEmbedding.realPoint point)).re

/-- The closed unit real segment as a finite Gaussian box. -/
@[expose] def unitBox : Box := ⟨0, 1, 0, 0, by decide, le_rfl⟩

/-- The retained Gaussian unit box contains every original rational unit point. -/
theorem unitBox_contains (point : Fraction.Rational) (lower : 0 ≤ point) (upper : point ≤ 1) :
    unitBox.Contains (RationalEmbedding.realPoint point) := ⟨lower, upper, le_rfl, le_rfl⟩

/-- The original polynomial's exact unit cell, with its own coefficient table and integral computation. -/
@[expose] def model (polynomial : Ascending.Gaussian.CoefficientPolynomial) : Cell.Basic.CellModel :=
  Cell.Basic.CellModel.exact 0 1 polynomial

/-- The original polynomial's dense finite primitive certificate on the unit box. -/
@[expose] def primitive (polynomial : Ascending.Gaussian.CoefficientPolynomial) :
    Certificate.DensePrimitive (Evaluation.toDense polynomial) unitBox :=
  Certificate.DensePrimitive.ofPolynomial (Evaluation.toDense polynomial) unitBox

/-- The retained dense primitive evaluates as the original ascending antiderivative. -/
theorem primitive_eval (polynomial : Ascending.Gaussian.CoefficientPolynomial) (point : Basic.Canonical) :
    (primitive polynomial).value.eval point =
      Ascending.Gaussian.Evaluation.eval (Ascending.Gaussian.Antiderivative.antiderivative polynomial) point := by
  change (Dense.Gaussian.Antiderivative.denseAntiderivative
    (Evaluation.toDense polynomial)).eval point = _
  unfold Dense.Gaussian.Antiderivative.denseAntiderivative Evaluation.toDense
  rw [Purelib.Data.List.Reverse.reverse_reverse]
  exact Evaluation.toDense_eval
    (Ascending.Gaussian.Antiderivative.antiderivative polynomial) point

/-- The actual original Gaussian unit-cell sample is the retained primitive's endpoint increment. -/
theorem model_sample_re (polynomial : Ascending.Gaussian.CoefficientPolynomial) :
    (model polynomial).integralSample.re =
      ((primitive polynomial).value.eval (RationalEmbedding.realPoint 1)).re -
        ((primitive polynomial).value.eval (RationalEmbedding.realPoint 0)).re := by
  rw [model, Cell.Basic.CellModel.exact_integralSample]
  have displacement : (1 : Basic.Canonical) - 0 = 1 := by rw [Basic.sub_zero]
  rw [displacement, Basic.one_mul]
  unfold Ascending.Gaussian.Integral.definiteIntegral
  rw [Basic.sub_re, primitive_eval, primitive_eval]
  rfl

/-- Scaling the original polynomial scales its exact unit-cell integral sample. -/
theorem model_sample_scale (factor : Basic.Canonical) (polynomial : Ascending.Gaussian.CoefficientPolynomial) :
    (model (Ascending.Gaussian.Arithmetic.scale factor polynomial)).integralSample =
      factor * (model polynomial).integralSample := by
  unfold model
  rw [Cell.Basic.CellModel.exact_integralSample, Cell.Basic.CellModel.exact_integralSample]
  have displacement : (1 : Basic.Canonical) - 0 = 1 := by rw [Basic.sub_zero]
  rw [displacement, Basic.one_mul, Ascending.Gaussian.Integral.definiteIntegral_scale, Basic.one_mul]

/-- Every pointwise-matching source frontier contains the original Gaussian polynomial unit-cell sample.

The supplied frontier uses exactly the polynomial's rational real-coordinate
readings. Its original ranges and partition derive admission of the original
cell's exact integral sample, for any finite coefficient table. -/
theorem model_sample_contains_of_eq (polynomial : Ascending.Gaussian.CoefficientPolynomial)
    {reading : Fraction.Rational → Fraction.Rational} (frontier : SourceFrontier reading)
    (same : ∀ point, 0 ≤ point → point ≤ 1 → reading point = source polynomial point) :
    (integralBound frontier.cells).Contains (model polynomial).integralSample.re := by
  have admitted := SourceFrontier.Polynomial.integral_contains (primitive polynomial) frontier unitBox_contains
    (fun point lower upper => (same point lower upper).trans (congrArg Basic.Canonical.re
      (Evaluation.toDense_eval polynomial (RationalEmbedding.realPoint point))).symm)
  rw [model_sample_re]
  exact admitted

/-- Every frontier for the original Gaussian polynomial readings contains its original unit-cell sample. -/
theorem model_sample_contains (polynomial : Ascending.Gaussian.CoefficientPolynomial)
    (frontier : SourceFrontier (source polynomial)) :
    (integralBound frontier.cells).Contains (model polynomial).integralSample.re :=
  model_sample_contains_of_eq polynomial frontier (fun _ _ _ => rfl)

end Purelib.Integration.Polynomial.Gaussian.Continuous

end
