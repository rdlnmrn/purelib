module
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Dense.Derivative
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FactorBounds
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Normalization.InverseModelDifferentialResidual
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

public section

/-!
# Uniform geometric error of the cap comparison polynomial

Pay the regular root residual and both inverse-root differential residuals
with fixed coordinate, numerator, inverse and cap-factor ceilings. The
resulting scale is computed before the Newton index and controls every
point in the intersection of the original cap and local reciprocal boxes.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ComparisonBounds

open Purelib
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FactorBounds
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Polynomial
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Riemann.Comparison
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison
open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback (Preparation Sample)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds RegionClearance)
open Purelib.Riemann.Normalization.InverseModelDifferentialResidual (differentialResidual)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Model half)
open Purelib.Polynomial.Dense.Basic.DensePolynomial (constant)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {localBox :
    Purelib.Geometry.Rational.Box}
  {initial : Model
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve) localBox}

set_option genInjectivity false in
/-- Cached reciprocal and cap-factor ceilings for the original differential comparison.

The exact collar-box coordinate bound and combined error scale are retained with their original model and clearance
owners. -/
structure Bounds (preparation : PolynomialPullback.Preparation cap initial)
    (clearance : PrimitiveEdgeComparison.RegionClearance (HyperellipticReciprocal.polynomial curve) localBox)
      (differential : Differentials.Basic.Differential genus) where
  /-- The retained overlap bounds for the original reciprocal primitive model with unit numerator bound. -/ reciprocal :
    PrimitiveEdgeComparison.PrimitiveOverlapBounds clearance (DensePolynomial.constant 1)
  /-- The retained regular-factor bounds for the original cap differential. -/ factor : FactorBounds cap
    differential
  /-- The cached squared-norm ceiling of the original collar box. -/ pointUpper : InverseRootPolynomial.Coordinate
  /-- The retained point ceiling is exactly the original collar-box squared-norm bound. -/ pointUpper_eq : pointUpper =
    collar.box.normSqBound
  /-- The retained comparison scale combining the original numerator, inverse, factor and coordinate ceilings. -/ scale
    : InverseRootPolynomial.Coordinate
  /-- The cached scale is exactly the displayed sum of the original numerator, factor, inverse and coordinate error
    contributions. -/ scale_eq : scale = 2 * factor.base.numeratorUpper * reciprocal.inverseUpper * cap.model.bound +
    4 * factor.bound * ((1 + pointUpper) * factor.base.inverseUpper * preparation.reciprocal.bound +
      pointUpper * reciprocal.inverseUpper * preparation.regular.bound)

constructive_injectivity Bounds

namespace Bounds

/-- Cache the original reciprocal and cap-factor bounds and their exact combined comparison scale. -/
@[expose] public def build (preparation : PolynomialPullback.Preparation cap initial)
    (clearance : PrimitiveEdgeComparison.RegionClearance (HyperellipticReciprocal.polynomial curve) localBox)
      (differential : Differentials.Basic.Differential genus) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.ComparisonBounds.Bounds preparation clearance differential :=
  let reciprocal := PrimitiveOverlapBounds.build clearance (DensePolynomial.constant 1)
  let factor := FactorBounds.build cap differential
  let pointUpper := collar.box.normSqBound
  let scale := 2 * factor.base.numeratorUpper * reciprocal.inverseUpper * cap.model.bound +
    4 * factor.bound * ((1 + pointUpper) * factor.base.inverseUpper * preparation.reciprocal.bound +
      pointUpper * reciprocal.inverseUpper * preparation.regular.bound)
  ⟨reciprocal, factor, pointUpper, rfl, scale, rfl⟩

variable {preparation : Preparation cap initial}
  {clearance : RegionClearance
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve) localBox} {differential :
    Differential genus}

/-- The original collar-box squared-norm ceiling is nonnegative. -/
theorem pointUpper_nonnegative (bounds : Curves.Hyperelliptic.Charts.Reciprocal.Cap.ComparisonBounds.Bounds preparation
  clearance differential) : 0 ≤ bounds.pointUpper := by
  rw [bounds.pointUpper_eq]
  exact collar.box.normSqBound_nonneg

/-- The retained cap comparison error scale is nonnegative. -/
theorem scale_nonnegative (bounds : Curves.Hyperelliptic.Charts.Reciprocal.Cap.ComparisonBounds.Bounds preparation
  clearance differential) : 0 ≤ bounds.scale := by
  rw [bounds.scale_eq]
  apply add_nonneg
  · exact Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) bounds.factor.base.numeratorUpper_nonnegative)
        bounds.reciprocal.inverseUpper_positive.le) cap.model.bound_nonnegative
  · apply Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) bounds.factor.bound_nonnegative)
    exact add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (add_nonneg (by decide) bounds.pointUpper_nonnegative)
          bounds.factor.base.inverseUpper_positive.le) preparation.reciprocal.bound_nonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct bounds.pointUpper_nonnegative
          bounds.reciprocal.inverseUpper_positive.le)
        preparation.regular.bound_nonnegative)

/-- A point of the original cap box satisfies the retained collar-box squared-norm ceiling. -/
private theorem coordinate_le (bounds : Curves.Hyperelliptic.Charts.Reciprocal.Cap.ComparisonBounds.Bounds preparation
  clearance differential) {point : InverseRootPolynomial.Gaussian}
    (inside : collar.box.Contains point) : Data.Gaussian.Norm.Basic.normSq point ≤ bounds.pointUpper := by
  rw [bounds.pointUpper_eq]
  exact Rational.Box.normSq_le_normSqBound inside

/-- The original parity power has squared norm at most one plus the retained point ceiling. -/
private theorem parity_le (bounds : Curves.Hyperelliptic.Charts.Reciprocal.Cap.ComparisonBounds.Bounds preparation
  clearance differential) {point : InverseRootPolynomial.Gaussian}
    (inside : collar.box.Contains point) :
    Data.Gaussian.Norm.Basic.normSq (point ^ (1 - HyperellipticReciprocal.originOrder curve)) ≤ 1 +
      bounds.pointUpper := by
  rcases (HyperellipticReciprocal.origin_factor curve).2 with regular | branch
  · rw [regular, Nat.sub_zero, pow_one]
    exact (bounds.coordinate_le inside).trans (le_add_of_nonneg_left (by decide))
  · rw [branch, Nat.sub_self, pow_zero, Data.Gaussian.Norm.Basic.normSq_one]
    exact Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _ bounds.pointUpper_nonnegative

/-- The squared norm of a product of three Gaussian factors is bounded by the product of their nonnegative ceilings. -/
private theorem product_bound {first second third : InverseRootPolynomial.Gaussian} {firstUpper secondUpper thirdUpper :
  InverseRootPolynomial.Coordinate}
    (firstBound : Data.Gaussian.Norm.Basic.normSq first ≤ firstUpper) (secondBound :
      Data.Gaussian.Norm.Basic.normSq second ≤ secondUpper)
    (thirdBound : Data.Gaussian.Norm.Basic.normSq third ≤ thirdUpper) :
      Data.Gaussian.Norm.Basic.normSq (first * second * third) ≤ firstUpper * secondUpper * thirdUpper := by
  rw [Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_direct
    (Fraction.Order.Arithmetic.mul_le_mul_direct firstBound secondBound (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      ((Data.Gaussian.Norm.Basic.normSq_nonneg _).trans firstBound))
    thirdBound (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct ((Data.Gaussian.Norm.Basic.normSq_nonneg _).trans firstBound)
      ((Data.Gaussian.Norm.Basic.normSq_nonneg _).trans secondBound))

/-- The derivative error has one uniform geometric budget on the common domain, independent of all later polynomial
degrees and spatial mesh counts. -/
theorem derivative_error_le (bounds : Curves.Hyperelliptic.Charts.Reciprocal.Cap.ComparisonBounds.Bounds preparation
  clearance differential) {index : Nat} {box : Rational.Box}
    {capSample : Primitives.Sample cap differential index box} (sample : PolynomialPullback.Sample preparation
      capSample)
    {point : InverseRootPolynomial.Gaussian} (localInside : localBox.Contains point) (capInside : collar.box.Contains
      point) :
    Data.Gaussian.Norm.Basic.normSq ((Derivative.derivative sample.value).eval point - sample.coefficient.eval
      point) ≤
      Geometric.Basic.quarterRadius bounds.scale index := by
  let first := point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent *
    sample.reciprocal.value.eval point *
    capSample.inverse.residual.eval point
  let second := point ^ (1 - HyperellipticReciprocal.originOrder curve) * capSample.inverse.value.eval point *
    InverseModelDifferentialResidual.differentialResidual (HyperellipticReciprocal.polynomial curve)
      sample.reciprocal.value point
  let third := point * sample.reciprocal.value.eval point * InverseModelDifferentialResidual.differentialResidual
    cap.polynomial capSample.inverse.value point
  have reciprocalBound := bounds.reciprocal.inverse_norm_le sample.reciprocal localInside
  have regularBound := bounds.factor.base.inverse_norm_le capSample.inverse capInside
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at reciprocalBound regularBound
  have numeratorBound : Data.Gaussian.Norm.Basic.normSq (point ^ (HyperellipticReciprocal.reversedDifferential
    differential).exponent) ≤
      bounds.factor.base.numeratorUpper := by
    rw [← bounds.factor.numerator_eq, bounds.factor.base.numeratorUpper_eq]
    exact Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound _ capInside
  have residualBound : Data.Gaussian.Norm.Basic.normSq (capSample.inverse.residual.eval point) ≤
    Geometric.Basic.quarterRadius cap.model.bound index := by
    rw [capSample.inverse_eq, ← cap.model.refine_bound]
    have scalar := (cap.model.refine index).residualBound point capInside
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  have firstBound : Data.Gaussian.Norm.Basic.normSq first ≤
      Geometric.Basic.quarterRadius (bounds.factor.base.numeratorUpper * bounds.reciprocal.inverseUpper *
        cap.model.bound) index :=
    (product_bound numeratorBound reciprocalBound
      residualBound).trans_eq (by
          rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow];
          ring1)
  have secondBound : Data.Gaussian.Norm.Basic.normSq second ≤
      Geometric.Basic.quarterRadius ((1 + bounds.pointUpper) * bounds.factor.base.inverseUpper *
        preparation.reciprocal.bound) index :=
    (product_bound (bounds.parity_le capInside)
      regularBound (sample.reciprocal_differential_bound localInside)).trans_eq
      (by rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]; ring1)
  have thirdBound : Data.Gaussian.Norm.Basic.normSq third ≤
      Geometric.Basic.quarterRadius (bounds.pointUpper * bounds.reciprocal.inverseUpper * preparation.regular.bound)
        index :=
    (product_bound (bounds.coordinate_le capInside)
      reciprocalBound (sample.regular_differential_bound capInside)).trans_eq
      (by rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]; ring1)
  have factorBound : Data.Gaussian.Norm.Basic.normSq (InverseRootPolynomial.half * capSample.factor.eval point)
    ≤ bounds.factor.bound := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact (Fraction.Order.Arithmetic.mul_le_mul_direct
      (show Data.Gaussian.Norm.Basic.normSq InverseRootPolynomial.half ≤ 1 by decide) (bounds.factor.factor_le
        capSample capInside)
      (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide)).trans_eq (Fraction.Field.one_mul _)
  have sumBound := (Data.Gaussian.Norm.Bounds.normSq_add_le_two second third).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add secondBound thirdBound) (by decide))
  have tailBound : Data.Gaussian.Norm.Basic.normSq (InverseRootPolynomial.half * capSample.factor.eval point *
    (second + third)) ≤
      bounds.factor.bound * (2 *
        (Geometric.Basic.quarterRadius ((1 + bounds.pointUpper) * bounds.factor.base.inverseUpper *
          preparation.reciprocal.bound) index +
          Geometric.Basic.quarterRadius (bounds.pointUpper * bounds.reciprocal.inverseUpper * preparation.regular.bound)
            index)) := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct factorBound sumBound (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      bounds.factor.bound_nonnegative
  rw [sample.derivative_error]
  change Data.Gaussian.Norm.Basic.normSq (first + InverseRootPolynomial.half * capSample.factor.eval point *
    (second + third)) ≤ _
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add firstBound tailBound) (by decide)).trans_eq
      (by
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow, bounds.scale_eq]
      ring1))

end Bounds
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ComparisonBounds
