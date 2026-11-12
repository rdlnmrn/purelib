module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Projective.Homography.Injectivity
import Purelib.Geometry.Projective.Homography.Pole
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RationalFunctions.Curve.Coordinates
public import Purelib.RationalFunctions.Curve.Transform

import Purelib.Tactic.QuotientFreeOmega

open Purelib.LinearAlgebra.Coordinates2.Matrix
open Purelib.Geometry.Projective.Homography

section
public section

/-!
# Nondegeneracy of the finite CCL boundary charts

Every active curve source is a genuine rational line or a nonzero-radius
circle transported by an invertible finite homography.  Consequently its
homogeneous denominator is a represented nonzero coordinate polynomial, and
its affine values are injective at non-pole parameters.

The final theorem uses only finitely many parameters: one denominator-safe
point in each of `natDegree + 1` disjoint unit intervals.  If both cleared
coordinates vanished identically, these points would give too many distinct
displayed roots of the original Gaussian-rational polynomial.
-/

namespace Purelib.RationalFunctions.Curve

namespace RationalCurve

open Purelib.Data in
open Purelib.RationalFunctions in
/-- Nonzero denominator quadrance and injectivity at non-pole parameters for a rational curve.

The denominator-quadrance polynomial is explicitly nonzero. Equal affine points at any two parameters with nonzero
denominators force those parameters to be equal. -/
structure Nondegenerate (curve : RationalCurve) : Prop where
  /-- The curve's denominator-quadrance polynomial is not the zero polynomial. -/ denominatorNormNonzero :
    (Coordinates.denominatorNormSq curve).isZero = false
  /-- Equal affine values at non-pole parameters imply equal parameters. -/ pointInjective : ∀ {left right :
    Rat.Fraction.Rational},
    curve.denominatorAt left ≠ 0 → curve.denominatorAt right ≠ 0 →
      curve.point left = curve.point right → left = right

end RationalCurve

section
open Purelib.LinearAlgebra
open Purelib.Data
open Purelib.Geometry
open Purelib.RationalFunctions
/-- An adjugate homographic transform preserves injectivity at parameters with nonzero transformed denominator.

The matrix determinant is nonzero, and the source curve has nonzero denominator everywhere and an injective affine
parameterization. -/
private theorem transformed_point_injective
    (matrix : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    (source : RationalCurve)
    (sourceTotal : ∀ parameter, source.denominatorAt parameter ≠ 0)
    (sourceInjective : Function.Injective source.point)
    {left right : Rat.Fraction.Rational}
    (leftDenominator :
      (source.transform
        (BoundaryAdjugate.adjugate matrix)).denominatorAt left ≠ 0)
    (rightDenominator :
      (source.transform
        (BoundaryAdjugate.adjugate matrix)).denominatorAt right ≠ 0)
    (equal :
      (source.transform
          (BoundaryAdjugate.adjugate matrix)).point left =
        (source.transform
          (BoundaryAdjugate.adjugate matrix)).point right) :
    left = right := by
  have leftAdjugate := adjugateDenominator_ne_of_transformed matrix source left
    (sourceTotal left) leftDenominator
  have rightAdjugate := adjugateDenominator_ne_of_transformed matrix source right
    (sourceTotal right) rightDenominator
  have imageEqual :
      Basic.homographic
          (BoundaryAdjugate.adjugate matrix) (source.point left) =
        Basic.homographic
          (BoundaryAdjugate.adjugate matrix)
            (source.point right) := by
    rw [← RationalCurve.point_transform
          (BoundaryAdjugate.adjugate matrix) source left
            (sourceTotal left) leftAdjugate,
      ← RationalCurve.point_transform
          (BoundaryAdjugate.adjugate matrix) source right
            (sourceTotal right) rightAdjugate]
    exact equal
  apply sourceInjective
  apply Injectivity.homographic_injective
    (BoundaryAdjugate.adjugate matrix)
  · change BoundaryAdjugate.determinant
      (BoundaryAdjugate.adjugate matrix) ≠ 0
    rw [BoundaryAdjugate.determinant_adjugate]
    exact determinantNonzero
  · exact leftAdjugate
  · exact rightAdjugate
  · exact imageEqual

/-- The adjugate-transformed denominator cannot vanish at both zero and one.

The matrix is invertible, and the source curve is total and injective. Two such poles would force the distinct source
parameters to have the same affine point. -/
private theorem transformed_denominators_not_both_zero
    (matrix : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    (source : RationalCurve)
    (sourceTotal : ∀ parameter, source.denominatorAt parameter ≠ 0)
    (sourceInjective : Function.Injective source.point) :
    ¬ ((source.transform
          (BoundaryAdjugate.adjugate matrix)).denominatorAt 0 = 0 ∧
       (source.transform
          (BoundaryAdjugate.adjugate matrix)).denominatorAt 1 = 0) := by
  rintro ⟨zeroAtZero, zeroAtOne⟩
  have adjugateZeroAtZero :
      Basic.denominator
          (BoundaryAdjugate.adjugate matrix) (source.point 0) = 0 := by
    by_cases nonzero : Basic.denominator
        (BoundaryAdjugate.adjugate matrix) (source.point 0) ≠ 0
    · exact (Gaussian.Field.mul_ne_zero_direct nonzero
        (sourceTotal 0) (by
          rw [← NondegenerateHelpers.transformedDenominator_eq matrix source 0 (sourceTotal 0)]
          exact zeroAtZero)).elim
    · by_cases zero : Basic.denominator
          (BoundaryAdjugate.adjugate matrix) (source.point 0) = 0
      · exact zero
      · exact (nonzero zero).elim
  have adjugateZeroAtOne :
      Basic.denominator
          (BoundaryAdjugate.adjugate matrix) (source.point 1) = 0 := by
    by_cases nonzero : Basic.denominator
        (BoundaryAdjugate.adjugate matrix) (source.point 1) ≠ 0
    · exact (Gaussian.Field.mul_ne_zero_direct nonzero
        (sourceTotal 1) (by
          rw [← NondegenerateHelpers.transformedDenominator_eq matrix source 1 (sourceTotal 1)]
          exact zeroAtOne)).elim
    · by_cases zero : Basic.denominator
          (BoundaryAdjugate.adjugate matrix) (source.point 1) = 0
      · exact zero
      · exact (nonzero zero).elim
  have sourcePointsEqual := Projective.Homography.denominator_zero_unique
    (BoundaryAdjugate.adjugate matrix) (by
      rw [BoundaryAdjugate.determinant_adjugate]
      exact determinantNonzero) adjugateZeroAtZero adjugateZeroAtOne
  have parametersEqual : (0 : Rat.Fraction.Rational) = 1 :=
    sourceInjective sourcePointsEqual
  exact (show (0 : Rat.Fraction.Rational) ≠ 1 by decide) parametersEqual

end

open Purelib.LinearAlgebra in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- The adjugate transform of a total injective source curve is nondegenerate.

A nonzero matrix determinant preserves injectivity away from poles. The transformed denominator-quadrance polynomial is
nonzero because the denominators at zero and one cannot both vanish. -/
theorem transformed_nondegenerate
    (matrix : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    (source : RationalCurve)
    (sourceTotal : ∀ parameter, source.denominatorAt parameter ≠ 0)
    (sourceInjective : Function.Injective source.point) :
    RationalCurve.Nondegenerate
      (source.transform (BoundaryAdjugate.adjugate matrix)) := by
  let curve := source.transform (BoundaryAdjugate.adjugate matrix)
  have notBothZero := transformed_denominators_not_both_zero matrix
    determinantNonzero source sourceTotal sourceInjective
  refine
    { denominatorNormNonzero := ?_
      pointInjective := ?_ }
  · by_cases nonzero :
        (Coordinates.denominatorNormSq curve).isZero =
          false
    · exact nonzero
    · have zero :
          (Coordinates.denominatorNormSq curve).isZero =
            true := by
        cases value : (Coordinates.denominatorNormSq curve).isZero with
        | false => exact (nonzero value).elim
        | true => rfl
      have zeroAt (parameter : Rat.Fraction.Rational) : curve.denominatorAt parameter = 0 := by
        apply Gaussian.Norm.Basic.normSq_eq_zero.mp
        rw [← Coordinates.eval_denominatorNormSq]
        exact Dense.Basic.DensePolynomial.eval_eq_zero_of_isZero zero parameter
      exact (notBothZero ⟨zeroAt 0, zeroAt 1⟩).elim
  · intro left right leftDenominator rightDenominator equal
    exact transformed_point_injective matrix determinantNonzero source
      sourceTotal sourceInjective leftDenominator rightDenominator equal

end Purelib.RationalFunctions.Curve

end
