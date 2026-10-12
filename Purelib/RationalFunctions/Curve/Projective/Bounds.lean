module
public import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Matrix.WeightLower
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Hermitian
public import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Line.Matrix.Gaussian
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Components
public import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RationalFunctions.Curve.Coordinates
public import Purelib.RationalFunctions.Curve.Projective.Basic
public import Purelib.RationalFunctions.Curve.Transform
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Interval (Bounds)

section
@[expose] public section

/-!
# Quantitative projective bounds for finite rational curves

The homogeneous numerator and denominator of a rational curve are ordinary
finite coordinate polynomials.  Componentwise Horner bounds therefore give
an explicit Lipschitz coefficient for their projective cross product.  Once
the denominator coordinates carry a positive Bézout clearance on a bounded
parameter interval, this becomes a squared-chordal image bound proportional
to the square of the parameter width.

No affine division, square root, completed point, or limiting argument is
used.  The result is the finite shrinking-cylinder estimate needed to compare
a persistent curve event with a simultaneously shrinking winding box.
-/

namespace Purelib.RationalFunctions.Curve.Projective

section
open Purelib.Data
section
open Purelib.Polynomial
open Purelib.RationalFunctions
/-- Compute an interval quadrance bound for the homogeneous numerator.

Sum the squared Horner evaluation bounds for its real and imaginary coordinate polynomials. -/
def numeratorValueBound (curve : Curve.RationalCurve) (interval :
  Bounds) :
    Rational :=
  Dense.Rational.Bounds.Horner.evalSqBound
      (Curve.Coordinates.numeratorReal curve) interval +
    Dense.Rational.Bounds.Horner.evalSqBound
      (Curve.Coordinates.numeratorImaginary curve) interval

/-- Compute an interval quadrance bound for the homogeneous denominator.

Sum the squared Horner evaluation bounds for its real and imaginary coordinate polynomials. -/
def denominatorValueBound (curve : Curve.RationalCurve) (interval :
  Bounds) :
    Rational :=
  Dense.Rational.Bounds.Horner.evalSqBound
      (Curve.Coordinates.denominatorReal curve) interval +
    Dense.Rational.Bounds.Horner.evalSqBound
      (Curve.Coordinates.denominatorImaginary curve) interval

/-- Compute a squared Lipschitz coefficient for the homogeneous numerator on an interval.

Sum the real and imaginary coordinate bounds so that multiplication by squared parameter displacement bounds numerator
quadrance variation. -/
def numeratorLipschitzBound (curve : Curve.RationalCurve) (interval :
  Bounds) :
    Rational :=
  Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound
      (Curve.Coordinates.numeratorReal curve) interval +
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound
      (Curve.Coordinates.numeratorImaginary curve) interval

/-- Compute a squared Lipschitz coefficient for the homogeneous denominator on an interval.

Sum the real and imaginary coordinate bounds so that multiplication by squared parameter displacement bounds denominator
quadrance variation. -/
def denominatorLipschitzBound (curve : Curve.RationalCurve) (interval
  : Bounds) :
    Rational :=
  Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound
      (Curve.Coordinates.denominatorReal curve) interval +
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound
      (Curve.Coordinates.denominatorImaginary curve) interval

end

open Purelib.RationalFunctions in
/-- Compute a squared variation coefficient for the homogeneous cross product.

Twice the sum of the numerator Lipschitz coefficient times denominator value bound and the numerator value bound times
denominator Lipschitz coefficient controls the cross-product quadrance. -/
def crossVariationCoefficient (curve : Curve.RationalCurve) (interval
  : Bounds) :
    Rational :=
  2 * (numeratorLipschitzBound curve interval *
      denominatorValueBound curve interval +
    numeratorValueBound curve interval *
      denominatorLipschitzBound curve interval)

section
open Purelib.Polynomial
open Purelib.RationalFunctions
/-- The numerator quadrance bound is nonnegative. -/
theorem numeratorValueBound_nonneg
    (curve : Curve.RationalCurve) (interval : Bounds) :
    0 ≤ numeratorValueBound curve interval :=
  add_nonneg
    (Dense.Rational.Bounds.Horner.evalSqBound_nonneg _ _)
    (Dense.Rational.Bounds.Horner.evalSqBound_nonneg _ _)

/-- The denominator quadrance bound is nonnegative. -/
theorem denominatorValueBound_nonneg
    (curve : Curve.RationalCurve) (interval : Bounds) :
    0 ≤ denominatorValueBound curve interval :=
  add_nonneg
    (Dense.Rational.Bounds.Horner.evalSqBound_nonneg _ _)
    (Dense.Rational.Bounds.Horner.evalSqBound_nonneg _ _)

/-- The numerator squared Lipschitz coefficient is nonnegative. -/
theorem numeratorLipschitzBound_nonneg
    (curve : Curve.RationalCurve) (interval : Bounds) :
    0 ≤ numeratorLipschitzBound curve interval :=
  add_nonneg
    (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg _ _).2
    (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg _ _).2

/-- The denominator squared Lipschitz coefficient is nonnegative. -/
theorem denominatorLipschitzBound_nonneg
    (curve : Curve.RationalCurve) (interval : Bounds) :
    0 ≤ denominatorLipschitzBound curve interval :=
  add_nonneg
    (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg _ _).2
    (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg _ _).2

end

open Purelib.RationalFunctions in
/-- The homogeneous cross-product variation coefficient is nonnegative. -/
theorem crossVariationCoefficient_nonneg
    (curve : Curve.RationalCurve) (interval : Bounds) :
    0 ≤ crossVariationCoefficient curve interval := by
  apply Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
  exact add_nonneg
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (numeratorLipschitzBound_nonneg curve interval)
      (denominatorValueBound_nonneg curve interval))
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (numeratorValueBound_nonneg curve interval)
      (denominatorLipschitzBound_nonneg curve interval))

section
open Purelib.Polynomial
open Purelib.RationalFunctions
/-- The homogeneous numerator quadrance is at most its interval value bound.

The parameter lies in the displayed interval; summing its two coordinate evaluation bounds gives the estimate. -/
theorem normSq_numeratorAt_le
    (curve : Curve.RationalCurve) (interval : Bounds) {parameter : Rational}
    (inside : interval.Contains parameter) :
    Data.Gaussian.Norm.Basic.normSq (curve.numeratorAt parameter) ≤
      numeratorValueBound curve interval := by
  have bounds := add_le_add
    (Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound
      (Curve.Coordinates.numeratorReal curve)
      interval inside)
    (Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound
      (Curve.Coordinates.numeratorImaginary curve)
      interval inside)
  simpa only [numeratorValueBound,
    Curve.Coordinates.numeratorReal,
    Curve.Coordinates.numeratorImaginary,
    Dense.Gaussian.Components.eval_realPart,
    Dense.Gaussian.Components.eval_imagPart,
    Curve.RationalCurve.numeratorAt, Data.Gaussian.Norm.Basic.normSq] using
      bounds

/-- The homogeneous denominator quadrance is at most its interval value bound.

The parameter lies in the displayed interval; summing its two coordinate evaluation bounds gives the estimate. -/
theorem normSq_denominatorAt_le
    (curve : Curve.RationalCurve) (interval : Bounds) {parameter : Rational}
    (inside : interval.Contains parameter) :
    Data.Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter) ≤
      denominatorValueBound curve interval := by
  have bounds := add_le_add
    (Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound
      (Curve.Coordinates.denominatorReal curve)
      interval inside)
    (Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound
      (Curve.Coordinates.denominatorImaginary curve)
      interval inside)
  simpa only [denominatorValueBound,
    Curve.Coordinates.denominatorReal,
    Curve.Coordinates.denominatorImaginary,
    Dense.Gaussian.Components.eval_realPart,
    Dense.Gaussian.Components.eval_imagPart,
    Curve.RationalCurve.denominatorAt, Data.Gaussian.Norm.Basic.normSq] using
      bounds

/-- Numerator variation is bounded by its squared Lipschitz coefficient times squared parameter displacement.

Both parameters lie in the same interval. The estimate sums the real and imaginary coordinate Lipschitz bounds. -/
theorem normSq_numeratorAt_sub_le
    (curve : Curve.RationalCurve) (interval : Bounds) {left right : Rational}
    (leftInside : interval.Contains left)
    (rightInside : interval.Contains right) :
    Data.Gaussian.Norm.Basic.normSq (curve.numeratorAt left - curve.numeratorAt right) ≤
      numeratorLipschitzBound curve interval * (left - right) ^ 2 := by
  have bounds :
      ((Curve.Coordinates.numeratorReal curve).eval left -
          (Curve.Coordinates.numeratorReal curve).eval right) ^ 2 +
        ((Curve.Coordinates.numeratorImaginary curve).eval left -
          (Curve.Coordinates.numeratorImaginary curve).eval
            right) ^ 2 ≤
        numeratorLipschitzBound curve interval * (left - right) ^ 2 := calc
    _ ≤ Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound
          (Curve.Coordinates.numeratorReal curve) interval *
            (left - right) ^ 2 +
        Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound
          (Curve.Coordinates.numeratorImaginary curve) interval *
            (left - right) ^ 2 :=
      add_le_add
        (Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le _ interval
          leftInside rightInside)
        (Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le _ interval
          leftInside rightInside)
    _ = numeratorLipschitzBound curve interval * (left - right) ^ 2 := by
      dsimp only [numeratorLipschitzBound]
      ring1
  simpa only [Curve.Coordinates.numeratorReal,
    Curve.Coordinates.numeratorImaginary,
    Dense.Gaussian.Components.eval_realPart,
    Dense.Gaussian.Components.eval_imagPart,
    Curve.RationalCurve.numeratorAt, Data.Gaussian.Norm.Basic.normSq,
    Gaussian.Basic.sub_re,
    Gaussian.Basic.sub_im] using bounds

/-- Denominator variation is bounded by its squared Lipschitz coefficient times squared parameter displacement.

Both parameters lie in the same interval. The estimate sums the real and imaginary coordinate Lipschitz bounds. -/
theorem normSq_denominatorAt_sub_le
    (curve : Curve.RationalCurve) (interval : Bounds) {left right : Rational}
    (leftInside : interval.Contains left)
    (rightInside : interval.Contains right) :
    Data.Gaussian.Norm.Basic.normSq (curve.denominatorAt left - curve.denominatorAt right) ≤
      denominatorLipschitzBound curve interval * (left - right) ^ 2 := by
  have bounds :
      ((Curve.Coordinates.denominatorReal curve).eval left -
          (Curve.Coordinates.denominatorReal curve).eval right) ^ 2 +
        ((Curve.Coordinates.denominatorImaginary curve).eval left -
          (Curve.Coordinates.denominatorImaginary curve).eval
            right) ^ 2 ≤
        denominatorLipschitzBound curve interval * (left - right) ^ 2 := calc
    _ ≤ Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound
          (Curve.Coordinates.denominatorReal curve) interval *
            (left - right) ^ 2 +
        Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound
          (Curve.Coordinates.denominatorImaginary curve) interval *
            (left - right) ^ 2 :=
      add_le_add
        (Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le _ interval
          leftInside rightInside)
        (Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le _ interval
          leftInside rightInside)
    _ = denominatorLipschitzBound curve interval * (left - right) ^ 2 := by
      dsimp only [denominatorLipschitzBound]
      ring1
  simpa only [Curve.Coordinates.denominatorReal,
    Curve.Coordinates.denominatorImaginary,
    Dense.Gaussian.Components.eval_realPart,
    Dense.Gaussian.Components.eval_imagPart,
    Curve.RationalCurve.denominatorAt, Data.Gaussian.Norm.Basic.normSq,
    Gaussian.Basic.sub_re,
    Gaussian.Basic.sub_im] using bounds

end

open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- The homogeneous cross-product quadrance is bounded by the variation coefficient times squared parameter
displacement.

Both parameters lie in the interval. Expanding the cross product into numerator and denominator differences combines
their coordinate Lipschitz estimates with the corresponding value bounds. -/
theorem normSq_cross_le
    (curve : Curve.RationalCurve) (interval : Bounds) {left right : Rational}
    (leftInside : interval.Contains left)
    (rightInside : interval.Contains right) :
    Data.Gaussian.Norm.Basic.normSq (Projective.Line.Hermitian.Proj.cross
      (Curve.Projective.projective curve left) (Curve.Projective.projective curve right)) ≤
      crossVariationCoefficient curve interval * (left - right) ^ 2 := by
  let leftNumerator := curve.numeratorAt left
  let rightNumerator := curve.numeratorAt right
  let leftDenominator := curve.denominatorAt left
  let rightDenominator := curve.denominatorAt right
  have crossIdentity :
      leftNumerator * rightDenominator - rightNumerator * leftDenominator =
        (leftNumerator - rightNumerator) * rightDenominator +
          rightNumerator * (rightDenominator - leftDenominator) := by
    symm
    calc
      (leftNumerator - rightNumerator) * rightDenominator +
            rightNumerator * (rightDenominator - leftDenominator) =
          (leftNumerator * rightDenominator +
              -(rightNumerator * rightDenominator)) +
            (rightNumerator * rightDenominator +
              -(rightNumerator * leftDenominator)) := by
        rw [Gaussian.Basic.sub_eq_add_neg,
          Gaussian.Basic.sub_eq_add_neg,
          Gaussian.Basic.right_distrib,
          Gaussian.Basic.left_distrib,
          _root_.neg_mul, _root_.mul_neg]
      _ = leftNumerator * rightDenominator +
          (-(rightNumerator * rightDenominator) +
            (rightNumerator * rightDenominator +
              -(rightNumerator * leftDenominator))) :=
        Gaussian.Basic.add_assoc _ _ _
      _ = leftNumerator * rightDenominator +
          ((-(rightNumerator * rightDenominator) +
              rightNumerator * rightDenominator) +
            -(rightNumerator * leftDenominator)) := by
        rw [Gaussian.Basic.add_assoc]
      _ = leftNumerator * rightDenominator +
          (0 + -(rightNumerator * leftDenominator)) := by
        rw [neg_add_cancel]
      _ = leftNumerator * rightDenominator +
          -(rightNumerator * leftDenominator) := by
        rw [Gaussian.Basic.zero_add]
      _ = leftNumerator * rightDenominator -
          rightNumerator * leftDenominator :=
        (Gaussian.Basic.sub_eq_add_neg _ _).symm
  have firstBound :
      Data.Gaussian.Norm.Basic.normSq ((leftNumerator - rightNumerator) * rightDenominator) ≤
        (numeratorLipschitzBound curve interval * (left - right) ^ 2) *
          denominatorValueBound curve interval := by
    rw [Gaussian.Norm.Basic.normSq_mul]
    exact Rat.Fraction.Order.Arithmetic.mul_le_mul_direct
      (normSq_numeratorAt_sub_le curve interval leftInside rightInside)
      (normSq_denominatorAt_le curve interval rightInside)
      (Gaussian.Norm.Basic.normSq_nonneg rightDenominator)
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
        (numeratorLipschitzBound_nonneg curve interval)
        (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct (left - right)))
  have secondBound :
      Data.Gaussian.Norm.Basic.normSq (rightNumerator * (rightDenominator - leftDenominator)) ≤
        numeratorValueBound curve interval *
          (denominatorLipschitzBound curve interval * (left - right) ^ 2) := by
    rw [Gaussian.Norm.Basic.normSq_mul]
    exact Rat.Fraction.Order.Arithmetic.mul_le_mul_direct
      (normSq_numeratorAt_le curve interval rightInside)
      (by
        have reversed := normSq_denominatorAt_sub_le curve interval
          leftInside rightInside
        have differenceIdentity :
            rightDenominator - leftDenominator =
              -(leftDenominator - rightDenominator) := by
          simp only [Gaussian.Basic.sub_eq_add_neg,
            _root_.neg_add_rev, neg_neg, -eq_self, -iff_self]
          rfl
        rw [differenceIdentity, Gaussian.Norm.Basic.normSq_neg]
        exact reversed)
      (Gaussian.Norm.Basic.normSq_nonneg (rightDenominator - leftDenominator))
      (numeratorValueBound_nonneg curve interval)
  change Data.Gaussian.Norm.Basic.normSq
    (leftNumerator * rightDenominator - rightNumerator * leftDenominator) ≤ _
  rw [crossIdentity]
  calc
    Data.Gaussian.Norm.Basic.normSq ((leftNumerator - rightNumerator) * rightDenominator +
        rightNumerator * (rightDenominator - leftDenominator)) ≤
      2 * (Data.Gaussian.Norm.Basic.normSq ((leftNumerator - rightNumerator) * rightDenominator) +
        Data.Gaussian.Norm.Basic.normSq (rightNumerator *
          (rightDenominator - leftDenominator))) :=
      Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 *
        ((numeratorLipschitzBound curve interval * (left - right) ^ 2) *
            denominatorValueBound curve interval +
          numeratorValueBound curve interval *
            (denominatorLipschitzBound curve interval *
              (left - right) ^ 2)) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add firstBound secondBound) (by decide)
    _ = crossVariationCoefficient curve interval * (left - right) ^ 2 := by
      dsimp only [crossVariationCoefficient]
      ring1
end

end Purelib.RationalFunctions.Curve.Projective

end

section
@[expose] public section

/-!
# Rational parameterizations of CCL comparison boundaries

Coordinate lines and centered circles are transported through an invertible
finite homography by its explicit adjugate.  The resulting rational curve is
proved to lie on the corresponding Hermitian comparison boundary at every
non-pole parameter.  This is the provenance-preserving bridge needed before
the cleared gcd/Sturm classifier can inspect parser-formula boundaries.
-/

namespace Purelib
namespace Geometry.Projective.Hermitian.Parametrization

section
open Purelib.Data
open Purelib.Geometry
open Purelib.LinearAlgebra in
open Purelib.RationalFunctions in
/-- Transport a uniform projective weight lower bound through a Gaussian matrix action.

Multiply the source lower bound by determinant quadrance and divide by the adjugate action coefficient. The resulting
rational quantity bounds the transformed curve weight at every parameter. -/
private theorem
  transformedCurveWeightLower_le
    (matrix : Coordinates2.Matrix.GaussianMatrix) (source : Curve.RationalCurve)
    (sourceLower : Rational)
    (sourceLowerLe : ∀ parameter, sourceLower ≤
      Projective.Line.Hermitian.Proj.weight
        ⟨source.numeratorAt parameter, source.denominatorAt parameter⟩)
    (parameter : Rational) :
    (Data.Gaussian.Norm.Basic.normSq (Coordinates2.Matrix.BoundaryAdjugate.determinant matrix) * sourceLower /
      Projective.Chordal.Matrix.Mat2.actionWeightCoefficient (Coordinates2.Matrix.BoundaryAdjugate.adjugate matrix)) ≤
      Projective.Line.Hermitian.Proj.weight
        ⟨(source.transform matrix).numeratorAt parameter,
          (source.transform matrix).denominatorAt parameter⟩ := by
  have bound := transformedPointWeightLower matrix sourceLower
    ⟨source.numeratorAt parameter, source.denominatorAt parameter⟩
    (sourceLowerLe parameter)
  simpa only [
    Curve.RationalCurve.numeratorAt_transform,
    Curve.RationalCurve.denominatorAt_transform,
    Projective.Line.Matrix.act] using bound

section
open Purelib.RationalFunctions
/-- A homogeneous denominator equal to parameter squared plus one gives source projective weight at least one. -/
private theorem circleSourceWeightLower
    (curve : Curve.RationalCurve)
    (denominatorFormula : ∀ parameter,
      curve.denominatorAt parameter = ⟨parameter ^ 2 + 1, 0⟩)
    (parameter : Rational) :
    (1 : Rational) ≤ Projective.Line.Hermitian.Proj.weight
      ⟨curve.numeratorAt parameter, curve.denominatorAt parameter⟩ := by
  have oneLe : (1 : Rational) ≤ parameter ^ 2 + 1 := by
    have added := Rat.Fraction.Order.Arithmetic.add_le_add_right_direct
      (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct parameter) 1
    simpa only [Rat.Fraction.Field.zero_add] using added
  have squareLe : (1 : Rational) ≤ (parameter ^ 2 + 1) ^ 2 := by
    simpa only [one_pow] using
      Rat.Fraction.Order.Arithmetic.pow_le_pow_direct (by decide) oneLe 2
  rw [denominatorFormula parameter]
  change 1 ≤ Data.Gaussian.Norm.Basic.normSq (curve.numeratorAt parameter) +
    ((parameter ^ 2 + 1) ^ 2 + 0 ^ 2)
  exact squareLe.trans (by
    calc
      (parameter ^ 2 + 1) ^ 2 ≤
          Data.Gaussian.Norm.Basic.normSq (curve.numeratorAt parameter) +
            (parameter ^ 2 + 1) ^ 2 :=
        le_add_of_nonneg_left (Gaussian.Norm.Basic.normSq_nonneg (curve.numeratorAt parameter))
      _ = Data.Gaussian.Norm.Basic.normSq (curve.numeratorAt parameter) +
          ((parameter ^ 2 + 1) ^ 2 + 0 ^ 2) := by ring1)

/-- An identically unit homogeneous denominator gives source projective weight at least one. -/
private theorem
  unitDenominatorSourceWeightLower
    (curve : Curve.RationalCurve)
    (denominatorFormula : ∀ parameter,
      curve.denominatorAt parameter = 1)
    (parameter : Rational) :
    (1 : Rational) ≤ Projective.Line.Hermitian.Proj.weight
      ⟨curve.numeratorAt parameter, curve.denominatorAt parameter⟩ := by
  rw [denominatorFormula parameter]
  simp only [Projective.Line.Hermitian.Proj.weight, Gaussian.Norm.Basic.normSq_one]
  have added := Rat.Fraction.Order.Arithmetic.add_le_add_right_direct
    (Gaussian.Norm.Basic.normSq_nonneg (curve.numeratorAt parameter)) 1
  simpa only [Rat.Fraction.Field.zero_add] using added

end

open Purelib.LinearAlgebra in
open Purelib.RationalFunctions in
/-- An invertible Gaussian matrix preserves nonzero homogeneous coordinates of a rational curve.

The source has a nonzero coordinate at every parameter, and the matrix determinant is nonzero. Its transformed curve
therefore remains projectively valid at each parameter. -/
public theorem transformedProjectiveValid
    (matrix : Coordinates2.Matrix.GaussianMatrix)
    (determinantNonzero :
      Coordinates2.Matrix.BoundaryAdjugate.determinant matrix ≠ 0)
    (source : Curve.RationalCurve)
    (sourceValid : ∀ parameter,
      Projective.Line.Gaussian.Proj.HasNonzeroCoordinate
        ⟨source.numeratorAt parameter, source.denominatorAt parameter⟩)
    (parameter : Rational) :
    Projective.Line.Gaussian.Proj.HasNonzeroCoordinate
      ⟨(source.transform matrix).numeratorAt parameter,
        (source.transform matrix).denominatorAt parameter⟩ := by
  have acted := Projective.Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
    (matrix := matrix)
    (point := ⟨source.numeratorAt parameter, source.denominatorAt parameter⟩)
    determinantNonzero (sourceValid parameter)
  simpa only [Projective.Line.Matrix.act,
    Curve.RationalCurve.numeratorAt_transform,
    Curve.RationalCurve.denominatorAt_transform]
    using acted

end

end Geometry.Projective.Hermitian.Parametrization

open Purelib.Data
open Purelib.Geometry
open Purelib.RationalFunctions
namespace RationalFunctions.Curve.Projective

/-- A curve whose homogeneous denominator is identically one has projective weight at least one. -/
theorem unitDenominatorWeightLower
    (curve : Curve.RationalCurve)
    (denominatorFormula : ∀ parameter, curve.denominatorAt parameter = 1)
    (parameter : Rational) :
    (1 : Rational) ≤ Projective.Line.Hermitian.Proj.weight
      ⟨curve.numeratorAt parameter, curve.denominatorAt parameter⟩ := by
  rw [denominatorFormula parameter]
  simp only [Projective.Line.Hermitian.Proj.weight, Gaussian.Norm.Basic.normSq_one]
  have added := Rat.Fraction.Order.Arithmetic.add_le_add_right_direct
    (Gaussian.Norm.Basic.normSq_nonneg (curve.numeratorAt parameter)) 1
  simpa only [Rat.Fraction.Field.zero_add] using added

/-- A curve with denominator quadrance arising from the circle chart has projective weight at least one.

The homogeneous denominator is the real Gaussian value parameter squared plus one, so its quadrance alone supplies the
lower bound. -/
theorem circleDenominatorWeightLower
    (curve : Curve.RationalCurve)
    (denominatorFormula : ∀ parameter,
      curve.denominatorAt parameter = ⟨parameter ^ 2 + 1, 0⟩)
    (parameter : Rational) :
    (1 : Rational) ≤ Projective.Line.Hermitian.Proj.weight
      ⟨curve.numeratorAt parameter, curve.denominatorAt parameter⟩ := by
  have oneLe : (1 : Rational) ≤ parameter ^ 2 + 1 := by
    have added := Rat.Fraction.Order.Arithmetic.add_le_add_right_direct
      (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct parameter) 1
    simpa only [Rat.Fraction.Field.zero_add] using added
  have squareLe : (1 : Rational) ≤ (parameter ^ 2 + 1) ^ 2 := by
    simpa only [one_pow] using
      Rat.Fraction.Order.Arithmetic.pow_le_pow_direct (by decide) oneLe 2
  rw [denominatorFormula parameter]
  change 1 ≤ Data.Gaussian.Norm.Basic.normSq (curve.numeratorAt parameter) +
    ((parameter ^ 2 + 1) ^ 2 + 0 ^ 2)
  exact squareLe.trans (by
    calc
      (parameter ^ 2 + 1) ^ 2 ≤
          Data.Gaussian.Norm.Basic.normSq (curve.numeratorAt parameter) +
            (parameter ^ 2 + 1) ^ 2 :=
        le_add_of_nonneg_left (Gaussian.Norm.Basic.normSq_nonneg (curve.numeratorAt parameter))
      _ = Data.Gaussian.Norm.Basic.normSq (curve.numeratorAt parameter) +
          ((parameter ^ 2 + 1) ^ 2 + 0 ^ 2) := by ring1)

end RationalFunctions.Curve.Projective

end Purelib

end
