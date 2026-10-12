module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Projective.Hermitian.Comparison
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
public import Purelib.Geometry.Projective.Hermitian.Parametrization.Transform
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Projective.Homography.Inverse
import Purelib.LinearAlgebra.Coordinates2.Matrix
public import Purelib.RationalFunctions.Curve.Canonical.Circle.Basic
public import Purelib.RationalFunctions.Curve.Canonical.Line
public import Purelib.RationalFunctions.Curve.Projective.Bounds
import Purelib.RationalFunctions.Curve.Transform
import Init.Prelude
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Hermitian
import Purelib.RationalFunctions.Curve.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Parametrization

open Purelib.LinearAlgebra.Coordinates2.Matrix

open Purelib.RationalFunctions.Curve

open Purelib.RationalFunctions.Curve.Canonical

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

namespace Purelib.Geometry.Projective.Hermitian.Parametrization

/-- Pull the canonical vertical line back through an invertible homography. -/
def realComparison
    (matrix : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    (threshold : Fraction.Rational) :
    Parametrization (Hermitian.realComparisonForm matrix threshold) := by
  let source := Line.realLine threshold
  refine Parametrization.ofTransformedCurve _ source
    (BoundaryAdjugate.adjugate matrix) 1 (by decide)
    (Projective.unitDenominatorWeightLower source
      (Line.realLine_denominatorAt threshold))
    (fun parameter => Or.inr
      (Line.realLine_denominator_ne threshold parameter))
    (by
      rw [BoundaryAdjugate.determinant_adjugate]
      exact determinantNonzero) ?_
  intro parameter transformedDenominatorNonzero
  have sourceDenominatorNonzero : source.denominatorAt parameter ≠ 0 :=
    Line.realLine_denominator_ne
      threshold parameter
  have inverseDenominatorNonzero :
      Homography.Basic.denominator (BoundaryAdjugate.adjugate matrix)
        (source.point parameter) ≠ 0 := by
    intro inverseDenominatorZero
    apply transformedDenominatorNonzero
    rw [RationalCurve.denominatorAt_transform_eq
      (BoundaryAdjugate.adjugate matrix) source parameter
        sourceDenominatorNonzero,
      inverseDenominatorZero, Data.Gaussian.Basic.zero_mul]
  have pointIdentity :=
    RationalCurve.point_transform
      (BoundaryAdjugate.adjugate matrix) source parameter
        sourceDenominatorNonzero inverseDenominatorNonzero
  have forwardDenominatorNonzero :=
    Homography.denominator_inverse_tail_ne matrix
      (source.point parameter) determinantNonzero inverseDenominatorNonzero
  have inverseIdentity :=
    Homography.homographic_adjugate_inverse matrix
      (source.point parameter) determinantNonzero inverseDenominatorNonzero
  rw [show (source.transform
      (BoundaryAdjugate.adjugate matrix)).point parameter =
      Homography.Basic.homographic (BoundaryAdjugate.adjugate matrix)
        (source.point parameter) by exact pointIdentity]
  apply (Hermitian.real_homographic_eq_iff matrix _ threshold
    forwardDenominatorNonzero).1
  rw [inverseIdentity]
  exact congrArg Data.Gaussian.Basic.re
    (Line.realLine_point threshold parameter)

/-- Pull the canonical horizontal line back through an invertible homography. -/
def imaginaryComparison
    (matrix : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    (threshold : Fraction.Rational) :
    Parametrization (Hermitian.imagComparisonForm matrix threshold) := by
  let source := Line.imaginaryLine threshold
  refine Parametrization.ofTransformedCurve _ source
    (BoundaryAdjugate.adjugate matrix) 1 (by decide)
    (Projective.unitDenominatorWeightLower source
      (Line.imaginaryLine_denominatorAt threshold))
    (fun parameter => Or.inr
      (Line.imaginaryLine_denominator_ne
        threshold parameter))
    (by
      rw [BoundaryAdjugate.determinant_adjugate]
      exact determinantNonzero) ?_
  intro parameter transformedDenominatorNonzero
  have sourceDenominatorNonzero : source.denominatorAt parameter ≠ 0 :=
    Line.imaginaryLine_denominator_ne
      threshold parameter
  have inverseDenominatorNonzero :
      Homography.Basic.denominator (BoundaryAdjugate.adjugate matrix)
        (source.point parameter) ≠ 0 := by
    intro inverseDenominatorZero
    apply transformedDenominatorNonzero
    rw [RationalCurve.denominatorAt_transform_eq
      (BoundaryAdjugate.adjugate matrix) source parameter
        sourceDenominatorNonzero,
      inverseDenominatorZero, Data.Gaussian.Basic.zero_mul]
  have pointIdentity :=
    RationalCurve.point_transform
      (BoundaryAdjugate.adjugate matrix) source parameter
        sourceDenominatorNonzero inverseDenominatorNonzero
  have forwardDenominatorNonzero :=
    Homography.denominator_inverse_tail_ne matrix
      (source.point parameter) determinantNonzero inverseDenominatorNonzero
  have inverseIdentity :=
    Homography.homographic_adjugate_inverse matrix
      (source.point parameter) determinantNonzero inverseDenominatorNonzero
  rw [show (source.transform
      (BoundaryAdjugate.adjugate matrix)).point parameter =
      Homography.Basic.homographic (BoundaryAdjugate.adjugate matrix)
        (source.point parameter) by exact pointIdentity]
  apply (Hermitian.imag_homographic_eq_iff matrix _ threshold
    forwardDenominatorNonzero).1
  rw [inverseIdentity]
  exact congrArg Data.Gaussian.Basic.im
    (Line.imaginaryLine_point threshold parameter)

/-- Pull a centered circle through an invertible homography. The displayed base point supplies the rational
stereographic parameterization. -/
def normComparison
    (matrix : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    (base : Data.Gaussian.Basic.Canonical) :
    Parametrization (Hermitian.normComparisonForm matrix
        (Data.Gaussian.Norm.Basic.normSq
      base)) := by
  let source := Circle.circle base
  refine Parametrization.ofTransformedCurve _ source
    (BoundaryAdjugate.adjugate matrix) 1 (by decide)
    (Projective.circleDenominatorWeightLower source
      (Circle.circle_denominatorAt base))
    (fun parameter => Or.inr
      (Circle.circle_denominator_ne base parameter))
    (by
      rw [BoundaryAdjugate.determinant_adjugate]
      exact determinantNonzero) ?_
  intro parameter transformedDenominatorNonzero
  have sourceDenominatorNonzero : source.denominatorAt parameter ≠ 0 :=
    Circle.circle_denominator_ne base parameter
  have inverseDenominatorNonzero :
      Homography.Basic.denominator (BoundaryAdjugate.adjugate matrix)
        (source.point parameter) ≠ 0 := by
    intro inverseDenominatorZero
    apply transformedDenominatorNonzero
    rw [RationalCurve.denominatorAt_transform_eq
      (BoundaryAdjugate.adjugate matrix) source parameter
        sourceDenominatorNonzero,
      inverseDenominatorZero, Data.Gaussian.Basic.zero_mul]
  have pointIdentity :=
    RationalCurve.point_transform
      (BoundaryAdjugate.adjugate matrix) source parameter
        sourceDenominatorNonzero inverseDenominatorNonzero
  have forwardDenominatorNonzero :=
    Homography.denominator_inverse_tail_ne matrix
      (source.point parameter) determinantNonzero inverseDenominatorNonzero
  have inverseIdentity :=
    Homography.homographic_adjugate_inverse matrix
      (source.point parameter) determinantNonzero inverseDenominatorNonzero
  rw [show (source.transform
      (BoundaryAdjugate.adjugate matrix)).point parameter =
      Homography.Basic.homographic (BoundaryAdjugate.adjugate matrix)
        (source.point parameter) by exact pointIdentity]
  apply (Hermitian.norm_homographic_eq_iff matrix _ (Data.Gaussian.Norm.Basic.normSq base)
    forwardDenominatorNonzero).1
  rw [inverseIdentity]
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical,
    Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact Circle.normSq_circle_point base parameter

/-- Reciprocal chart of the same pulled-back centered norm boundary. Its zero parameter supplies the projective point
missed by `normComparison`. -/
def normComparisonReciprocal
    (matrix : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    (base : Data.Gaussian.Basic.Canonical) :
    Parametrization (Hermitian.normComparisonForm matrix
        (Data.Gaussian.Norm.Basic.normSq
      base)) := by
  let source := Circle.reciprocalCircle base
  refine Parametrization.ofTransformedCurve _ source
    (BoundaryAdjugate.adjugate matrix) 1 (by decide)
    (Projective.circleDenominatorWeightLower source
      (Circle.reciprocalCircle_denominatorAt base))
    (fun parameter => Or.inr
      (Circle.reciprocalCircle_denominator_ne
        base parameter))
    (by
      rw [BoundaryAdjugate.determinant_adjugate]
      exact determinantNonzero) ?_
  intro parameter transformedDenominatorNonzero
  have sourceDenominatorNonzero : source.denominatorAt parameter ≠ 0 :=
    Circle.reciprocalCircle_denominator_ne
      base parameter
  have inverseDenominatorNonzero :
      Homography.Basic.denominator (BoundaryAdjugate.adjugate matrix)
        (source.point parameter) ≠ 0 := by
    intro inverseDenominatorZero
    apply transformedDenominatorNonzero
    rw [RationalCurve.denominatorAt_transform_eq
      (BoundaryAdjugate.adjugate matrix) source parameter
        sourceDenominatorNonzero,
      inverseDenominatorZero, Data.Gaussian.Basic.zero_mul]
  have pointIdentity :=
    RationalCurve.point_transform
      (BoundaryAdjugate.adjugate matrix) source parameter
        sourceDenominatorNonzero inverseDenominatorNonzero
  have forwardDenominatorNonzero :=
    Homography.denominator_inverse_tail_ne matrix
      (source.point parameter) determinantNonzero inverseDenominatorNonzero
  have inverseIdentity :=
    Homography.homographic_adjugate_inverse matrix
      (source.point parameter) determinantNonzero inverseDenominatorNonzero
  rw [show (source.transform
      (BoundaryAdjugate.adjugate matrix)).point parameter =
      Homography.Basic.homographic (BoundaryAdjugate.adjugate matrix)
        (source.point parameter) by exact pointIdentity]
  apply (Hermitian.norm_homographic_eq_iff matrix _ (Data.Gaussian.Norm.Basic.normSq base)
    forwardDenominatorNonzero).1
  rw [inverseIdentity]
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical,
    Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact Circle.normSq_reciprocalCircle_point
    base parameter
end Purelib.Geometry.Projective.Hermitian.Parametrization

end
