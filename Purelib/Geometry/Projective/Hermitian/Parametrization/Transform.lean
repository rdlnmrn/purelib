module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Chordal.Matrix
public import Purelib.Geometry.Projective.Chordal.Matrix.WeightLower
import Purelib.Geometry.Projective.Hermitian.Basic
public import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
public import Purelib.Geometry.Projective.Hermitian.Pullback
import Purelib.Geometry.Projective.Homography.Basic
public import Purelib.Geometry.Projective.Homography.Inverse
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Hermitian
import Purelib.Geometry.Projective.Line.Matrix
public import Purelib.Geometry.Projective.Line.Matrix.Gaussian
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RationalFunctions.Curve.Transform
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Line.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Chordal.Matrix

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Parametrization

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.Geometry.Projective.Line.Hermitian

open Purelib.Geometry.Projective.Line.Matrix

open Purelib.LinearAlgebra.Coordinates2.Matrix

open Purelib.RationalFunctions

open Purelib.RationalFunctions.Curve

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
section Parametrization

/-- Construct the transported curve with its explicit rational weight bound. The boundary equation is supplied by the
particular comparison form. -/
def ofTransformedCurve
    (form : Hermitian.HermitianForm) (source : Curve.RationalCurve) (matrix : GaussianMatrix)
    (sourceLower : Fraction.Rational)
    (sourceLowerPositive : 0 < sourceLower)
    (sourceLowerLe : ∀ parameter, sourceLower ≤
      Proj.weight
        ⟨source.numeratorAt parameter, source.denominatorAt parameter⟩)
    (sourceValid : ∀ parameter,
      Proj.HasNonzeroCoordinate
        ⟨source.numeratorAt parameter, source.denominatorAt parameter⟩)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    (onBoundary : ∀ parameter,
      (source.transform matrix).denominatorAt parameter ≠ 0 →
        form.eval ((source.transform matrix).point parameter) = 0) :
    Parametrization form := by
  refine
    { curve := source.transform matrix
      weightLower := Data.Gaussian.Norm.Basic.normSq (BoundaryAdjugate.determinant matrix) *
          sourceLower /
        Mat2.actionWeightCoefficient
          (BoundaryAdjugate.adjugate matrix)
      weightLowerPositive := ?_
      weightLower_le := ?_
      projectiveValid := ?_
      onBoundary := onBoundary }
  · exact Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.mul_pos_direct
        (Data.Gaussian.Norm.Basic.normSq_pos determinantNonzero) sourceLowerPositive)
      (Mat2.actionWeightCoefficient_pos
        (BoundaryAdjugate.adjugate matrix))
  · intro parameter
    have bound := Parametrization.transformedPointWeightLower matrix sourceLower
      ⟨source.numeratorAt parameter, source.denominatorAt parameter⟩
      (sourceLowerLe parameter)
    simpa only [
      RationalCurve.numeratorAt_transform,
      RationalCurve.denominatorAt_transform,
      Line.Matrix.act] using bound
  · intro parameter
    have acted := Gaussian.Mat2.act_hasNonzeroCoordinate
      (matrix := matrix)
      (point := ⟨source.numeratorAt parameter, source.denominatorAt parameter⟩)
      determinantNonzero (sourceValid parameter)
    simpa only [Line.Matrix.act,
      RationalCurve.numeratorAt_transform,
      RationalCurve.denominatorAt_transform]
      using acted

/-- Transport a total source parameterization into the forward/input coordinate. The resulting Hermitian form is exactly
the adjugate pullback used by `inputIncrementalAdvanceFormula`. -/
def pushForward
    {form : Hermitian.HermitianForm} (source : Parametrization form)
    (sourceTotal : ∀ parameter, source.curve.denominatorAt parameter ≠ 0)
    (forward : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant forward ≠ 0) :
    Parametrization
      (Hermitian.pullbackForm
        (BoundaryAdjugate.adjugate forward) form) := by
  refine ofTransformedCurve _ source.curve forward
    source.weightLower
    source.weightLowerPositive source.weightLower_le source.projectiveValid
    determinantNonzero ?_
  intro parameter transformedDenominatorNonzero
  have sourceDenominatorNonzero := sourceTotal parameter
  have forwardDenominatorNonzero :
      Homography.Basic.denominator forward (source.curve.point parameter) ≠ 0 := by
    intro forwardZero
    apply transformedDenominatorNonzero
    rw [RationalCurve.denominatorAt_transform_eq
      forward source.curve parameter sourceDenominatorNonzero,
      forwardZero, Data.Gaussian.Basic.zero_mul]
  have pointIdentity :=
    RationalCurve.point_transform
      forward source.curve parameter sourceDenominatorNonzero
        forwardDenominatorNonzero
  have inverseDenominatorNonzero :=
    Homography.adjugate_denominator_homographic_ne
      forward (source.curve.point parameter) determinantNonzero
        forwardDenominatorNonzero
  have inverseIdentity :=
    Homography.homographic_adjugate_forward_inverse
      forward (source.curve.point parameter) determinantNonzero
        forwardDenominatorNonzero
  rw [show (source.curve.transform forward).point parameter =
      Homography.Basic.homographic forward (source.curve.point parameter) by
        exact pointIdentity,
    Hermitian.eval_pullbackForm
      (BoundaryAdjugate.adjugate forward) form _
        inverseDenominatorNonzero,
    inverseIdentity,
    source.onBoundary parameter sourceDenominatorNonzero,
    Fraction.Field.mul_zero_direct]

end Parametrization
end Purelib.Geometry.Projective.Hermitian.Parametrization

end
