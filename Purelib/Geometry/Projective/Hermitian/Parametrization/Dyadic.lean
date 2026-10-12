module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
public import Purelib.Geometry.Projective.Hermitian.Radial
import Purelib.RationalFunctions.Curve.Canonical.Circle.Basic
public import Purelib.RationalFunctions.Curve.Canonical.Circle.Dyadic
public import Purelib.RationalFunctions.Curve.Projective.Bounds
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Hermitian
import Purelib.RationalFunctions.Curve.Basic
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Field.Defs

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

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

/-- Canonical centered norm boundary. -/
def affineNorm (base : Data.Gaussian.Basic.Canonical) :
    Parametrization
      (Hermitian.affineNormComparisonForm (Data.Gaussian.Norm.Basic.normSq base)) := by
  let curve := Circle.circle base
  refine
    { curve := curve
      weightLower := 1
      weightLowerPositive := by decide
      weightLower_le := Projective.circleDenominatorWeightLower curve
        (Circle.circle_denominatorAt base)
      projectiveValid := fun parameter => Or.inr
        (Circle.circle_denominator_ne base parameter)
      onBoundary := ?_ }
  intro parameter _denominatorNonzero
  rw [Hermitian.eval_affineNormComparisonForm,
    Data.Gaussian.Norm.Basic.normSq_eq_canonical,
    Data.Gaussian.Norm.Basic.normSq_eq_canonical,
    Circle.normSq_circle_point]
  ring1

/-- Boundary `normSq z = 2^exponent`. -/
def affineNormDyadic (exponent : Nat) :
    Parametrization
      (Hermitian.affineNormComparisonForm
        ((2 : Fraction.Rational) ^ exponent)) := by
  let curve := Circle.dyadicCircle exponent
  refine
    { curve := curve
      weightLower := 1
      weightLowerPositive := by decide
      weightLower_le := Projective.circleDenominatorWeightLower curve
        (by
          intro parameter
          exact Circle.circle_denominatorAt
            (Power.natPow Canonical.gamma exponent) parameter)
      projectiveValid := fun parameter => Or.inr (by
        simpa [curve, Circle.dyadicCircle] using
          Circle.circle_denominator_ne
            (Power.natPow Canonical.gamma exponent) parameter)
      onBoundary := ?_ }
  intro parameter _denominatorNonzero
  rw [Hermitian.eval_affineNormComparisonForm,
    Circle.normSq_dyadicCircle_point]
  ring1

/-- The dyadic norm-boundary parametrization has nonzero denominator at every rational parameter. -/
theorem affineNormDyadic_total (exponent : Nat) (parameter
  : Fraction.Rational) :
    (affineNormDyadic exponent).curve.denominatorAt parameter ≠ 0 :=
  by
    simpa [affineNormDyadic, Circle.dyadicCircle]
      using
      Circle.circle_denominator_ne
        (Power.natPow Canonical.gamma exponent) parameter

/-- Boundary `2^exponent * normSq z = 1`. -/
def scaledNormOne (exponent : Nat) :
    Parametrization
      (Hermitian.scaledNormComparisonForm exponent 1) := by
  let curve := Circle.inverseDyadicCircle exponent
  refine
    { curve := curve
      weightLower := 1
      weightLowerPositive := by decide
      weightLower_le := Projective.circleDenominatorWeightLower curve
        (Circle.circle_denominatorAt
          ((Power.natPow Canonical.gamma exponent)⁻¹))
      projectiveValid := fun parameter => Or.inr
        (Circle.circle_denominator_ne
          ((Power.natPow Canonical.gamma exponent)⁻¹) parameter)
      onBoundary := ?_ }
  intro parameter _denominatorNonzero
  rw [Hermitian.eval_scaledNormComparisonForm,
    Circle.normSq_inverseDyadicCircle_point]
  have powerPositive : 0 < (2 : Fraction.Rational) ^ exponent :=
    Fraction.Order.Arithmetic.pow_pos_direct (by decide) exponent
  rw [Fraction.Field.mul_inv_cancel _ powerPositive.ne']
  ring1

/-- The inverse-dyadic circle parametrization has nonzero denominator at every rational parameter. -/
theorem scaledNormOne_total (exponent : Nat) (parameter :
  Fraction.Rational) :
    (scaledNormOne exponent).curve.denominatorAt parameter ≠ 0 :=
  by
    simpa only [scaledNormOne,
      Circle.inverseDyadicCircle,
      Circle.circle,
      RationalCurve.denominatorAt] using
      Circle.circle_denominator_ne
        ((Power.natPow Canonical.gamma exponent)⁻¹) parameter

/-- Boundary `2^exponent * normSq z = 2`. -/
def scaledNormTwo (exponent : Nat) :
    Parametrization
      (Hermitian.scaledNormComparisonForm exponent 2) := by
  let curve := Circle.lowUpperCircle exponent
  refine
    { curve := curve
      weightLower := 1
      weightLowerPositive := by decide
      weightLower_le := Projective.circleDenominatorWeightLower curve (by
        intro parameter
        cases exponent with
        | zero =>
            exact Circle.circle_denominatorAt
              (Power.natPow Canonical.gamma 1) parameter
        | succ exponent =>
            exact Circle.circle_denominatorAt
              ((Power.natPow Canonical.gamma exponent)⁻¹) parameter)
      projectiveValid := fun parameter => Or.inr (by
        cases exponent with
        | zero =>
            exact Circle.circle_denominator_ne
              (Power.natPow Canonical.gamma 1) parameter
        | succ exponent =>
            exact Circle.circle_denominator_ne
              ((Power.natPow Canonical.gamma exponent)⁻¹) parameter)
      onBoundary := ?_ }
  intro parameter _denominatorNonzero
  rw [Hermitian.eval_scaledNormComparisonForm,
    Circle.scaled_normSq_lowUpperCircle_point]
  ring1

/-- The scaled-norm-two parametrization has nonzero denominator at every rational parameter. -/
theorem scaledNormTwo_total (exponent : Nat) (parameter :
  Fraction.Rational) :
    (scaledNormTwo exponent).curve.denominatorAt parameter ≠ 0 := by
  cases exponent with
  | zero =>
      exact Circle.circle_denominator_ne
        (Power.natPow Canonical.gamma 1) parameter
  | succ exponent =>
      exact Circle.circle_denominator_ne
        ((Power.natPow Canonical.gamma exponent)⁻¹) parameter

end Purelib.Geometry.Projective.Hermitian.Parametrization

end
