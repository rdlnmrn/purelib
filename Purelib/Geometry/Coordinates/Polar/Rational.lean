module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares
import Purelib.Geometry.Circles.Unit.Basic
public import Purelib.Geometry.Circles.Unit.Lines
import Purelib.Geometry.Circles.Unit.Parametrization
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Gaussian
public import Purelib.Geometry.Trigonometry.Turn.Composition
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.ExistsUnique
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Curves.Plane (Conic)

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Trigonometry.Turn

section
@[expose] public section

/-!
# Divine Proportions, Exercise 16.8: rational polar form

A Cartesian point is used as a finite Gaussian pair.  Multiplication and
scaling are explicit coordinate operations; no completed complex carrier is
introduced.  The unit-circle parameter is recovered by the finite quotient
`y / (1+x)`, and the chord through `-1` has the displayed equation
`lambda*x-y+lambda=0`.

The multiplication theorem uses the same `turnComposition` operation as
Exercise 9.2.  Its premise `1-lambda₁*lambda₂ != 0` is essential: when it
vanishes, the product unit point is the excluded point `[-1,0]`, so the finite
chart has no resulting parameter.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- The Gaussian point with the given rational-circle parameter and radial scale. -/
def rationalPolarPoint (radius parameter : K) : Plane.Point K
  :=
  Conic.gaussianScale radius (Conic.unitCirclePoint parameter)

/-- Express the rational polar point as a scaled square of its Gaussian chart factor. -/
theorem rationalPolarPoint_eq_scaled_square (radius parameter : K) :
    rationalPolarPoint radius parameter =
      Conic.gaussianScale (radius / (1 + parameter ^ 2))
        (Conic.gaussianMul (Conic.onePlusIParameter parameter)
          (Conic.onePlusIParameter parameter)) := by
  apply Plane.Point.ext <;>
    unfold rationalPolarPoint Conic.unitCirclePoint Conic.gaussianScale Conic.gaussianMul
      Conic.onePlusIParameter <;>
    dsimp only <;>
    simp only [ExplicitField.div_eq_mul_inv] <;>
    ring1

/-- When the turn-composition denominator is nonzero, the product `(1+i*left)(1+i*right)` is that denominator times the
next chart factor. -/
theorem gaussianMul_onePlusIParameter_eq_scale
    (left right : K) (compositionDenominatorNonzero :
      1 - left * right ≠ 0) :
    Conic.gaussianMul (Conic.onePlusIParameter left) (Conic.onePlusIParameter right) =
      Conic.gaussianScale (1 - left * right)
        (Conic.onePlusIParameter (Composition.turnComposition left right)) := by
  have compositionCancel :
      Composition.turnComposition left right * (1 - left * right) = left + right := by
    unfold Composition.turnComposition
    exact ExplicitField.div_mul_cancel (left + right)
      compositionDenominatorNonzero
  apply Plane.Point.ext
  · unfold Conic.gaussianMul Conic.gaussianScale Conic.onePlusIParameter
    dsimp only
    ring1
  · unfold Conic.gaussianMul Conic.gaussianScale Conic.onePlusIParameter
    dsimp only
    calc
      1 * right + left * 1 = left + right := by ring1
      _ =
          Composition.turnComposition left right * (1 - left * right) :=
        compositionCancel.symm
      _ = (1 - left * right) * Composition.turnComposition left right := by ring1

/-- Multiply rational polar points by multiplying radii and composing circle parameters.

The two circle denominators and the turn-composition denominator are assumed nonzero; the resulting parameter also has a
nonzero circle denominator. -/
theorem rationalPolarPoint_mul
    (leftRadius rightRadius leftParameter rightParameter : K)
    (leftSquareNotNegativeOne : leftParameter ^ 2 ≠ -1)
    (rightSquareNotNegativeOne : rightParameter ^ 2 ≠ -1)
    (compositionDenominatorNonzero :
      1 - leftParameter * rightParameter ≠ 0) :
    let composed := Composition.turnComposition leftParameter rightParameter
    composed ^ 2 ≠ -1 ∧
      Conic.gaussianMul
          (rationalPolarPoint leftRadius leftParameter)
          (rationalPolarPoint rightRadius rightParameter) =
        rationalPolarPoint (leftRadius * rightRadius) composed := by
  dsimp only
  let leftDenominator := 1 + leftParameter ^ 2
  let rightDenominator := 1 + rightParameter ^ 2
  let compositionDenominator := 1 - leftParameter * rightParameter
  let composed := Composition.turnComposition leftParameter rightParameter
  have leftDenominatorNonzero : leftDenominator ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff leftParameter).2
      leftSquareNotNegativeOne
  have rightDenominatorNonzero : rightDenominator ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff rightParameter).2
      rightSquareNotNegativeOne
  have composedSquareNotNegativeOne : composed ^ 2 ≠ -1 :=
    Conic.turnComposition_square_ne_negative_one leftParameter rightParameter
      leftSquareNotNegativeOne rightSquareNotNegativeOne
      compositionDenominatorNonzero
  have composedDenominatorNonzero : 1 + composed ^ 2 ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff composed).2
      composedSquareNotNegativeOne
  have leftCancel :
      (leftRadius / leftDenominator) * leftDenominator = leftRadius :=
    ExplicitField.div_mul_cancel leftRadius leftDenominatorNonzero
  have rightCancel :
      (rightRadius / rightDenominator) * rightDenominator = rightRadius :=
    ExplicitField.div_mul_cancel rightRadius rightDenominatorNonzero
  have compositionCancel :
      composed * compositionDenominator =
        leftParameter + rightParameter := by
    exact ExplicitField.div_mul_cancel
      (leftParameter + rightParameter) compositionDenominatorNonzero
  have denominatorIdentity :
      (1 + composed ^ 2) * compositionDenominator ^ 2 =
        leftDenominator * rightDenominator := by
    calc
      (1 + composed ^ 2) * compositionDenominator ^ 2 =
          compositionDenominator ^ 2 +
            (composed * compositionDenominator) ^ 2 := by ring1
      _ = compositionDenominator ^ 2 +
          (leftParameter + rightParameter) ^ 2 := by rw [compositionCancel]
      _ = leftDenominator * rightDenominator := by
        unfold leftDenominator rightDenominator compositionDenominator
        ring1
  have scalarEquality :
      (leftRadius / leftDenominator) *
          (rightRadius / rightDenominator) *
          compositionDenominator ^ 2 =
        (leftRadius * rightRadius) / (1 + composed ^ 2) := by
    apply ExplicitField.eq_of_mul_eq_mul_right composedDenominatorNonzero
    calc
      ((leftRadius / leftDenominator) *
            (rightRadius / rightDenominator) *
            compositionDenominator ^ 2) * (1 + composed ^ 2) =
          (leftRadius / leftDenominator) *
            (rightRadius / rightDenominator) *
            (leftDenominator * rightDenominator) := by
        rw [← denominatorIdentity]
        ring1
      _ = ((leftRadius / leftDenominator) * leftDenominator) *
          ((rightRadius / rightDenominator) * rightDenominator) := by ring1
      _ = leftRadius * rightRadius := by rw [leftCancel, rightCancel]
      _ = ((leftRadius * rightRadius) / (1 + composed ^ 2)) *
          (1 + composed ^ 2) :=
        (ExplicitField.div_mul_cancel
          (leftRadius * rightRadius) composedDenominatorNonzero).symm
  refine ⟨composedSquareNotNegativeOne, ?_⟩
  rw [rationalPolarPoint_eq_scaled_square,
    rationalPolarPoint_eq_scaled_square,
    rationalPolarPoint_eq_scaled_square]
  change Conic.gaussianMul
      (Conic.gaussianScale (leftRadius / leftDenominator)
        (Conic.gaussianMul (Conic.onePlusIParameter leftParameter)
          (Conic.onePlusIParameter leftParameter)))
      (Conic.gaussianScale (rightRadius / rightDenominator)
        (Conic.gaussianMul (Conic.onePlusIParameter rightParameter)
          (Conic.onePlusIParameter rightParameter))) =
    Conic.gaussianScale ((leftRadius * rightRadius) / (1 + composed ^ 2))
      (Conic.gaussianMul (Conic.onePlusIParameter composed)
        (Conic.onePlusIParameter composed))
  calc
    Conic.gaussianMul
        (Conic.gaussianScale (leftRadius / leftDenominator)
          (Conic.gaussianMul (Conic.onePlusIParameter leftParameter)
            (Conic.onePlusIParameter leftParameter)))
        (Conic.gaussianScale (rightRadius / rightDenominator)
          (Conic.gaussianMul (Conic.onePlusIParameter rightParameter)
            (Conic.onePlusIParameter rightParameter))) =
      Conic.gaussianScale
        ((leftRadius / leftDenominator) *
          (rightRadius / rightDenominator))
        (Conic.gaussianMul
          (Conic.gaussianMul (Conic.onePlusIParameter leftParameter)
            (Conic.onePlusIParameter leftParameter))
          (Conic.gaussianMul (Conic.onePlusIParameter rightParameter)
            (Conic.onePlusIParameter rightParameter))) :=
      Conic.gaussianMul_scale_scale _ _ _ _
    _ = Conic.gaussianScale
        ((leftRadius / leftDenominator) *
          (rightRadius / rightDenominator))
        (Conic.gaussianMul
          (Conic.gaussianMul (Conic.onePlusIParameter leftParameter)
            (Conic.onePlusIParameter rightParameter))
          (Conic.gaussianMul (Conic.onePlusIParameter leftParameter)
            (Conic.onePlusIParameter rightParameter))) := by
      rw [Conic.gaussianMul_squares]
    _ = Conic.gaussianScale
        ((leftRadius / leftDenominator) *
          (rightRadius / rightDenominator))
        (Conic.gaussianMul
          (Conic.gaussianScale compositionDenominator
            (Conic.onePlusIParameter composed))
          (Conic.gaussianScale compositionDenominator
            (Conic.onePlusIParameter composed))) := by
      rw [gaussianMul_onePlusIParameter_eq_scale leftParameter
        rightParameter compositionDenominatorNonzero]
    _ = Conic.gaussianScale
        ((leftRadius / leftDenominator) *
          (rightRadius / rightDenominator))
        (Conic.gaussianScale (compositionDenominator * compositionDenominator)
          (Conic.gaussianMul (Conic.onePlusIParameter composed)
            (Conic.onePlusIParameter composed))) := by
      rw [Conic.gaussianMul_scale_scale]
    _ = Conic.gaussianScale
        ((leftRadius / leftDenominator) *
          (rightRadius / rightDenominator) *
          compositionDenominator ^ 2)
        (Conic.gaussianMul (Conic.onePlusIParameter composed)
          (Conic.onePlusIParameter composed)) := by
      rw [Conic.gaussianScale_scale]
      congr 1
      ring1
    _ = Conic.gaussianScale ((leftRadius * rightRadius) / (1 + composed ^ 2))
        (Conic.gaussianMul (Conic.onePlusIParameter composed)
          (Conic.onePlusIParameter composed)) := by rw [scalarEquality]

/-- Combine rational circle parametrization, chord intersection and Gaussian polar multiplication.

Over a nontrivial explicit field with decidable equality and nonzero two, every circle point except the excluded
endpoint has a unique chart parameter. The same parameter describes its chord and obeys the displayed multiplication
law. -/
theorem exercise_16_8 [Nontrivial K] [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    (∀ point : Plane.Point K,
      Conic.unitCircle.Contains point → point ≠ Conic.unitCircleExcludedPoint →
        ∃! parameter : K,
          parameter ^ 2 ≠ -1 ∧ point = Conic.unitCirclePoint parameter) ∧
    (∀ parameter : K, parameter ^ 2 ≠ -1 →
      Conic.unitCircle.Contains (Conic.unitCirclePoint parameter)) ∧
    (∀ (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1),
      (Incidence.lineThrough Conic.unitCircleExcludedPoint (Conic.unitCirclePoint parameter)
          (Ne.symm (Conic.unitCirclePoint_ne_excluded parameter
            squareNotNegativeOne twoNonzero))).Equivalent
            (Conic.unitCircleParameterLine parameter) ∧
        Conic.imaginaryParameterPoint parameter =
          Intersection.lineIntersection Conic.imaginaryAxis (Conic.unitCircleParameterLine parameter)
            (Conic.imaginaryAxis_parameterLine_nonparallel parameter)) ∧
    (∀ (leftRadius rightRadius leftParameter rightParameter : K),
      leftParameter ^ 2 ≠ -1 → rightParameter ^ 2 ≠ -1 →
      1 - leftParameter * rightParameter ≠ 0 →
      let composed := Composition.turnComposition leftParameter rightParameter
      composed ^ 2 ≠ -1 ∧
        Conic.gaussianMul
            (rationalPolarPoint leftRadius leftParameter)
            (rationalPolarPoint rightRadius rightParameter) =
          rationalPolarPoint (leftRadius * rightRadius) composed) := by
  refine ⟨?_, Conic.unitCirclePoint_contains, ?_, rationalPolarPoint_mul⟩
  · intro point pointOnCircle pointNotExcluded
    exact Conic.unitCirclePoint_existsUnique point twoNonzero pointOnCircle
      pointNotExcluded
  · intro parameter squareNotNegativeOne
    exact ⟨Conic.unitCircleParameterLine_equivalent_lineThrough parameter
      squareNotNegativeOne twoNonzero,
      Conic.imaginaryParameterPoint_is_intersection parameter⟩

end

end Purelib.Curves.Plane.Conic

end
