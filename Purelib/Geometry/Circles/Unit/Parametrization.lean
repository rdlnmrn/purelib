module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares
import Purelib.Geometry.Circles.Projective.Basic
import Purelib.Geometry.Circles.Projective.Parametrization
public import Purelib.Geometry.Circles.Unit.Basic
import Purelib.Geometry.Circles.Unit.Projective
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Determinant
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

open Purelib.Geometry.Plane.Point

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

/-- Recover the parameter of a non-excluded unit-circle point. -/
def unitCircleParameter (point : Plane.Point K) : K :=
  point.y / (1 + point.x)

/-- An admissible unit-circle parameter satisfies `y = parameter * (1 + x)`.

The nonzero chart denominator is cancelled explicitly; the equation retains the parameter before any division by `1 +
x`. -/
public theorem unitCirclePoint_parameter_equation
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    (Conic.unitCirclePoint parameter).y =
      parameter * (1 + (Conic.unitCirclePoint parameter).x) := by
  let denominator := 1 + parameter ^ 2
  have denominatorNonzero : denominator ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter).2
      squareNotNegativeOne
  have realCancel :
      ((1 - parameter ^ 2) / denominator) * denominator =
        1 - parameter ^ 2 :=
    ExplicitField.div_mul_cancel
      (1 - parameter ^ 2) denominatorNonzero
  have imaginaryCancel :
      ((2 * parameter) / denominator) * denominator = 2 * parameter :=
    ExplicitField.div_mul_cancel
      (2 * parameter) denominatorNonzero
  apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
  change ((2 * parameter) / denominator) * denominator =
    (parameter * (1 + (1 - parameter ^ 2) / denominator)) * denominator
  calc
    ((2 * parameter) / denominator) * denominator =
        2 * parameter := imaginaryCancel
    _ = parameter *
        (denominator + (1 - parameter ^ 2)) := by
      unfold denominator
      ring1
    _ = parameter *
        (((1 - parameter ^ 2) / denominator) * denominator +
          denominator) := by rw [realCancel]; ring1
    _ = (parameter *
        (1 + (1 - parameter ^ 2) / denominator)) * denominator := by ring1

/-- For an admissible parameter, `(1 + x) * (1 + parameter²)` equals two. -/
private theorem unitCirclePoint_one_plus_x_times_denominator
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    (1 + (Conic.unitCirclePoint parameter).x) * (1 + parameter ^ 2) = 2 := by
  have denominatorNonzero : 1 + parameter ^ 2 ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter).2
      squareNotNegativeOne
  have realCancel :
      ((1 - parameter ^ 2) / (1 + parameter ^ 2)) *
          (1 + parameter ^ 2) = 1 - parameter ^ 2 :=
    ExplicitField.div_mul_cancel
      (1 - parameter ^ 2) denominatorNonzero
  change (1 + (1 - parameter ^ 2) / (1 + parameter ^ 2)) *
    (1 + parameter ^ 2) = 2
  calc
    (1 + (1 - parameter ^ 2) / (1 + parameter ^ 2)) *
        (1 + parameter ^ 2) =
      (1 + parameter ^ 2) +
        ((1 - parameter ^ 2) / (1 + parameter ^ 2)) *
          (1 + parameter ^ 2) := by ring1
    _ = 2 := by rw [realCancel]; ring1

/-- The finite quotient `y/(1+x)` recovers an admissible unit-circle parameter. -/
theorem unitCircleParameter_unitCirclePoint
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1)
    (twoNonzero : (2 : K) ≠ 0) :
    unitCircleParameter (Conic.unitCirclePoint parameter) = parameter := by
  have onePlusXNonzero : 1 + (Conic.unitCirclePoint parameter).x ≠ 0 := by
    intro onePlusXZero
    apply twoNonzero
    calc
      (2 : K) =
          (1 + (Conic.unitCirclePoint parameter).x) *
            (1 + parameter ^ 2) :=
        (unitCirclePoint_one_plus_x_times_denominator parameter
          squareNotNegativeOne).symm
      _ = 0 := by rw [onePlusXZero]; ring1
  apply ExplicitField.eq_of_mul_eq_mul_right onePlusXNonzero
  calc
    unitCircleParameter (Conic.unitCirclePoint parameter) *
        (1 + (Conic.unitCirclePoint parameter).x) =
      (Conic.unitCirclePoint parameter).y :=
        ExplicitField.div_mul_cancel _ onePlusXNonzero
    _ = parameter * (1 + (Conic.unitCirclePoint parameter).x) :=
      unitCirclePoint_parameter_equation parameter squareNotNegativeOne

/-- An admissible parameter avoids the excluded point `[-1,0]` when two is nonzero. -/
theorem unitCirclePoint_ne_excluded
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1)
    (twoNonzero : (2 : K) ≠ 0) :
    Conic.unitCirclePoint parameter ≠ Conic.unitCircleExcludedPoint := by
  intro pointEqual
  have xEqual := congrArg Plane.Point.x pointEqual
  change (Conic.unitCirclePoint parameter).x = -1 at xEqual
  have onePlusXZero : 1 + (Conic.unitCirclePoint parameter).x = 0 := by
    rw [xEqual]
    ring1
  apply twoNonzero
  calc
    (2 : K) =
        (1 + (Conic.unitCirclePoint parameter).x) * (1 + parameter ^ 2) :=
      (unitCirclePoint_one_plus_x_times_denominator parameter
        squareNotNegativeOne).symm
    _ = 0 := by rw [onePlusXZero]; ring1

/-- The unit-circle chart is injective on its admissible parameters. -/
theorem unitCirclePoint_injective
    (left right : K)
    (leftSquareNotNegativeOne : left ^ 2 ≠ -1)
    (rightSquareNotNegativeOne : right ^ 2 ≠ -1)
    (twoNonzero : (2 : K) ≠ 0)
    (pointsEqual : Conic.unitCirclePoint left = Conic.unitCirclePoint right) :
    left = right := by
  calc
    left = unitCircleParameter (Conic.unitCirclePoint left) :=
      (unitCircleParameter_unitCirclePoint left
        leftSquareNotNegativeOne twoNonzero).symm
    _ = unitCircleParameter (Conic.unitCirclePoint right) := by rw [pointsEqual]
    _ = right := unitCircleParameter_unitCirclePoint right
      rightSquareNotNegativeOne twoNonzero

end

end Purelib.Curves.Plane.Conic

end

section
/-!
# Divine Proportions, §16.3: the unit circle

The source's map `[x,y] ↦ [2y-1,2x]` is stored as an executable point
transformation.  Its unit-circle equation is exactly four times the
projective-circle equation, so Theorem 108 follows from Theorem 107 with one
visible characteristic-two exclusion in the reverse direction.
-/

@[expose] public section

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- Every admissible rational parameter gives a point on the unit circle. -/
theorem unitCirclePoint_contains [Nontrivial K]
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    Conic.unitCircle.Contains (Conic.unitCirclePoint parameter) := by
  rw [← Conic.projectiveToUnit_projectiveCirclePoint parameter
    squareNotNegativeOne]
  exact Conic.projectiveToUnit_contains (Conic.projectiveCirclePoint parameter)
    (Conic.projectiveCirclePoint_contains parameter squareNotNegativeOne)

/-- Converse half of Theorem 108: every non-excluded unit-circle point constructs its projective parameter. -/
theorem unitCirclePoint_exists [Nontrivial K] [DecidableEq K]
    (point : Plane.Point K) (twoNonzero : (2 : K) ≠ 0)
    (pointOnCircle : Conic.unitCircle.Contains point)
    (pointNotExcluded : point ≠ Conic.unitCircleExcludedPoint) :
    ∃ parameter : K,
      parameter ^ 2 ≠ -1 ∧ point = Conic.unitCirclePoint parameter := by
  let projectivePoint := Conic.unitToProjective point
  have projectivePointOnCircle :
      Conic.projectiveCircle.Contains projectivePoint :=
    Conic.unitToProjective_contains point twoNonzero pointOnCircle
  have recovered : Conic.projectiveToUnit projectivePoint = point :=
    Conic.projectiveToUnit_unitToProjective point twoNonzero
  have projectivePointNotOrigin :
      projectivePoint ≠ (⟨0, 0⟩ : Plane.Point K) := by
    intro projectivePointEqualsOrigin
    apply pointNotExcluded
    calc
      point = Conic.projectiveToUnit projectivePoint := recovered.symm
      _ = Conic.projectiveToUnit (⟨0, 0⟩ : Plane.Point K) := by
        rw [projectivePointEqualsOrigin]
      _ = Conic.unitCircleExcludedPoint := by
        unfold Conic.projectiveToUnit Conic.unitCircleExcludedPoint
        apply Plane.Point.ext <;> dsimp only <;> ring1
  rcases Conic.projectiveCirclePoint_exists projectivePoint
      projectivePointOnCircle projectivePointNotOrigin with
    ⟨parameter, squareNotNegativeOne, projectiveFormula⟩
  refine ⟨parameter, squareNotNegativeOne, ?_⟩
  calc
    point = Conic.projectiveToUnit projectivePoint := recovered.symm
    _ = Conic.projectiveToUnit (Conic.projectiveCirclePoint parameter) := by
      rw [projectiveFormula]
    _ = Conic.unitCirclePoint parameter :=
      Conic.projectiveToUnit_projectiveCirclePoint parameter squareNotNegativeOne

/-- Every non-excluded unit-circle point has exactly one admissible rational parameter. -/
theorem unitCirclePoint_existsUnique [Nontrivial K] [DecidableEq K]
    (point : Plane.Point K) (twoNonzero : (2 : K) ≠ 0)
    (pointOnCircle : Conic.unitCircle.Contains point)
    (pointNotExcluded : point ≠ Conic.unitCircleExcludedPoint) :
    ∃! parameter : K,
      parameter ^ 2 ≠ -1 ∧ point = Conic.unitCirclePoint parameter := by
  rcases unitCirclePoint_exists point twoNonzero pointOnCircle
      pointNotExcluded with
    ⟨parameter, squareNotNegativeOne, pointFormula⟩
  refine ⟨parameter, ⟨squareNotNegativeOne, pointFormula⟩, ?_⟩
  intro other otherFormula
  exact (unitCirclePoint_injective parameter other squareNotNegativeOne
    otherFormula.1 twoNonzero (pointFormula.symm.trans otherFormula.2)).symm
/-- Parametrize the unit circle away from its distinguished excluded point.

When two is nonzero, every other circle point arises from a parameter whose square is not minus one; each admissible
parameter also gives a circle point (Theorem 108). -/
theorem unit_circle [Nontrivial K] [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    (∀ parameter : K, parameter ^ 2 ≠ -1 →
      Conic.unitCircle.Contains (Conic.unitCirclePoint parameter)) ∧
    (∀ point : Plane.Point K,
      Conic.unitCircle.Contains point → point ≠ Conic.unitCircleExcludedPoint →
        ∃ parameter : K,
          parameter ^ 2 ≠ -1 ∧ point = Conic.unitCirclePoint parameter) := by
  exact ⟨unitCirclePoint_contains,
    fun point pointOnCircle pointNotExcluded =>
      unitCirclePoint_exists point twoNonzero pointOnCircle pointNotExcluded⟩
end

end Purelib.Curves.Plane.Conic

end

end

section
/-!
# Divine Proportions, Theorem 113: cyclic signed area

The source's unit-circle points are explicit finite coordinate pairs.  The
proof clears the product of their four certified denominators and computes
the shoelace sum.  No orientation quotient, square root, or completed circle
is introduced.
-/

@[expose] public section

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

variable {K : Type*} [ExplicitField K]

section

/-- The coordinate order used in Theorem 113: `[2*lambda/(1+lambda^2), (1-lambda^2)/(1+lambda^2)]`. -/
def orientedUnitCirclePoint (parameter : K) :
  Plane.Point K :=
  ⟨(2 * parameter) / (1 + parameter ^ 2),
    (1 - parameter ^ 2) / (1 + parameter ^ 2)⟩

/-- The displayed point really lies on the unit circle. -/
theorem orientedUnitCirclePoint_contains [Nontrivial K]
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    Conic.unitCircle.Contains (orientedUnitCirclePoint parameter) := by
  have originalOnCircle :=
    Curves.Plane.Conic.unitCirclePoint_contains parameter squareNotNegativeOne
  apply (Conic.unitCircle_contains_iff _).2
  have originalEquation :=
    (Conic.unitCircle_contains_iff (Conic.unitCirclePoint parameter)).1
      originalOnCircle
  change
    ((2 * parameter) / (1 + parameter ^ 2)) ^ 2 +
      ((1 - parameter ^ 2) / (1 + parameter ^ 2)) ^ 2 - 1 = 0
  calc
    ((2 * parameter) / (1 + parameter ^ 2)) ^ 2 +
          ((1 - parameter ^ 2) / (1 + parameter ^ 2)) ^ 2 - 1 =
        (Conic.unitCirclePoint parameter).x ^ 2 +
          (Conic.unitCirclePoint parameter).y ^ 2 - 1 := by
      unfold Conic.unitCirclePoint
      ring1
    _ = 0 := originalEquation

/-- The position determinant of two parametrized unit-circle points after clearing their two denominators. -/
theorem orientedUnitCircle_positionDeterminant_cleared
    (left right : K)
    (leftSquareNotNegativeOne : left ^ 2 ≠ -1)
    (rightSquareNotNegativeOne : right ^ 2 ≠ -1) :
    Determinant.positionDeterminant (orientedUnitCirclePoint left)
        (orientedUnitCirclePoint right) *
        ((1 + left ^ 2) * (1 + right ^ 2)) =
      (2 * left) * (1 - right ^ 2) -
        (2 * right) * (1 - left ^ 2) := by
  have leftDenominatorNonzero : 1 + left ^ 2 ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff left).2
      leftSquareNotNegativeOne
  have rightDenominatorNonzero : 1 + right ^ 2 ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff right).2
      rightSquareNotNegativeOne
  have leftXCancel :
      ((2 * left) / (1 + left ^ 2)) * (1 + left ^ 2) = 2 * left :=
    ExplicitField.div_mul_cancel _ leftDenominatorNonzero
  have leftYCancel :
      ((1 - left ^ 2) / (1 + left ^ 2)) * (1 + left ^ 2) =
        1 - left ^ 2 :=
    ExplicitField.div_mul_cancel _ leftDenominatorNonzero
  have rightXCancel :
      ((2 * right) / (1 + right ^ 2)) * (1 + right ^ 2) = 2 * right :=
    ExplicitField.div_mul_cancel _ rightDenominatorNonzero
  have rightYCancel :
      ((1 - right ^ 2) / (1 + right ^ 2)) * (1 + right ^ 2) =
        1 - right ^ 2 :=
    ExplicitField.div_mul_cancel _ rightDenominatorNonzero
  unfold Determinant.positionDeterminant orientedUnitCirclePoint
  dsimp only
  calc
    (((2 * left) / (1 + left ^ 2)) *
          ((1 - right ^ 2) / (1 + right ^ 2)) -
        ((2 * right) / (1 + right ^ 2)) *
          ((1 - left ^ 2) / (1 + left ^ 2))) *
          ((1 + left ^ 2) * (1 + right ^ 2)) =
      (((2 * left) / (1 + left ^ 2)) * (1 + left ^ 2)) *
          (((1 - right ^ 2) / (1 + right ^ 2)) *
            (1 + right ^ 2)) -
        (((2 * right) / (1 + right ^ 2)) * (1 + right ^ 2)) *
          (((1 - left ^ 2) / (1 + left ^ 2)) *
            (1 + left ^ 2)) := by ring1
    _ = (2 * left) * (1 - right ^ 2) -
        (2 * right) * (1 - left ^ 2) := by
      rw [leftXCancel, rightYCancel, rightXCancel, leftYCancel]
end

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end

end
