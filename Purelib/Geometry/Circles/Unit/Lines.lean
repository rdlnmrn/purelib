module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Circles.Unit.Basic
public import Purelib.Geometry.Circles.Unit.Parametrization
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Point.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Curves.Plane (Conic)

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

section
public section

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

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

/-- The chord through `[-1,0]` and the point with parameter `lambda`. -/
@[expose] def unitCircleParameterLine [Nontrivial K] (parameter : K) :
  Plane.Line K where
  a := parameter
  b := -1
  c := parameter
  direction_nonzero := Or.inr ((by intro negZero; have restored := congrArg (fun value : K => -value) negZero; rewrite
    [neg_neg, SubNegZeroMonoid.neg_zero] at restored; exact one_ne_zero restored))

/-- The parameter chord contains the excluded unit-circle point. -/
theorem unitCircleParameterLine_contains_excluded [Nontrivial K]
    (parameter : K) :
    (unitCircleParameterLine parameter).Contains
      Conic.unitCircleExcludedPoint := by
  unfold unitCircleParameterLine Conic.unitCircleExcludedPoint Plane.Line.Contains
  dsimp only
  ring1

/-- The parameter chord contains its parametrized unit-circle point. -/
theorem unitCircleParameterLine_contains_point [Nontrivial K]
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    (unitCircleParameterLine parameter).Contains
      (Conic.unitCirclePoint parameter) := by
  have parameterEquation := Conic.unitCirclePoint_parameter_equation parameter
    squareNotNegativeOne
  unfold unitCircleParameterLine Plane.Line.Contains
  dsimp only
  rw [parameterEquation]
  ring1

/-- The explicit parameter chord is the line through `[-1,0]` and the parametrized unit-circle point, up to
quotient-free line equivalence. -/
theorem unitCircleParameterLine_equivalent_lineThrough [Nontrivial K]
    [DecidableEq K]
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1)
    (twoNonzero : (2 : K) ≠ 0) :
    (Incidence.lineThrough Conic.unitCircleExcludedPoint (Conic.unitCirclePoint parameter)
      (Ne.symm (Conic.unitCirclePoint_ne_excluded parameter
        squareNotNegativeOne twoNonzero))).Equivalent
      (unitCircleParameterLine parameter) := by
  apply Incidence.lineThrough_unique Conic.unitCircleExcludedPoint
    (Conic.unitCirclePoint parameter)
    (Ne.symm (Conic.unitCirclePoint_ne_excluded parameter
      squareNotNegativeOne twoNonzero))
  · exact unitCircleParameterLine_contains_excluded parameter
  · exact unitCircleParameterLine_contains_point parameter
      squareNotNegativeOne

/-- The point `i*lambda` lies on the corresponding parameter chord. -/
theorem unitCircleParameterLine_contains_imaginary [Nontrivial K]
    (parameter : K) :
    (unitCircleParameterLine parameter).Contains
      (Conic.imaginaryParameterPoint parameter) := by
  unfold unitCircleParameterLine Conic.imaginaryParameterPoint Plane.Line.Contains
  dsimp only
  ring1

/-- The imaginary axis and any parameter chord are nonparallel. -/
theorem imaginaryAxis_parameterLine_nonparallel [Nontrivial K]
    (parameter : K) :
    ¬ Conic.imaginaryAxis.Parallel (unitCircleParameterLine parameter) := by
  unfold Conic.imaginaryAxis unitCircleParameterLine Plane.Line.Parallel
  dsimp only
  intro negativeOneZero
  apply (show (- (1 : K)) ≠ 0 from (by
    intro negZero
    have restored := congrArg (fun value : K => -value) negZero
    rewrite [neg_neg, SubNegZeroMonoid.neg_zero] at restored
    exact (one_ne_zero : (1 : K) ≠ 0) restored))
  calc
    (-1 : K) = 1 * -1 - parameter * 0 := by ring1
    _ = 0 := negativeOneZero

/-- The book's point `i*lambda` is the unique intersection of the imaginary axis and the chord through `-1` and the
parametrized unit-circle point. -/
theorem imaginaryParameterPoint_is_intersection [Nontrivial K]
    (parameter : K) :
    Conic.imaginaryParameterPoint parameter =
      Intersection.lineIntersection Conic.imaginaryAxis (unitCircleParameterLine
        parameter)
        (imaginaryAxis_parameterLine_nonparallel parameter) := by
  exact Intersection.lineIntersection_unique Conic.imaginaryAxis
    (unitCircleParameterLine parameter)
    (imaginaryAxis_parameterLine_nonparallel parameter)
    (Conic.imaginaryParameterPoint parameter)
    (Conic.imaginaryAxis_contains_parameter parameter)
    (unitCircleParameterLine_contains_imaginary parameter)
end

end Purelib.Curves.Plane.Conic

end

end
