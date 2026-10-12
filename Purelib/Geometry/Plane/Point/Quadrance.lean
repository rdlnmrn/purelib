module
public import Purelib.Data.Nat.Order
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, Theorem 109: cyclic quadrilaterals

A quadrilateral is kept as four displayed points together with the source's
finite distinctness and noncollinearity certificates.  The cyclic predicate
stores an explicit conic, center, quadrance, circle presentation, and four
incidence proofs.

The printed four-by-four determinant is expanded by `determinantThree`; no
matrix determinant, permutation enumeration, or quotient of cyclic orderings
is introduced.  A translated determinant identity then gives both directions
of Theorem 109 constructively.
-/

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

variable {K : Type*} [ExplicitField K]
section

/-- The first coordinate in each row of the cyclicity determinant. -/
def circleRowNorm (point : Plane.Point K) : K :=
  point.x ^ 2 + point.y ^ 2
end

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 5: quadrance

Quadrance is a polynomial, so its basic geometry works uniformly over the
constructive rationals and finite fields.  The few exclusions below are
stated explicitly: midpoint and Triple-quad arguments require `2 ≠ 0`.
-/

namespace Purelib.Geometry.Plane.Point.Quadrance

variable {K : Type*} [ExplicitField K]

/-- The quadrance between two Cartesian points. -/
def quadrance (first second : Plane.Point K) : K :=
  (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2

/-- Quadrance is symmetric in its two Cartesian points. -/
theorem quadrance_symm (first second : Plane.Point K) :
    quadrance first second = quadrance second first := by
  unfold quadrance
  ring1

/-- The quadrance of a Cartesian point from itself is zero. -/
theorem quadrance_self (point : Plane.Point K) :
  quadrance point point = 0 := by
  unfold quadrance
  ring1
end Purelib.Geometry.Plane.Point.Quadrance

end

end

section
@[expose] public section

/-!
# Divine Proportions, §15.4 and Exercise 19.3: quadrolas

A quadrola is given by one finite Archimedes polynomial in the two focal
quadrances and its associated quadrance.  The apparent quartic terms cancel
to an explicit conic.  Its gradient tangent satisfies the equal-spread
reflection property by a denominator-cleared polynomial identity.
-/

namespace Purelib.Geometry.Plane.Point.Quadrance.Quadrola

section

variable {K : Type*} [ExplicitField K]

/-- The linear difference `Q(X,F₁)-Q(X,F₂)`. -/
def quadranceDifferenceLinear
    (firstFocus secondFocus : Plane.Point K) (point : Plane.Point K) : K :=
  2 * (secondFocus.x - firstFocus.x) * point.x +
    2 * (secondFocus.y - firstFocus.y) * point.y +
    firstFocus.x ^ 2 + firstFocus.y ^ 2 -
    secondFocus.x ^ 2 - secondFocus.y ^ 2

/-- Difference of the two focal quadrances is exactly linear in the point. -/
theorem quadrance_difference
    (firstFocus secondFocus point : Plane.Point K) :
    quadrance point firstFocus - quadrance point secondFocus =
      quadranceDifferenceLinear firstFocus secondFocus point := by
  unfold quadrance quadranceDifferenceLinear
  ring1
end

end Purelib.Geometry.Plane.Point.Quadrance.Quadrola

end
