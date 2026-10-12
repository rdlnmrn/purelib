module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Curves.Plane.Lemniscate.Basic
public import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Curves.Plane.Lemniscate

open Purelib.Geometry

open Purelib.Geometry.Plane

public section

namespace Purelib.Curves.Plane.Lemniscate.Tangent.Line

section Lemniscate

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The two first-order coefficients at a displayed point. -/
@[expose] def tangentA (parameter : K) (point :
  Geometry.Plane.Point K) : K :=
  point.x * (point.x ^ 2 + point.y ^ 2 - parameter)

/-- The y-direction first-order coefficient of the displayed lemniscate at the base point. -/
@[expose] def tangentB (parameter : K) (point :
  Geometry.Plane.Point K) : K :=
  point.y * (point.x ^ 2 + point.y ^ 2 + parameter)

/-- At least one displayed first-order tangent coefficient is nonzero. -/
@[expose] def IsNonSingularAt (parameter : K) (point :
  Geometry.Plane.Point K) : Prop :=
  tangentA parameter point ≠ 0 ∨
    tangentB parameter point ≠ 0

/-- The first-order tangent line translated back to its base point. -/
@[expose] def tangentLine (parameter : K) (point :
  Geometry.Plane.Point K)
    (nonSingular : IsNonSingularAt parameter point) : Geometry.Plane.Line K
      where
  a := tangentA parameter point
  b := tangentB parameter point
  c := -parameter * (point.x ^ 2 - point.y ^ 2)
  direction_nonzero := nonSingular

/-- The source's tangent line contains its incident base point. -/
theorem tangentLine_contains
    (parameter : K) (point : Geometry.Plane.Point K)
    (onLemniscate : Contains parameter point)
    (nonSingular : IsNonSingularAt parameter point) :
    (tangentLine parameter point nonSingular).Contains point :=
      by
  unfold Lemniscate.Contains Lemniscate.evaluate at onLemniscate
  unfold tangentLine
    tangentA tangentB
    Geometry.Plane.Line.Contains
  calc
    point.x * (point.x ^ 2 + point.y ^ 2 - parameter) * point.x +
          point.y * (point.x ^ 2 + point.y ^ 2 + parameter) * point.y +
          -parameter * (point.x ^ 2 - point.y ^ 2) =
        (point.x ^ 2 + point.y ^ 2) ^ 2 -
          2 * parameter * (point.x ^ 2 - point.y ^ 2) := by ring1
    _ = 0 := onLemniscate
end Lemniscate

end Purelib.Curves.Plane.Lemniscate.Tangent.Line

end

end
