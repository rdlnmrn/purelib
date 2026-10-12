module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Curves.Plane.Conic.Tangent
import Purelib.Curves.Plane.Lemniscate.Basic
public import Purelib.Curves.Plane.Lemniscate.Tangent.Line
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Curves.Plane

open Purelib.Curves.Plane.Lemniscate

open Purelib.Curves.Plane.Lemniscate.Tangent.Line

open Purelib.Geometry

public section

namespace Purelib.Curves.Plane.Lemniscate.Tangent.Conic

section Lemniscate

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The three second-order Taylor coefficients. -/
@[expose] def tangentD (parameter : K) (point :
  Geometry.Plane.Point K) : K :=
  3 * point.x ^ 2 + point.y ^ 2 - parameter

/-- The mixed second-order Taylor coefficient, four times the product of the original point coordinates. -/
@[expose] def tangentE (point : Geometry.Plane.Point
  K) : K :=
  4 * point.x * point.y

/-- The vertical quadratic Taylor coefficient of the lemniscate at the original point. -/
@[expose] def tangentF (parameter : K) (point :
  Geometry.Plane.Point K) : K :=
  point.x ^ 2 + 3 * point.y ^ 2 + parameter

/-- At least one of the three displayed quadratic Taylor coefficients is nonzero. -/
@[expose] def IsSecondOrderNonSingularAt (parameter : K)
  (point : Geometry.Plane.Point K) : Prop :=
  tangentD parameter point ≠ 0 ∨
    tangentE point ≠ 0 ∨
    tangentF parameter point ≠ 0

/-- The second-order tangent conic after translating back to the base point. -/
@[expose] def tangentConic (parameter : K) (point :
  Geometry.Plane.Point K)
    (secondOrderNonSingular : IsSecondOrderNonSingularAt parameter
      point) :
    Conic K where
  d := tangentD parameter point
  e := tangentE point
  f := tangentF parameter point
  a := -4 * point.x * (point.x ^ 2 + point.y ^ 2)
  b := -4 * point.y * (point.x ^ 2 + point.y ^ 2)
  c := 3 * parameter * (point.x ^ 2 - point.y ^ 2)
  quadratic_nonzero := secondOrderNonSingular

/-- The second-order tangent conic contains its base point. -/
theorem tangentConic_contains
    (parameter : K) (point : Geometry.Plane.Point K)
    (onLemniscate : Contains parameter point)
    (secondOrderNonSingular : IsSecondOrderNonSingularAt parameter
      point) :
    (tangentConic parameter point
      secondOrderNonSingular).Contains point := by
  unfold Lemniscate.Contains Lemniscate.evaluate at onLemniscate
  unfold tangentConic tangentD
    tangentE tangentF
    Conic.Contains Conic.evaluate
  calc
    (3 * point.x ^ 2 + point.y ^ 2 - parameter) * point.x ^ 2 +
          (4 * point.x * point.y) * point.x * point.y +
          (point.x ^ 2 + 3 * point.y ^ 2 + parameter) * point.y ^ 2 +
          (-4 * point.x * (point.x ^ 2 + point.y ^ 2)) * point.x +
          (-4 * point.y * (point.x ^ 2 + point.y ^ 2)) * point.y +
          3 * parameter * (point.x ^ 2 - point.y ^ 2) =
        -((point.x ^ 2 + point.y ^ 2) ^ 2 -
          2 * parameter * (point.x ^ 2 - point.y ^ 2)) := by ring1
    _ = 0 := by rw [onLemniscate]; ring1

/-- The first-order tangent to the lemniscate is also the tangent to its second-order tangent conic at the same point.
-/
theorem tangentLine_is_tangent_to_tangentConic
    (parameter : K) (point : Geometry.Plane.Point K)
    (onLemniscate : Contains parameter point)
    (twoNonzero : (2 : K) ≠ 0)
    (nonSingular : Line.IsNonSingularAt parameter point)
    (secondOrderNonSingular : IsSecondOrderNonSingularAt parameter
      point) :
    ∃ conicNonSingular :
        (tangentConic parameter point
          secondOrderNonSingular).IsNonSingularAt
          point,
      (Line.tangentLine parameter point nonSingular).Equivalent
        (Conic.tangentLine
          (tangentConic parameter point secondOrderNonSingular)
          point conicNonSingular) := by
  let conic := tangentConic parameter point secondOrderNonSingular
  have firstGradient :
      conic.a + 2 * conic.d * point.x + conic.e * point.y =
        2 * Line.tangentA parameter point := by
    unfold conic tangentConic
      tangentD
      tangentE Line.tangentA
    ring1
  have secondGradient :
      conic.b + conic.e * point.x + 2 * conic.f * point.y =
        2 * Line.tangentB parameter point := by
    unfold conic tangentConic
      tangentE
      tangentF Line.tangentB
    ring1
  have conicNonSingular : conic.IsNonSingularAt point := by
    unfold Conic.IsNonSingularAt
    rw [firstGradient, secondGradient]
    rcases nonSingular with firstNonzero | secondNonzero
    · left
      exact Algebra.Field.ExplicitField.mul_ne_zero twoNonzero firstNonzero
    · right
      exact Algebra.Field.ExplicitField.mul_ne_zero twoNonzero secondNonzero
  refine ⟨conicNonSingular, ?_⟩
  have constantCoefficient :
      conic.a * point.x + conic.b * point.y + 2 * conic.c =
        2 * (-parameter * (point.x ^ 2 - point.y ^ 2)) := by
    unfold conic tangentConic
    unfold Lemniscate.Contains Lemniscate.evaluate at onLemniscate
    calc
      (-4 * point.x * (point.x ^ 2 + point.y ^ 2)) * point.x +
            (-4 * point.y * (point.x ^ 2 + point.y ^ 2)) * point.y +
            2 * (3 * parameter * (point.x ^ 2 - point.y ^ 2)) =
          2 * (-parameter * (point.x ^ 2 - point.y ^ 2)) -
            4 * ((point.x ^ 2 + point.y ^ 2) ^ 2 -
              2 * parameter * (point.x ^ 2 - point.y ^ 2)) := by ring1
      _ = 2 * (-parameter * (point.x ^ 2 - point.y ^ 2)) := by
        rw [onLemniscate]
        ring1
  unfold Geometry.Plane.Line.Equivalent
  dsimp only [Conic.tangentLine, Line.tangentLine]
  rw [firstGradient, secondGradient, constantCoefficient]
  exact ⟨by ring1, by ring1, by ring1⟩
end Lemniscate

end Purelib.Curves.Plane.Lemniscate.Tangent.Conic

end

end
