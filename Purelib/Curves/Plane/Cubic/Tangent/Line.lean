module
public import Purelib.Geometry.Plane.Line.Basic
-- The exposed tangent constant retains this original negation parent.
public import Purelib.Algebra.Group.Negation
import Purelib.Geometry.Plane.Point.Basic

import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Cubic.Basic
public import Purelib.Curves.Plane.Cubic.Taylor
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

/-!
# First-order tangent lines of displayed cubics

The retained Taylor linear part gives the line direction, and translating it
back by the supplied point gives the exact affine constant. Nonsingularity
retains the constructive direction witness in that same line record.
-/

namespace Purelib.Curves.Plane.Cubic.Basic.CubicCurve

open Purelib.Algebra
open Purelib.Curves.Plane
open Purelib.Curves.Plane.Cubic.Basic
open Purelib.Geometry
open Purelib.Geometry.Plane

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

variable {K : Type*} [Field.ExplicitField K]

/-- The first-order tangent line obtained by translating the Taylor linear part back to the base point.

The two Taylor linear coefficients are retained as the direction.
The constant is their displayed affine translation, and the supplied
nonsingularity disjunction certifies that this direction does not vanish.
-/
@[expose] public def tangentLine
    (curve : Cubic.Basic.CubicCurve K) (point : Geometry.Plane.Point K)
    (nonSingular : curve.IsFirstOrderNonSingularAt point) : Geometry.Plane.Line K where
  a := CubicCurve.taylorA curve point
  b := CubicCurve.taylorB curve point
  c := -CubicCurve.taylorA curve point * point.x - CubicCurve.taylorB curve point * point.y
  direction_nonzero := nonSingular

/-- The first-order tangent line contains its base point.

Substituting the retained base point into the translated constant
cancels the two Taylor linear terms without changing the tangent representative.
-/
public theorem tangentLine_contains
    (curve : Cubic.Basic.CubicCurve K) (point : Geometry.Plane.Point K)
    (nonSingular : curve.IsFirstOrderNonSingularAt point) :
    (CubicCurve.tangentLine curve point nonSingular).Contains point := by
  unfold CubicCurve.tangentLine Geometry.Plane.Line.Contains
  ring1
end Purelib.Curves.Plane.Cubic.Basic.CubicCurve
