module
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Curves.Plane.Cubic.Basic
-- Exposed Taylor coefficients retain these original natural numeral certificates.
public import Purelib.Data.Nat.Order
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

/-!
# Taylor coefficients of retained cubic curves

The five coefficient polynomials describe translation of a displayed cubic to
a supplied affine base point. Their linear and quadratic nonvanishing
conditions retain the retained curve and point as first- and second-order
nonsingularity witnesses.
-/

namespace Purelib.Curves.Plane.Cubic.Basic.CubicCurve

open Purelib.Algebra
open Purelib.Curves.Plane
open Purelib.Curves.Plane.Cubic.Basic
open Purelib.Geometry.Plane.Point
open Purelib.Geometry
open scoped Purelib.Data.Nat

variable {K : Type*} [Field.ExplicitField K]

/-- The `x²` coefficient in the Taylor curve at `A`.

The quadratic coefficient is evaluated from the retained cubic
coefficients and the supplied base point coordinates. -/
@[expose] public def taylorD (curve : Cubic.Basic.CubicCurve K) (point : Geometry.Plane.Point K) : K :=
  curve.d + 3 * curve.g * point.x + curve.h * point.y

/-- The `xy` coefficient in the Taylor curve at `A`.

The mixed quadratic coefficient uses both supplied base point
coordinates and the retained cubic coefficients. -/
@[expose] public def taylorE (curve : Cubic.Basic.CubicCurve K) (point : Geometry.Plane.Point K) : K :=
  curve.e + 2 * curve.h * point.x + 2 * curve.i * point.y

/-- The `y²` coefficient in the Taylor curve at `A`.

The quadratic coefficient in the second coordinate retains the
displayed cubic coefficients and base point. -/
@[expose] public def taylorF (curve : Cubic.Basic.CubicCurve K) (point : Geometry.Plane.Point K) : K :=
  curve.f + curve.i * point.x + 3 * curve.j * point.y

/-- The `x` coefficient in the Taylor curve at `A`.

This polynomial retains the cubic record and both base point coordinates as
the exact linear coefficient in the first coordinate. -/
@[expose] public def taylorA (curve : Cubic.Basic.CubicCurve K) (point : Geometry.Plane.Point K) : K :=
  curve.a + 2 * curve.d * point.x + curve.e * point.y +
    3 * curve.g * point.x ^ 2 + 2 * curve.h * point.x * point.y +
    curve.i * point.y ^ 2

/-- The `y` coefficient in the Taylor curve at `A`.

This polynomial retains the cubic record and both base point coordinates as
the exact linear coefficient in the second coordinate. -/
@[expose] public def taylorB (curve : Cubic.Basic.CubicCurve K) (point : Geometry.Plane.Point K) : K :=
  curve.b + curve.e * point.x + 2 * curve.f * point.y +
    curve.h * point.x ^ 2 + 2 * curve.i * point.x * point.y +
    3 * curve.j * point.y ^ 2

/-- Exact finite Taylor expansion after substituting `X+A`.

Translating the supplied local point by the base point yields the displayed
cubic and five Taylor coefficient terms, together with the original base point
value. -/
public theorem taylor_expansion
    (curve : Cubic.Basic.CubicCurve K) (point localPoint : Geometry.Plane.Point K) :
    curve.evaluate (Affine.translationPoint point.x point.y localPoint) =
      curve.g * localPoint.x ^ 3 +
        curve.h * localPoint.x ^ 2 * localPoint.y +
        curve.i * localPoint.x * localPoint.y ^ 2 +
        curve.j * localPoint.y ^ 3 +
        CubicCurve.taylorD curve point * localPoint.x ^ 2 +
        CubicCurve.taylorE curve point * localPoint.x * localPoint.y +
        CubicCurve.taylorF curve point * localPoint.y ^ 2 +
        CubicCurve.taylorA curve point * localPoint.x +
        CubicCurve.taylorB curve point * localPoint.y + curve.evaluate point := by
  unfold Cubic.Basic.CubicCurve.evaluate Affine.translationPoint CubicCurve.taylorD CubicCurve.taylorE
    CubicCurve.taylorF CubicCurve.taylorA CubicCurve.taylorB
  ring1

/-- At an incident base point the Taylor curve has zero constant term.

The supplied incidence witness makes the base point value zero in the same
finite Taylor expansion. -/
public theorem taylor_expansion_of_contains
    (curve : Cubic.Basic.CubicCurve K) (point localPoint : Geometry.Plane.Point K)
    (onCurve : curve.Contains point) :
    curve.evaluate (Affine.translationPoint point.x point.y localPoint) =
      curve.g * localPoint.x ^ 3 +
        curve.h * localPoint.x ^ 2 * localPoint.y +
        curve.i * localPoint.x * localPoint.y ^ 2 +
        curve.j * localPoint.y ^ 3 +
        CubicCurve.taylorD curve point * localPoint.x ^ 2 +
        CubicCurve.taylorE curve point * localPoint.x * localPoint.y +
        CubicCurve.taylorF curve point * localPoint.y ^ 2 +
        CubicCurve.taylorA curve point * localPoint.x +
        CubicCurve.taylorB curve point * localPoint.y := by
  rw [CubicCurve.taylor_expansion]
  unfold Cubic.Basic.CubicCurve.Contains at onCurve
  rw [onCurve]
  ring1

/-- First-order non-singularity is nonvanishing of the Taylor linear part.

The two alternatives refer to the exact retained linear Taylor coefficients at
the supplied point. -/
@[expose] public def IsFirstOrderNonSingularAt
    (curve : Cubic.Basic.CubicCurve K) (point : Geometry.Plane.Point K) : Prop :=
  CubicCurve.taylorA curve point ≠ 0 ∨ CubicCurve.taylorB curve point ≠ 0

/-- Second-order non-singularity is nonvanishing of the Taylor quadratic part.

The three alternatives refer to the exact retained quadratic Taylor
coefficients at the supplied point. -/
@[expose] public def IsSecondOrderNonSingularAt
    (curve : Cubic.Basic.CubicCurve K) (point : Geometry.Plane.Point K) : Prop :=
  CubicCurve.taylorD curve point ≠ 0 ∨ CubicCurve.taylorE curve point ≠ 0 ∨
    CubicCurve.taylorF curve point ≠ 0
end Purelib.Curves.Plane.Cubic.Basic.CubicCurve
