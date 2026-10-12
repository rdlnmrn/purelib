module
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Curves.Plane.Conic.Tangent
import Purelib.Curves.Plane.Conic.Translation
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic

import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Cubic.Basic
public import Purelib.Curves.Plane.Cubic.Tangent.Line
import Purelib.Curves.Plane.Cubic.Taylor
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Plane

open Purelib.Curves.Plane.Cubic.Basic

open Purelib.Geometry

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Point

/-!
# Divine Proportions, §19.3: higher-order curves and tangents

A cubic remains a finite ten-coefficient record.  Its Taylor coefficients are
explicit polynomials in the displayed base point.  First- and second-order
non-singularity are constructive disjunctions, used directly to build the
tangent line and tangent conic.
-/

@[expose] public section

namespace Purelib.Curves.Plane.Cubic.Basic.CubicCurve

open Purelib.Algebra

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The degree-at-most-two truncation of the Taylor curve at the origin. -/
def standardTangentConic
    (curve : Cubic.Basic.CubicCurve K) (point : Plane.Point K)
    (secondOrderNonSingular : curve.IsSecondOrderNonSingularAt point) :
    Conic K where
  d := CubicCurve.taylorD curve point
  e := CubicCurve.taylorE curve point
  f := CubicCurve.taylorF curve point
  a := CubicCurve.taylorA curve point
  b := CubicCurve.taylorB curve point
  c := 0
  quadratic_nonzero := secondOrderNonSingular

/-- The second-order tangent conic translated back to the base point. -/
def tangentConic
    (curve : Cubic.Basic.CubicCurve K) (point : Plane.Point K)
    (secondOrderNonSingular : curve.IsSecondOrderNonSingularAt point) :
    Conic K :=
  Conic.translateConic
    (standardTangentConic curve point secondOrderNonSingular) point

/-- The second-order tangent conic contains its base point. -/
theorem tangentConic_contains
    (curve : Cubic.Basic.CubicCurve K) (point : Plane.Point K)
    (secondOrderNonSingular : curve.IsSecondOrderNonSingularAt point) :
    (tangentConic curve point secondOrderNonSingular).Contains point := by
  unfold Conic.Contains CubicCurve.tangentConic
  calc
    (Conic.translateConic
        (standardTangentConic curve point secondOrderNonSingular) point).evaluate
          point =
      (standardTangentConic curve point secondOrderNonSingular).evaluate
        ⟨0, 0⟩ := by
      have translated := Conic.translateConic_evaluate
        (standardTangentConic curve point secondOrderNonSingular) point
        ⟨0, 0⟩
      simpa only [Affine.translationPoint, zero_add] using translated
    _ = 0 := by
      unfold standardTangentConic Conic.evaluate
      ring1

/-- First-order non-singularity transfers from the cubic to its tangent conic at the same point. -/
theorem tangentConic_nonSingularAt
    (curve : Cubic.Basic.CubicCurve K) (point : Plane.Point K)
    (firstOrderNonSingular : curve.IsFirstOrderNonSingularAt point)
    (secondOrderNonSingular : curve.IsSecondOrderNonSingularAt point) :
    (tangentConic curve point secondOrderNonSingular).IsNonSingularAt point
      := by
  unfold Conic.IsNonSingularAt CubicCurve.tangentConic Conic.translateConic
    standardTangentConic
  dsimp only
  rcases firstOrderNonSingular with firstNonzero | secondNonzero
  · left
    intro expandedZero
    apply firstNonzero
    calc
      CubicCurve.taylorA curve point =
          CubicCurve.taylorA curve point - 2 * CubicCurve.taylorD curve point * point.x -
            CubicCurve.taylorE curve point * point.y +
            2 * CubicCurve.taylorD curve point * point.x +
            CubicCurve.taylorE curve point * point.y := by
        ring1
      _ = 0 := expandedZero
  · right
    intro expandedZero
    apply secondNonzero
    calc
      CubicCurve.taylorB curve point =
          CubicCurve.taylorB curve point - 2 * CubicCurve.taylorF curve point * point.y -
            CubicCurve.taylorE curve point * point.x +
            CubicCurve.taylorE curve point * point.x +
            2 * CubicCurve.taylorF curve point * point.y := by
        ring1
      _ = 0 := expandedZero

/-- The source's compatibility claim: the first-order tangent to the cubic is also the tangent to its second-order
tangent conic at the base point. -/
theorem tangentLine_is_tangent_to_tangentConic
    (curve : Cubic.Basic.CubicCurve K) (point : Plane.Point K)
    (firstOrderNonSingular : curve.IsFirstOrderNonSingularAt point)
    (secondOrderNonSingular : curve.IsSecondOrderNonSingularAt point) :
    (Purelib.Curves.Plane.Cubic.Basic.CubicCurve.tangentLine curve point firstOrderNonSingular).Equivalent
      (Purelib.Curves.Plane.Conic.tangentLine (tangentConic
        curve point secondOrderNonSingular)
        point (tangentConic_nonSingularAt curve point firstOrderNonSingular
          secondOrderNonSingular)) := by
  unfold CubicCurve.tangentLine Conic.tangentLine CubicCurve.tangentConic Conic.translateConic
    standardTangentConic Plane.Line.Equivalent
  exact ⟨by ring1, by ring1, by ring1⟩

end Purelib.Curves.Plane.Cubic.Basic.CubicCurve

end
