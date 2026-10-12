module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Curves.Plane.Conic.Tangent
public import Purelib.Geometry.Conics.Quadrola.Basic
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra.Field

open Purelib.Curves.Plane (Conic)

open Purelib.Geometry

open Purelib.Geometry.Conics.Quadrola

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Point

section
@[expose] public section

/-!
# Divine Proportions, §15.4 and Exercise 19.3: quadrolas

A quadrola is given by one finite Archimedes polynomial in the two focal
quadrances and its associated quadrance.  The apparent quartic terms cancel
to an explicit conic.  Its gradient tangent satisfies the equal-spread
reflection property by a denominator-cleared polynomial identity.
-/

namespace Purelib.Geometry

namespace Conics.Quadrola.Tangent

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The first scalar coefficient in the quadrola gradient. -/
def firstWeight (firstQuadrance secondQuadrance
  associatedQuadrance : K) : K :=
  associatedQuadrance + secondQuadrance - firstQuadrance

/-- The second scalar coefficient in the quadrola gradient. -/
def secondWeight (firstQuadrance secondQuadrance
  associatedQuadrance : K) : K :=
  associatedQuadrance + firstQuadrance - secondQuadrance

/-- `x` coordinate of the gradient direction, after removing its common factor four. -/
def tangentNormalX (firstFocus secondFocus :
  Plane.Point K)
    (associatedQuadrance : K) (point : Plane.Point K) : K :=
  let firstQuadrance := Quadrance.quadrance point firstFocus
  let secondQuadrance := Quadrance.quadrance point secondFocus
  firstWeight firstQuadrance secondQuadrance associatedQuadrance *
      (point.x - firstFocus.x) +
    secondWeight firstQuadrance secondQuadrance associatedQuadrance *
      (point.x - secondFocus.x)

/-- `y` coordinate of the same gradient direction. -/
def tangentNormalY (firstFocus secondFocus :
  Plane.Point K)
    (associatedQuadrance : K) (point : Plane.Point K) : K :=
  let firstQuadrance := Quadrance.quadrance point firstFocus
  let secondQuadrance := Quadrance.quadrance point secondFocus
  firstWeight firstQuadrance secondQuadrance associatedQuadrance *
      (point.y - firstFocus.y) +
    secondWeight firstQuadrance secondQuadrance associatedQuadrance *
      (point.y - secondFocus.y)

/-- The gradient tangent representative used in Exercise 19.3. -/
def tangentLine [DecidableEq K]
    (firstFocus secondFocus : Plane.Point K) (associatedQuadrance : K)
    (point : Plane.Point K)
    (normalNonNull :
      tangentNormalX firstFocus secondFocus associatedQuadrance point ^ 2 +
        tangentNormalY firstFocus secondFocus associatedQuadrance point ^ 2 ≠
          0) : Plane.Line K where
  a := tangentNormalX firstFocus secondFocus associatedQuadrance point
  b := tangentNormalY firstFocus secondFocus associatedQuadrance point
  c := -(tangentNormalX firstFocus secondFocus associatedQuadrance point *
      point.x +
    tangentNormalY firstFocus secondFocus associatedQuadrance point * point.y)
  direction_nonzero := by
    by_cases firstZero :
        tangentNormalX firstFocus secondFocus associatedQuadrance point = 0
    · right
      intro secondZero
      apply normalNonNull
      rw [firstZero, secondZero]
      ring1
    · exact Or.inl firstZero

/-- The displayed quadrola gradient line passes through its defining point. -/
theorem tangentLine_contains [DecidableEq K]
    (firstFocus secondFocus : Plane.Point K) (associatedQuadrance : K)
    (point : Plane.Point K)
    (normalNonNull :
      tangentNormalX firstFocus secondFocus associatedQuadrance point ^ 2 +
        tangentNormalY firstFocus secondFocus associatedQuadrance point ^ 2 ≠
          0) :
    (tangentLine firstFocus secondFocus associatedQuadrance point
      normalNonNull).Contains point := by
  unfold tangentLine Plane.Line.Contains
  ring1

/-- The retained nonzero squared gradient norm makes the tangent line non-null. -/
theorem tangentLine_nonNull [DecidableEq K]
    (firstFocus secondFocus : Plane.Point K) (associatedQuadrance : K)
    (point : Plane.Point K)
    (normalNonNull :
      tangentNormalX firstFocus secondFocus associatedQuadrance point ^ 2 +
        tangentNormalY firstFocus secondFocus associatedQuadrance point ^ 2 ≠
          0) :
    ¬ (tangentLine firstFocus secondFocus associatedQuadrance point
      normalNonNull).IsNull := by
  unfold tangentLine Plane.Line.IsNull
  exact normalNonNull

/-- The explicit conic gradient is four times the finite quadrola normal. -/
theorem conic_gradient [DecidableEq K]
    (firstFocus secondFocus : Plane.Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (point : Plane.Point K) :
    let quadrolaConic := Quadrola.conic firstFocus secondFocus associatedQuadrance
      associatedNonzero eightNonzero
    quadrolaConic.a + 2 * quadrolaConic.d * point.x +
        quadrolaConic.e * point.y =
          4 * tangentNormalX firstFocus secondFocus associatedQuadrance point ∧
      quadrolaConic.b + quadrolaConic.e * point.x +
        2 * quadrolaConic.f * point.y =
          4 * tangentNormalY firstFocus secondFocus associatedQuadrance point
            := by
  dsimp only
  unfold Quadrola.conic Quadrola.conicD Quadrola.conicE Quadrola.conicF Quadrola.conicA Quadrola.conicB
    tangentNormalX
    tangentNormalY firstWeight
      secondWeight Quadrance.quadrance
  exact ⟨by ring1, by ring1⟩

/-- The gradient representative is the tangent line of the explicit conic, up to the common factor four. -/
theorem tangentLine_formula [DecidableEq K]
    (firstFocus secondFocus : Plane.Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (point : Plane.Point K)
    (onQuadrola : Quadrola.Contains firstFocus secondFocus associatedQuadrance point)
    (normalNonNull :
      tangentNormalX firstFocus secondFocus associatedQuadrance point ^ 2 +
        tangentNormalY firstFocus secondFocus associatedQuadrance point ^ 2 ≠
          0) :
    ∃ nonSingular :
        (Quadrola.conic firstFocus secondFocus associatedQuadrance associatedNonzero
          eightNonzero).IsNonSingularAt point,
      (Conic.tangentLine
        (Quadrola.conic firstFocus secondFocus associatedQuadrance associatedNonzero
          eightNonzero) point nonSingular).Equivalent
        (tangentLine firstFocus secondFocus associatedQuadrance point
          normalNonNull) := by
  let quadrolaConic := Quadrola.conic firstFocus secondFocus associatedQuadrance
    associatedNonzero eightNonzero
  let gradientLine := tangentLine firstFocus secondFocus associatedQuadrance
    point normalNonNull
  have gradient := conic_gradient firstFocus secondFocus associatedQuadrance
    associatedNonzero eightNonzero point
  have fourNonzero := Purelib.Algebra.Field.Characteristic.Nonzero.four_ne_zero_of_eight_ne_zero eightNonzero
  have nonSingular : quadrolaConic.IsNonSingularAt point := by
    unfold Conic.IsNonSingularAt
    rw [gradient.1, gradient.2]
    rcases gradientLine.direction_nonzero with firstNonzero | secondNonzero
    · left
      exact Algebra.Field.ExplicitField.mul_ne_zero fourNonzero firstNonzero
    · right
      exact Algebra.Field.ExplicitField.mul_ne_zero fourNonzero secondNonzero
  have onConic : quadrolaConic.Contains point := by
    unfold Conic.Contains
    rw [Quadrola.conic_evaluate]
    exact onQuadrola
  let actualTangent := Conic.tangentLine quadrolaConic point nonSingular
  have actualContains : actualTangent.Contains point :=
    Conic.tangentLine_contains quadrolaConic point onConic nonSingular
  have firstCoefficient : actualTangent.a = 4 * gradientLine.a := by
    unfold actualTangent Conic.tangentLine gradientLine tangentLine
    exact gradient.1
  have secondCoefficient : actualTangent.b = 4 * gradientLine.b := by
    unfold actualTangent Conic.tangentLine gradientLine tangentLine
    exact gradient.2
  have constantCoefficient : actualTangent.c = 4 * gradientLine.c := by
    unfold Plane.Line.Contains at actualContains
    calc
      actualTangent.c =
          -(actualTangent.a * point.x + actualTangent.b * point.y) := by
        calc
          actualTangent.c =
              actualTangent.c -
                (actualTangent.a * point.x + actualTangent.b * point.y +
                  actualTangent.c) := by rw [actualContains]; ring1
          _ = -(actualTangent.a * point.x + actualTangent.b * point.y) := by
            ring1
      _ = -(4 * gradientLine.a * point.x +
          4 * gradientLine.b * point.y) := by
        rw [firstCoefficient, secondCoefficient]
      _ = 4 * gradientLine.c := by
        unfold gradientLine tangentLine
        ring1
  refine ⟨nonSingular, ?_⟩
  unfold Plane.Line.Equivalent
  rw [firstCoefficient, secondCoefficient, constantCoefficient]
  exact ⟨by ring1, by ring1, by ring1⟩
end Conics.Quadrola.Tangent

end Purelib.Geometry

end
