module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Curves.Plane.Conic.Tangent
public import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Construction
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

section
@[expose] public section

/-!
# Divine Proportions, Chapter 19: tangent lines and conics

Translations, Taylor conics, and tangent lines are retained as explicit
finite coefficient records.  A non-singular point carries the disjunction
that one of the two displayed linear coefficients is nonzero, so every line
construction remains executable and choice-free.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- Theorem 120 (Tangent to a circle): at every point of a circle with nonzero quadrance, the explicit tangent is
non-singular, non-null, and is the altitude from the point to the line joining it to the center. -/
theorem tangent_to_circle
    [Nontrivial K] [DecidableEq K]
    (conic : Conic K) (center point : Plane.Point K) (circleQuadrance : K)
    (presentation :
      conic.IsCirclePresentation center circleQuadrance)
    (onCircle : conic.Contains point)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0) :
    ∃ pointCenterDistinct : point ≠ center,
      ∃ nonSingular : conic.IsNonSingularAt point,
        let tangent := Conic.tangentLine conic point nonSingular
        let centerLine := Incidence.lineThrough point center pointCenterDistinct
        tangent.Contains point ∧
          ¬ tangent.IsNull ∧
          tangent.Perpendicular centerLine ∧
          tangent.Equivalent (Construction.altitudeThrough point centerLine) := by
  have pointQuadrance : Quadrance.quadrance point center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq conic center point circleQuadrance
      presentation).1 onCircle
  have pointCenterDistinct : point ≠ center := by
    intro equalPoints
    apply quadranceNonzero
    calc
      circleQuadrance = Quadrance.quadrance point center := pointQuadrance.symm
      _ = Quadrance.quadrance center center := by rw [equalPoints]
      _ = 0 := Quadrance.quadrance_self center
  have eZero := presentation.1
  have dEqualsF := presentation.2.1
  have dNonzero := presentation.2.2.1
  have aFormula := presentation.2.2.2.1
  have bFormula := presentation.2.2.2.2.1
  let scale := 2 * conic.d
  have scaleNonzero : scale ≠ 0 :=
    ExplicitField.mul_ne_zero twoNonzero dNonzero
  have gradientX :
      conic.a + 2 * conic.d * point.x + conic.e * point.y =
        scale * (point.x - center.x) := by
    rw [eZero, aFormula]
    unfold scale
    ring1
  have gradientY :
      conic.b + conic.e * point.x + 2 * conic.f * point.y =
        scale * (point.y - center.y) := by
    rw [eZero, ← dEqualsF, bFormula]
    unfold scale
    ring1
  have nonSingular : conic.IsNonSingularAt point := by
    unfold Conic.IsNonSingularAt
    by_cases firstNonzero :
        conic.a + 2 * conic.d * point.x + conic.e * point.y ≠ 0
    · exact Or.inl firstNonzero
    · right
      intro secondZero
      have xDifferenceZero : point.x - center.x = 0 :=
        ExplicitField.eq_zero_of_mul_eq_zero_left scaleNonzero (by
          rw [← gradientX]
          by_cases firstZero :
              conic.a + 2 * conic.d * point.x +
                conic.e * point.y = 0
          · exact firstZero
          · exact False.elim (firstNonzero firstZero))
      have yDifferenceZero : point.y - center.y = 0 :=
        ExplicitField.eq_zero_of_mul_eq_zero_left scaleNonzero (by
          rw [← gradientY]
          exact secondZero)
      apply pointCenterDistinct
      apply Plane.Point.ext
      · calc
          point.x = (point.x - center.x) + center.x := by ring1
          _ = center.x := by rw [xDifferenceZero]; ring1
      · calc
          point.y = (point.y - center.y) + center.y := by ring1
          _ = center.y := by rw [yDifferenceZero]; ring1
  refine ⟨pointCenterDistinct, nonSingular, ?_⟩
  dsimp only
  let tangent := Conic.tangentLine conic point nonSingular
  let centerLine := Incidence.lineThrough point center pointCenterDistinct
  let altitude := Construction.altitudeThrough point centerLine
  have tangentContains : tangent.Contains point :=
    Conic.tangentLine_contains conic point onCircle nonSingular
  have tangentA : tangent.a = scale * altitude.a := by
    change conic.a + 2 * conic.d * point.x + conic.e * point.y =
      scale * (-(center.x - point.x))
    rw [gradientX]
    ring1
  have tangentB : tangent.b = scale * altitude.b := by
    change conic.b + conic.e * point.x + 2 * conic.f * point.y =
      scale * (point.y - center.y)
    exact gradientY
  have tangentConstantFromIncidence :
      tangent.c = -tangent.a * point.x - tangent.b * point.y := by
    unfold Plane.Line.Contains at tangentContains
    calc
      tangent.c =
          (tangent.a * point.x + tangent.b * point.y + tangent.c) -
            tangent.a * point.x - tangent.b * point.y := by ring1
      _ = -tangent.a * point.x - tangent.b * point.y := by
        rw [tangentContains]
        ring1
  have tangentC : tangent.c = scale * altitude.c := by
    rw [tangentConstantFromIncidence, tangentA, tangentB]
    change
      -(scale * (-(center.x - point.x))) * point.x -
          scale * (point.y - center.y) * point.y =
        scale * ((center.x - point.x) * point.x -
          (point.y - center.y) * point.y)
    ring1
  have tangentNonNull : ¬ tangent.IsNull := by
    intro tangentNull
    have scaledQuadranceZero :
        (scale * scale) * Quadrance.quadrance point center = 0 := by
      calc
        (scale * scale) * Quadrance.quadrance point center =
            tangent.a ^ 2 + tangent.b ^ 2 := by
          rw [tangentA, tangentB]
          unfold altitude centerLine Construction.altitudeThrough Incidence.lineThrough Quadrance.quadrance
          ring1
        _ = 0 := tangentNull
    have scaledQuadranceNonzero :
        (scale * scale) * Quadrance.quadrance point center ≠ 0 :=
      ExplicitField.mul_ne_zero
        (ExplicitField.mul_ne_zero scaleNonzero scaleNonzero)
        (by rw [pointQuadrance]; exact quadranceNonzero)
    exact scaledQuadranceNonzero scaledQuadranceZero
  have tangentPerpendicular : tangent.Perpendicular centerLine := by
    unfold Plane.Line.Perpendicular
    rw [tangentA, tangentB]
    unfold altitude centerLine Construction.altitudeThrough Incidence.lineThrough
    ring1
  have tangentEquivalentAltitude : tangent.Equivalent altitude := by
    unfold Plane.Line.Equivalent
    rw [tangentA, tangentB, tangentC]
    exact ⟨by ring1, by ring1, by ring1⟩
  exact ⟨tangentContains, tangentNonNull, tangentPerpendicular,
    tangentEquivalentAltitude⟩
end

end Purelib.Curves.Plane.Conic

end
