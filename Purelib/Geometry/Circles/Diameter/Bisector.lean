module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Squares
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Geometry.Circles.Chord.Basic
import Purelib.Geometry.Circles.Conic.Basic
public import Purelib.Geometry.Circles.Diameter.Basic
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Line.Spread.Squares
public import Purelib.Geometry.Plane.Line.VertexBisector.Basic
import Purelib.Geometry.Plane.Line.VertexBisector.Existence
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra.Field

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Plane.Line.VertexBisector

open Purelib.Geometry.Plane.Point

@[expose] public section

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- A diameter supplies a nonzero square witness for the product of its line norm and the circle quadrance. -/
theorem diameter_norm_mul_quadrance_isNonzeroSquare [DecidableEq K]
    (circle : Conic K) (line : Plane.Line K) (center : Plane.Point K)
    (circleQuadrance : K) (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation :
      circle.IsCirclePresentation center circleQuadrance)
    (diameter : circle.IsDiameter line center) :
    Squares.IsNonzeroSquare (Basic.lineNorm line * circleQuadrance) := by
  have chord := Conic.exercise_16_1 circle line center circleQuadrance twoNonzero
    quadranceNonzero presentation diameter
  have lineNonNull := Conic.circle_chord circle line center circleQuadrance
    twoNonzero quadranceNonzero presentation chord
  rcases diameter with ⟨centerOnLine, point, pointIntersection⟩
  have pointRadiusFromPoint : Quadrance.quadrance point center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center point circleQuadrance
      presentation).1 pointIntersection.2
  have pointRadius : Quadrance.quadrance center point = circleQuadrance := by
    calc
      Quadrance.quadrance center point = Quadrance.quadrance point center :=
        Quadrance.quadrance_symm center point
      _ = circleQuadrance := pointRadiusFromPoint
  have directionDotZero :
      line.a * (point.x - center.x) +
        line.b * (point.y - center.y) = 0 := by
    have centerEquation := centerOnLine
    have pointEquation := pointIntersection.1
    unfold Purelib.Geometry.Plane.Line.Contains at centerEquation pointEquation
    calc
      line.a * (point.x - center.x) +
          line.b * (point.y - center.y) =
        (line.a * point.x + line.b * point.y + line.c) -
          (line.a * center.x + line.b * center.y + line.c) := by ring1
      _ = 0 := by rw [pointEquation, centerEquation]; ring1
  let crossValue :=
    line.a * (point.y - center.y) -
      line.b * (point.x - center.x)
  have squareEquation :
      Basic.lineNorm line * circleQuadrance = crossValue ^ 2 := by
    calc
      Basic.lineNorm line * circleQuadrance =
          Basic.lineNorm line * Quadrance.quadrance center point := by rw [pointRadius]
      _ = crossValue ^ 2 +
          (line.a * (point.x - center.x) +
            line.b * (point.y - center.y)) ^ 2 := by
        unfold Basic.lineNorm Quadrance.quadrance crossValue
        ring1
      _ = crossValue ^ 2 := by rw [directionDotZero]; ring1
  have productNonzero : Basic.lineNorm line * circleQuadrance ≠ 0 :=
    ExplicitField.mul_ne_zero lineNonNull quadranceNonzero
  have crossNonzero : crossValue ≠ 0 := by
    intro crossZero
    apply productNonzero
    calc
      Basic.lineNorm line * circleQuadrance = crossValue ^ 2 := squareEquation
      _ = 0 := by rw [crossZero]; ring1
  exact ⟨crossValue, crossNonzero, squareEquation⟩

/-- Exercise 16.2: two geometrically distinct diameters of a non-null circle form a square vertex, witnessed here by an
explicit vertex bisector. -/
theorem exercise_16_2 [DecidableEq K]
    (circle : Conic K) (firstLine secondLine : Plane.Line K)
    (center : Plane.Point K) (circleQuadrance : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation :
      circle.IsCirclePresentation center circleQuadrance)
    (firstDiameter : circle.IsDiameter firstLine center)
    (secondDiameter : circle.IsDiameter secondLine center)
    (notEquivalent : ¬ firstLine.Equivalent secondLine) :
    ∃ bisector : Plane.Line K,
      VertexBisector.Basic.IsVertexBisector firstLine secondLine bisector
        (Conic.circle_chord circle firstLine center circleQuadrance twoNonzero
          quadranceNonzero presentation
          (Conic.exercise_16_1 circle firstLine center circleQuadrance twoNonzero
            quadranceNonzero presentation firstDiameter))
        (Conic.circle_chord circle secondLine center circleQuadrance twoNonzero
          quadranceNonzero presentation
          (Conic.exercise_16_1 circle secondLine center circleQuadrance twoNonzero
            quadranceNonzero presentation secondDiameter))
        (by
          intro parallel
          exact notEquivalent
            (Relations.line_equivalent_of_parallel_and_common_point firstLine secondLine
              center parallel firstDiameter.1 secondDiameter.1)) := by
  let firstNonNull := Conic.circle_chord circle firstLine center circleQuadrance
    twoNonzero quadranceNonzero presentation
      (Conic.exercise_16_1 circle firstLine center circleQuadrance twoNonzero
        quadranceNonzero presentation firstDiameter)
  let secondNonNull := Conic.circle_chord circle secondLine center circleQuadrance
    twoNonzero quadranceNonzero presentation
      (Conic.exercise_16_1 circle secondLine center circleQuadrance twoNonzero
        quadranceNonzero presentation secondDiameter)
  have notParallel : ¬ firstLine.Parallel secondLine := by
    intro parallel
    exact notEquivalent
      (Relations.line_equivalent_of_parallel_and_common_point firstLine secondLine center
        parallel firstDiameter.1 secondDiameter.1)
  rcases diameter_norm_mul_quadrance_isNonzeroSquare circle firstLine center
      circleQuadrance twoNonzero quadranceNonzero presentation firstDiameter with
    ⟨firstRoot, firstRootNonzero, firstEquation⟩
  rcases diameter_norm_mul_quadrance_isNonzeroSquare circle secondLine center
      circleQuadrance twoNonzero quadranceNonzero presentation secondDiameter with
    ⟨secondRoot, secondRootNonzero, secondEquation⟩
  let root := (firstRoot * secondRoot) / circleQuadrance
  have rootNonzero : root ≠ 0 := by
    unfold root
    exact ExplicitField.div_ne_zero
      (ExplicitField.mul_ne_zero firstRootNonzero secondRootNonzero)
      quadranceNonzero
  have quadranceCancel :
      circleQuadrance * circleQuadrance⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel circleQuadrance quadranceNonzero
  have rootEquation :
      Line.Basic.lineNorm firstLine * Line.Basic.lineNorm secondLine = root ^ 2 := by
    unfold root
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      Line.Basic.lineNorm firstLine * Line.Basic.lineNorm secondLine =
          Line.Basic.lineNorm firstLine * Line.Basic.lineNorm secondLine *
            (circleQuadrance * circleQuadrance⁻¹) ^ 2 := by
        rw [quadranceCancel]
        ring1
      _ = (Line.Basic.lineNorm firstLine * circleQuadrance) *
          (Line.Basic.lineNorm secondLine * circleQuadrance) *
            (circleQuadrance⁻¹) ^ 2 := by ring1
      _ = firstRoot ^ 2 * secondRoot ^ 2 *
          (circleQuadrance⁻¹) ^ 2 := by
        rw [firstEquation, secondEquation]
      _ = (firstRoot * secondRoot * circleQuadrance⁻¹) ^ 2 := by ring1
  have normProductSquare :
      Squares.IsNonzeroSquare (Line.Basic.lineNorm firstLine * Line.Basic.lineNorm secondLine) :=
    ⟨root, rootNonzero, rootEquation⟩
  have spreadSquare :=
    (Squares.spread_isNonzeroSquare_iff_normProduct_isNonzeroSquare firstLine secondLine
      firstNonNull secondNonNull notParallel).2 normProductSquare
  exact
    (Existence.vertex_bisector_exists_iff_spread_isNonzeroSquare firstLine secondLine
      firstNonNull secondNonNull notParallel twoNonzero).2 spreadSquare
end

end Purelib.Curves.Plane.Conic

end
