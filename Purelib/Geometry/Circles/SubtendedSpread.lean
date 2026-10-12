module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Geometry.Circles.Chord.Basic
import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Line.Null
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Spread.Triple
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Circumcenter.ExtendedSpread
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Geometry.Plane (Line)

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Trigonometry.Spread

open Purelib.Geometry.Trigonometry.Spread.Triple

section
@[expose] public section

/-!
# Divine Proportions, §16.2: subtended spreads

The Extended spread law supplies the fixed cleared ratio on a circle.  A
second finite determinant identity for the two radius vectors converts that
ratio into the source's `S₂(s) = 4s(1-s)` formula.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- Theorem 105 (Subtended spread): the spread at the third circle point is fixed by the chord, and the spread at the
center is its second spread polynomial `4s(1-s)`. -/
theorem subtended_spread [Nontrivial K] [DecidableEq K]
    (circle : Conic K) (center first second third : Plane.Point K)
    (circleQuadrance : K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation :
      circle.IsCirclePresentation center circleQuadrance)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second)
    (thirdOnCircle : circle.Contains third) :
    let firstCenterDistinct : first ≠ center := by
      have radius : Quadrance.quadrance first center = circleQuadrance :=
        (Conic.contains_iff_quadrance_eq circle center first circleQuadrance
          presentation).1 firstOnCircle
      intro pointEqualsCenter
      apply quadranceNonzero
      calc
        circleQuadrance = Quadrance.quadrance first center := radius.symm
        _ = Quadrance.quadrance center center := by rw [pointEqualsCenter]
        _ = 0 := Quadrance.quadrance_self center
    let secondCenterDistinct : second ≠ center := by
      have radius : Quadrance.quadrance second center = circleQuadrance :=
        (Conic.contains_iff_quadrance_eq circle center second circleQuadrance
          presentation).1 secondOnCircle
      intro pointEqualsCenter
      apply quadranceNonzero
      calc
        circleQuadrance = Quadrance.quadrance second center := radius.symm
        _ = Quadrance.quadrance center center := by rw [pointEqualsCenter]
        _ = 0 := Quadrance.quadrance_self center
    let firstThirdNonNull := Conic.lineThrough_circle_points_nonNull circle center
      circleQuadrance twoNonzero quadranceNonzero presentation first third
      firstThirdDistinct firstOnCircle thirdOnCircle
    let secondThirdNonNull := Conic.lineThrough_circle_points_nonNull circle center
      circleQuadrance twoNonzero quadranceNonzero presentation second third
      secondThirdDistinct secondOnCircle thirdOnCircle
    let firstCenterNonNull :
        ¬ (Incidence.lineThrough first center firstCenterDistinct).IsNull := by
      intro lineNull
      apply quadranceNonzero
      have radiusZero :=
        (Quadrance.null_line_iff_quadrance_zero first center
          firstCenterDistinct).1 lineNull
      calc
        circleQuadrance = Quadrance.quadrance first center :=
          ((Conic.contains_iff_quadrance_eq circle center first circleQuadrance
            presentation).1 firstOnCircle).symm
        _ = 0 := radiusZero
    let secondCenterNonNull :
        ¬ (Incidence.lineThrough second center secondCenterDistinct).IsNull := by
      intro lineNull
      apply quadranceNonzero
      have radiusZero :=
        (Quadrance.null_line_iff_quadrance_zero second center
          secondCenterDistinct).1 lineNull
      calc
        circleQuadrance = Quadrance.quadrance second center :=
          ((Conic.contains_iff_quadrance_eq circle center second circleQuadrance
            presentation).1 secondOnCircle).symm
        _ = 0 := radiusZero
    let firstThirdReversedNonNull :
        ¬ (Incidence.lineThrough third first firstThirdDistinct.symm).IsNull := by
      exact Line.Null.reversedLine_nonNull
        first third firstThirdDistinct firstThirdNonNull
    let secondThirdReversedNonNull :
        ¬ (Incidence.lineThrough third second secondThirdDistinct.symm).IsNull := by
      exact Line.Null.reversedLine_nonNull
        second third secondThirdDistinct secondThirdNonNull
    let centralSpread :=
      Spread.spread (Incidence.lineThrough first center firstCenterDistinct)
        (Incidence.lineThrough second center secondCenterDistinct)
        firstCenterNonNull secondCenterNonNull
    let subtendedSpreadValue :=
      Spread.spread (Incidence.lineThrough third first firstThirdDistinct.symm)
        (Incidence.lineThrough third second secondThirdDistinct.symm)
        firstThirdReversedNonNull secondThirdReversedNonNull
    subtendedSpreadValue =
        Quadrance.quadrance first second / (4 * circleQuadrance) ∧
      centralSpread =
        4 * subtendedSpreadValue * (1 - subtendedSpreadValue) := by
  dsimp only
  let firstCenterDistinct :=
    Conic.point_ne_center_of_circle_quadrance_ne_zero circle center first
      circleQuadrance quadranceNonzero presentation firstOnCircle
  let secondCenterDistinct :=
    Conic.point_ne_center_of_circle_quadrance_ne_zero circle center second
      circleQuadrance quadranceNonzero presentation secondOnCircle
  let firstSecondNonNull := Conic.lineThrough_circle_points_nonNull circle center
    circleQuadrance twoNonzero quadranceNonzero presentation first second
    firstSecondDistinct firstOnCircle secondOnCircle
  let firstThirdNonNull := Conic.lineThrough_circle_points_nonNull circle center
    circleQuadrance twoNonzero quadranceNonzero presentation first third
    firstThirdDistinct firstOnCircle thirdOnCircle
  let secondThirdNonNull := Conic.lineThrough_circle_points_nonNull circle center
    circleQuadrance twoNonzero quadranceNonzero presentation second third
    secondThirdDistinct secondOnCircle thirdOnCircle
  let firstSecondReversedNonNull :
      ¬ (Incidence.lineThrough second first firstSecondDistinct.symm).IsNull := by
    exact Line.Null.reversedLine_nonNull
      first second firstSecondDistinct firstSecondNonNull
  let firstThirdReversedNonNull :
      ¬ (Incidence.lineThrough third first firstThirdDistinct.symm).IsNull := by
    exact Line.Null.reversedLine_nonNull
      first third firstThirdDistinct firstThirdNonNull
  let secondThirdReversedNonNull :
      ¬ (Incidence.lineThrough third second secondThirdDistinct.symm).IsNull := by
    exact Line.Null.reversedLine_nonNull
      second third secondThirdDistinct secondThirdNonNull
  let firstCenterNonNull :
      ¬ (Incidence.lineThrough first center firstCenterDistinct).IsNull := by
    intro lineNull
    apply quadranceNonzero
    have radiusZero :=
      (Quadrance.null_line_iff_quadrance_zero first center firstCenterDistinct).1 lineNull
    calc
      circleQuadrance = Quadrance.quadrance first center :=
        ((Conic.contains_iff_quadrance_eq circle center first circleQuadrance
          presentation).1 firstOnCircle).symm
      _ = 0 := radiusZero
  let secondCenterNonNull :
      ¬ (Incidence.lineThrough second center secondCenterDistinct).IsNull := by
    intro lineNull
    apply quadranceNonzero
    have radiusZero :=
      (Quadrance.null_line_iff_quadrance_zero second center secondCenterDistinct).1 lineNull
    calc
      circleQuadrance = Quadrance.quadrance second center :=
        ((Conic.contains_iff_quadrance_eq circle center second circleQuadrance
          presentation).1 secondOnCircle).symm
      _ = 0 := radiusZero
  let firstSpread :=
    Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
      (Incidence.lineThrough first third firstThirdDistinct)
      firstSecondNonNull firstThirdNonNull
  let secondSpread :=
    Spread.spread (Incidence.lineThrough second first firstSecondDistinct.symm)
      (Incidence.lineThrough second third secondThirdDistinct)
      firstSecondReversedNonNull secondThirdNonNull
  let subtendedSpreadValue :=
    Spread.spread (Incidence.lineThrough third first firstThirdDistinct.symm)
      (Incidence.lineThrough third second secondThirdDistinct.symm)
      firstThirdReversedNonNull secondThirdReversedNonNull
  let centralSpread :=
    Spread.spread (Incidence.lineThrough first center firstCenterDistinct)
      (Incidence.lineThrough second center secondCenterDistinct)
      firstCenterNonNull secondCenterNonNull
  let firstSideQuadrance := Quadrance.quadrance second third
  let secondSideQuadrance := Quadrance.quadrance first third
  let chordQuadrance := Quadrance.quadrance first second
  have firstRadiusFromPoint : Quadrance.quadrance first center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center first circleQuadrance
      presentation).1 firstOnCircle
  have secondRadiusFromPoint : Quadrance.quadrance second center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center second circleQuadrance
      presentation).1 secondOnCircle
  have thirdRadiusFromPoint : Quadrance.quadrance third center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center third circleQuadrance
      presentation).1 thirdOnCircle
  have firstRadius : Quadrance.quadrance center first = circleQuadrance := by
    calc
      Quadrance.quadrance center first = Quadrance.quadrance first center := Quadrance.quadrance_symm center first
      _ = circleQuadrance := firstRadiusFromPoint
  have secondRadius : Quadrance.quadrance center second = circleQuadrance := by
    calc
      Quadrance.quadrance center second = Quadrance.quadrance second center := Quadrance.quadrance_symm center second
      _ = circleQuadrance := secondRadiusFromPoint
  have thirdRadius : Quadrance.quadrance center third = circleQuadrance := by
    calc
      Quadrance.quadrance center third = Quadrance.quadrance third center := Quadrance.quadrance_symm center third
      _ = circleQuadrance := thirdRadiusFromPoint
  have extendedRatios := Triangles.Circumcenter.ExtendedSpread.extended_spread_law first second third center
    firstSecondDistinct firstThirdDistinct secondThirdDistinct
    firstSecondNonNull firstThirdNonNull secondThirdNonNull twoNonzero
    (firstRadius.trans secondRadius.symm)
    (secondRadius.trans thirdRadius.symm)
  dsimp only at extendedRatios
  rw [firstRadius] at extendedRatios
  change firstSpread / firstSideQuadrance =
        secondSpread / secondSideQuadrance ∧
      secondSpread / secondSideQuadrance =
        subtendedSpreadValue / chordQuadrance ∧
      subtendedSpreadValue / chordQuadrance =
        1 / (4 * circleQuadrance) at extendedRatios
  have firstSideNonzero : firstSideQuadrance ≠ 0 := by
    intro sideZero
    exact secondThirdNonNull
      ((Quadrance.null_line_iff_quadrance_zero second third
        secondThirdDistinct).2 sideZero)
  have secondSideNonzero : secondSideQuadrance ≠ 0 := by
    intro sideZero
    exact firstThirdNonNull
      ((Quadrance.null_line_iff_quadrance_zero first third
        firstThirdDistinct).2 sideZero)
  have chordNonzero : chordQuadrance ≠ 0 := by
    intro chordZero
    exact firstSecondNonNull
      ((Quadrance.null_line_iff_quadrance_zero first second
        firstSecondDistinct).2 chordZero)
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero :=
      ExplicitField.mul_ne_zero twoNonzero twoNonzero
    intro fourZero
    apply productNonzero
    calc
      (2 : K) * 2 = 4 := by ring1
      _ = 0 := fourZero
  have fourQuadranceNonzero : 4 * circleQuadrance ≠ 0 :=
    ExplicitField.mul_ne_zero fourNonzero quadranceNonzero
  have extendedCrossProducts := Triangles.Circumcenter.ExtendedSpread.extended_spread_law_cross_products
    firstSideQuadrance secondSideQuadrance chordQuadrance
    firstSpread secondSpread subtendedSpreadValue circleQuadrance
    firstSideNonzero secondSideNonzero chordNonzero
    fourQuadranceNonzero extendedRatios
  have subtendedCross :
      subtendedSpreadValue * (4 * circleQuadrance) = chordQuadrance :=
    extendedCrossProducts.2.2
  have fixedSubtendedSpread :
      subtendedSpreadValue =
        chordQuadrance / (4 * circleQuadrance) := by
    apply ExplicitField.eq_of_mul_eq_mul_right fourQuadranceNonzero
    calc
      subtendedSpreadValue * (4 * circleQuadrance) = chordQuadrance :=
        subtendedCross
      _ = (chordQuadrance / (4 * circleQuadrance)) *
          (4 * circleQuadrance) :=
        (ExplicitField.div_mul_cancel chordQuadrance
          fourQuadranceNonzero).symm
  let determinant :=
    (first.y - center.y) * (center.x - second.x) -
      (second.y - center.y) * (center.x - first.x)
  have centralSpreadFormula :
      centralSpread = determinant ^ 2 /
        (circleQuadrance * circleQuadrance) := by
    rw [show centralSpread =
      Spread.spread (Incidence.lineThrough first center firstCenterDistinct)
        (Incidence.lineThrough second center secondCenterDistinct)
        firstCenterNonNull secondCenterNonNull by rfl]
    rw [Spread.spread_from_points first second center firstCenterDistinct
      secondCenterDistinct firstCenterNonNull secondCenterNonNull]
    rw [firstRadiusFromPoint, secondRadiusFromPoint]
  have generalDeterminantIdentity :
      4 * determinant ^ 2 +
          (Quadrance.quadrance first center - Quadrance.quadrance second center) ^ 2 =
        chordQuadrance *
          (2 * Quadrance.quadrance first center + 2 * Quadrance.quadrance second center -
            chordQuadrance) := by
    unfold determinant chordQuadrance Quadrance.quadrance
    ring1
  have determinantIdentity :
      4 * determinant ^ 2 =
        chordQuadrance * (4 * circleQuadrance - chordQuadrance) := by
    calc
      4 * determinant ^ 2 = 4 * determinant ^ 2 +
          (Quadrance.quadrance first center - Quadrance.quadrance second center) ^ 2 := by
        rw [firstRadiusFromPoint, secondRadiusFromPoint]
        ring1
      _ = chordQuadrance *
          (2 * Quadrance.quadrance first center + 2 * Quadrance.quadrance second center -
            chordQuadrance) := generalDeterminantIdentity
      _ = chordQuadrance * (4 * circleQuadrance - chordQuadrance) := by
        rw [firstRadiusFromPoint, secondRadiusFromPoint]
        ring1
  have quadranceSquareNonzero :
      circleQuadrance * circleQuadrance ≠ 0 :=
    ExplicitField.mul_ne_zero quadranceNonzero quadranceNonzero
  have scalingFactorNonzero :
      4 * (circleQuadrance * circleQuadrance) ≠ 0 :=
    ExplicitField.mul_ne_zero fourNonzero quadranceSquareNonzero
  have centralScaled :
      centralSpread * (4 * (circleQuadrance * circleQuadrance)) =
        4 * determinant ^ 2 := by
    rw [centralSpreadFormula]
    calc
      (determinant ^ 2 / (circleQuadrance * circleQuadrance)) *
          (4 * (circleQuadrance * circleQuadrance)) =
        4 * ((determinant ^ 2 / (circleQuadrance * circleQuadrance)) *
          (circleQuadrance * circleQuadrance)) := by ring1
      _ = 4 * determinant ^ 2 := by
        rw [ExplicitField.div_mul_cancel (determinant ^ 2)
          quadranceSquareNonzero]
  have polynomialScaled :
      (4 * subtendedSpreadValue * (1 - subtendedSpreadValue)) *
          (4 * (circleQuadrance * circleQuadrance)) =
        chordQuadrance * (4 * circleQuadrance - chordQuadrance) := by
    calc
      (4 * subtendedSpreadValue * (1 - subtendedSpreadValue)) *
          (4 * (circleQuadrance * circleQuadrance)) =
        (subtendedSpreadValue * (4 * circleQuadrance)) *
          (4 * circleQuadrance -
            subtendedSpreadValue * (4 * circleQuadrance)) := by ring1
      _ = chordQuadrance * (4 * circleQuadrance - chordQuadrance) := by
        rw [subtendedCross]
  refine ⟨fixedSubtendedSpread, ?_⟩
  apply ExplicitField.eq_of_mul_eq_mul_right scalingFactorNonzero
  calc
    centralSpread * (4 * (circleQuadrance * circleQuadrance)) =
        4 * determinant ^ 2 := centralScaled
    _ = chordQuadrance * (4 * circleQuadrance - chordQuadrance) :=
      determinantIdentity
    _ = (4 * subtendedSpreadValue * (1 - subtendedSpreadValue)) *
        (4 * (circleQuadrance * circleQuadrance)) := polynomialScaled.symm

end

end Purelib.Curves.Plane.Conic

end

section
@[expose] public section

/-!
# Divine Proportions, Theorem 110: cyclic quadrilateral spreads

The six subtended spreads are finite field scalars.  Their four triangle
views are stored as explicit `SpreadTriple` certificates; Theorem 110 is then
exactly two applications of the Two spread triples theorem.

For an actual displayed cyclic quadrilateral on a non-null circle,
`normalizedCyclicSubtendedSpreads` constructs those six scalars as
`Q(A_i,A_j)/(4*K)` and derives every triple certificate from the finite
Subtended spread theorem.  The nonzero circle quadrance is visible because
over a general finite field a null circle can have null chords, for which the
book's spread quotients are not defined.
-/

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

variable {K : Type*} [ExplicitField K]

section

/-- The scale-free spread attached to a chord of a circle of quadrance `K`. -/
def normalizedSubtendedSpread
    (circleQuadrance : K) (first second : Plane.Point K) : K :=
  Quadrance.quadrance first second / (4 * circleQuadrance)

/-- Normalized subtended spread is symmetric in its chord endpoints. -/
theorem normalizedSubtendedSpread_symm
    (circleQuadrance : K) (first second : Plane.Point K) :
    normalizedSubtendedSpread circleQuadrance first second =
      normalizedSubtendedSpread circleQuadrance second first := by
  unfold normalizedSubtendedSpread
  rw [Quadrance.quadrance_symm first second]

/-- A spread subtended by two circle points at a third circle point equals the normalized chord quadrance. -/
theorem spread_at_circle_point_eq_normalized
    [Nontrivial K] [DecidableEq K]
    (circle : Conic K) (center first second vertex : Plane.Point K)
    (circleQuadrance : K)
    (firstSecondDistinct : first ≠ second)
    (firstVertexDistinct : first ≠ vertex)
    (secondVertexDistinct : second ≠ vertex)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second)
    (vertexOnCircle : circle.Contains vertex) :
    let vertexFirstNonNull :=
      Conic.lineThrough_circle_points_nonNull circle center circleQuadrance
        twoNonzero quadranceNonzero presentation vertex first
        firstVertexDistinct.symm vertexOnCircle firstOnCircle
    let vertexSecondNonNull :=
      Conic.lineThrough_circle_points_nonNull circle center circleQuadrance
        twoNonzero quadranceNonzero presentation vertex second
        secondVertexDistinct.symm vertexOnCircle secondOnCircle
    Spread.spread (Incidence.lineThrough vertex first firstVertexDistinct.symm)
        (Incidence.lineThrough vertex second secondVertexDistinct.symm)
        vertexFirstNonNull vertexSecondNonNull =
      normalizedSubtendedSpread circleQuadrance first second := by
  dsimp only
  have result := Curves.Plane.Conic.subtended_spread circle center first second vertex
    circleQuadrance firstSecondDistinct firstVertexDistinct
    secondVertexDistinct twoNonzero quadranceNonzero presentation
    firstOnCircle secondOnCircle vertexOnCircle
  dsimp only at result
  exact result.1

/-- Three chords viewed from a fourth point on the same non-null circle form a spread triple in their normalized
subtended-spread values. -/
theorem normalized_subtended_spreads_form_triple
    [Nontrivial K] [DecidableEq K]
    (circle : Conic K) (center first second third vertex : Plane.Point K)
    (circleQuadrance : K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (firstVertexDistinct : first ≠ vertex)
    (secondVertexDistinct : second ≠ vertex)
    (thirdVertexDistinct : third ≠ vertex)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second)
    (thirdOnCircle : circle.Contains third)
    (vertexOnCircle : circle.Contains vertex) :
    TripleSpread.SpreadTriple
      (normalizedSubtendedSpread circleQuadrance first second)
      (normalizedSubtendedSpread circleQuadrance second third)
      (normalizedSubtendedSpread circleQuadrance first third) := by
  let firstRayNonNull :=
    Conic.lineThrough_circle_points_nonNull circle center circleQuadrance
      twoNonzero quadranceNonzero presentation vertex first
      firstVertexDistinct.symm vertexOnCircle firstOnCircle
  let secondRayNonNull :=
    Conic.lineThrough_circle_points_nonNull circle center circleQuadrance
      twoNonzero quadranceNonzero presentation vertex second
      secondVertexDistinct.symm vertexOnCircle secondOnCircle
  let thirdRayNonNull :=
    Conic.lineThrough_circle_points_nonNull circle center circleQuadrance
      twoNonzero quadranceNonzero presentation vertex third
      thirdVertexDistinct.symm vertexOnCircle thirdOnCircle
  have rawTriple := Triple.three_lines_form_spreadTriple
    (Incidence.lineThrough vertex first firstVertexDistinct.symm)
    (Incidence.lineThrough vertex second secondVertexDistinct.symm)
    (Incidence.lineThrough vertex third thirdVertexDistinct.symm)
    firstRayNonNull secondRayNonNull thirdRayNonNull
  have secondThirdSpread := spread_at_circle_point_eq_normalized circle
    center
    second third vertex circleQuadrance secondThirdDistinct
    secondVertexDistinct thirdVertexDistinct twoNonzero quadranceNonzero
    presentation secondOnCircle thirdOnCircle vertexOnCircle
  have firstThirdSpread := spread_at_circle_point_eq_normalized circle
    center
    first third vertex circleQuadrance firstThirdDistinct
    firstVertexDistinct thirdVertexDistinct twoNonzero quadranceNonzero
    presentation firstOnCircle thirdOnCircle vertexOnCircle
  have firstSecondSpread := spread_at_circle_point_eq_normalized circle
    center
    first second vertex circleQuadrance firstSecondDistinct
    firstVertexDistinct secondVertexDistinct twoNonzero quadranceNonzero
    presentation firstOnCircle secondOnCircle vertexOnCircle
  dsimp only at secondThirdSpread firstThirdSpread firstSecondSpread
  rw [secondThirdSpread, firstThirdSpread, firstSecondSpread] at rawTriple
  exact Triple.spreadTriple_rotate (Triple.spreadTriple_rotate rawTriple)
end

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end
