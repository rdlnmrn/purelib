module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Polygons.Regular.Pentagon.MetricScalars
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Affine.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Polygons.Regular.CornerTriangle
import Purelib.Geometry.Triangles.Median.Quadrance
public import Purelib.Polynomial.Recurrence.Spread.Roots.Five.Radical
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Point.Affine

open Purelib.Geometry.Polygons.Regular

open Purelib.Polynomial.Recurrence.Spread.Roots.Five

open Purelib.Polynomial.Recurrence.Spread.Roots.Five.Radical

section
@[expose] public section

/-!
# Divine Proportions, Exercises 14.3 and 14.4

The source writes the two nonzero order-five spread values using a square
root `r²=5`.  Here `alpha` and `beta` are finite field expressions built from
an explicitly supplied root; no completed real or selected algebraic closure
is introduced.  Their root classification and logistic identities are proved
constructively.

`Figure` is the exact finite three-vertex window from Theorem 98, labelled as
`B,A,E` around the center `P`, together with the one radial spread used by
Exercise 14.4.  Its midpoint definitions are the points `M` and `F` in Figure
14.4.  The four quadrance displays follow from Polygon triangle and the
midpoint identities.  The printed decimals are retained as exact rational
millionth brackets with opposite quadratic signs.
-/

namespace Purelib.Geometry.Polygons.Regular.Pentagon.Metrics

variable {K : Type*} [ExplicitField K]
variable [Nontrivial K] [DecidableEq K]

set_option genInjectivity false in
/-- Figure 14.4 as finite data. The corner configuration is labelled `first=B`, `second=A`, `third=E`, and `center=P`.
Its last field is the radial spread `s(PB,PE)=alpha` used in Exercise 14.4. -/
structure Figure (root : K) where
  /-- The retained three-vertex corner configuration, labeled B, A and E around P. -/ corner :
    CornerTriangle.PolygonTriangleConfiguration K (ChapterFourteenPentagonMetrics.alpha root)
  /-- The first-to-third radial spread equals the explicitly supplied order-five alpha value. -/ radialDiagonalSpread :
    Spread.spread
        (Incidence.lineThrough corner.center corner.first corner.centerFirstDistinct)
        (Incidence.lineThrough corner.center corner.third corner.centerThirdDistinct)
        corner.centerFirstNonNull corner.centerThirdNonNull = ChapterFourteenPentagonMetrics.alpha root

constructive_injectivity Figure

namespace Figure

/-- The common side quadrance `R=Q(A,B)`. -/
def sideQuadrance (figure :
  Figure (K := K) root) : K :=
  Quadrance.quadrance figure.corner.second figure.corner.first

/-- The point `M`, the midpoint of the side `AB`. -/
def firstMidpoint (figure :
  Figure (K := K) root) : Geometry.Plane.Point K :=
  Affine.midpoint figure.corner.second figure.corner.first

/-- The point `F`, the midpoint of the diagonal `BE`. -/
def diagonalMidpoint (figure :
  Figure (K := K) root) : Geometry.Plane.Point K :=
  Affine.midpoint figure.corner.first figure.corner.third

/-- The adjacent radial spread `s(PA,PB)`. -/
def adjacentRadialSpread (figure :
  Figure (K := K) root) : K :=
  Spread.spread
    (Incidence.lineThrough figure.corner.center figure.corner.second
      figure.corner.centerSecondDistinct)
    (Incidence.lineThrough figure.corner.center figure.corner.first
      figure.corner.centerFirstDistinct)
    figure.corner.centerSecondNonNull figure.corner.centerFirstNonNull

/-- The diagonal radial spread `s(PB,PE)`. -/
def diagonalRadialSpread (figure :
  Figure (K := K) root) : K :=
  Spread.spread
    (Incidence.lineThrough figure.corner.center figure.corner.first
      figure.corner.centerFirstDistinct)
    (Incidence.lineThrough figure.corner.center figure.corner.third
      figure.corner.centerThirdDistinct)
    figure.corner.centerFirstNonNull figure.corner.centerThirdNonNull

/-- Exercise 14.3's six Figure 14.4 quadrance equalities. The first two are the two printed forms of `Q(P,A)`; the next
two concern `M` and `F`; the last two are the two printed forms of `Q(B,E)`. -/
theorem exercise_14_3 (root : K) (rootNonzero : root ≠
  0)
    (rootSquare : root ^ 2 = 5) (twoNonzero : (2 : K) ≠ 0)
    (figure : Figure (K := K) root) :
    Quadrance.quadrance figure.corner.center figure.corner.second =
        (1 - ChapterFourteenPentagonMetrics.alpha root) * figure.sideQuadrance / ChapterFourteenPentagonMetrics.beta
          root ∧
      Quadrance.quadrance figure.corner.center figure.corner.second =
        figure.sideQuadrance / (4 * ChapterFourteenPentagonMetrics.alpha root) ∧
      Quadrance.quadrance figure.corner.center figure.firstMidpoint =
        (1 - ChapterFourteenPentagonMetrics.alpha root) * figure.sideQuadrance / (4 *
          ChapterFourteenPentagonMetrics.alpha root) ∧
      Quadrance.quadrance figure.corner.first figure.diagonalMidpoint =
        (1 - ChapterFourteenPentagonMetrics.alpha root) * figure.sideQuadrance ∧
      Quadrance.quadrance figure.corner.first figure.corner.third =
        4 * (1 - ChapterFourteenPentagonMetrics.alpha root) * figure.sideQuadrance ∧
      Quadrance.quadrance figure.corner.first figure.corner.third =
        ChapterFourteenPentagonMetrics.beta root * figure.sideQuadrance / ChapterFourteenPentagonMetrics.alpha root :=
          by
  have aNonzero := Radical.alpha_ne_zero root rootNonzero rootSquare twoNonzero
  have bNonzero := Radical.beta_ne_zero root rootNonzero rootSquare twoNonzero
  rcases CornerTriangle.polygon_triangle (ChapterFourteenPentagonMetrics.alpha root) aNonzero twoNonzero figure.corner
    with
    ⟨firstSide, _secondSide, diagonal, _firstSpread, _thirdSpread,
      _apexSpread⟩
  let q := Quadrance.quadrance figure.corner.center figure.corner.second
  let r := figure.sideQuadrance
  let d := Quadrance.quadrance figure.corner.first figure.corner.third
  have sideValue : r = 4 * ChapterFourteenPentagonMetrics.alpha root * q := by
    unfold r q sideQuadrance
    calc
      Quadrance.quadrance figure.corner.second figure.corner.first =
          Quadrance.quadrance figure.corner.first figure.corner.second :=
        Quadrance.quadrance_symm _ _
      _ = 4 * ChapterFourteenPentagonMetrics.alpha root *
          Quadrance.quadrance figure.corner.center figure.corner.first := firstSide
      _ = 4 * ChapterFourteenPentagonMetrics.alpha root *
          Quadrance.quadrance figure.corner.center figure.corner.second := by
        rw [figure.corner.secondRadius]
  have diagonalValue : d = 16 * ChapterFourteenPentagonMetrics.alpha root * (1 - ChapterFourteenPentagonMetrics.alpha
    root) * q := by
    unfold d q
    calc
      Quadrance.quadrance figure.corner.first figure.corner.third =
          16 * ChapterFourteenPentagonMetrics.alpha root * (1 - ChapterFourteenPentagonMetrics.alpha root) *
            Quadrance.quadrance figure.corner.center figure.corner.first := diagonal
      _ = 16 * ChapterFourteenPentagonMetrics.alpha root * (1 - ChapterFourteenPentagonMetrics.alpha root) *
          Quadrance.quadrance figure.corner.center figure.corner.second := by
        rw [figure.corner.secondRadius]
  rcases Pentagon.MetricScalars.metricScalars (ChapterFourteenPentagonMetrics.alpha root)
    (ChapterFourteenPentagonMetrics.beta root) q r d aNonzero bNonzero
      twoNonzero (Radical.beta_logistic_alpha root rootSquare twoNonzero)
      sideValue diagonalValue with
    ⟨radiusFirst, radiusSecond, midpointScalar, halfDiagonal,
      diagonalSide, diagonalRatio⟩
  have midpointValue :
      Quadrance.quadrance figure.corner.center figure.firstMidpoint =
        (1 - ChapterFourteenPentagonMetrics.alpha root) * r / (4 * ChapterFourteenPentagonMetrics.alpha root) := by
    unfold firstMidpoint
    rw [Triangles.Median.Quadrance.median_quadrance _ _ _ twoNonzero]
    change (2 *
      (Quadrance.quadrance figure.corner.center figure.corner.first +
        Quadrance.quadrance figure.corner.center figure.corner.second) - r) / 4 = _
    rw [← figure.corner.secondRadius]
    exact midpointScalar
  have diagonalMidpointValue :
      Quadrance.quadrance figure.corner.first figure.diagonalMidpoint =
        (1 - ChapterFourteenPentagonMetrics.alpha root) * r := by
    unfold diagonalMidpoint
    calc
      Quadrance.quadrance figure.corner.first
          (Affine.midpoint figure.corner.first figure.corner.third) =
        Quadrance.quadrance (Affine.midpoint figure.corner.first figure.corner.third)
          figure.corner.first := Quadrance.quadrance_symm _ _
      _ = d / 4 := Quadrance.midpoint_quadrance _ _ twoNonzero
      _ = (1 - ChapterFourteenPentagonMetrics.alpha root) * r := halfDiagonal
  exact ⟨radiusFirst, radiusSecond, midpointValue,
    diagonalMidpointValue, diagonalSide, diagonalRatio⟩

omit [Nontrivial K] in
/-- The adjacent radial spread in Figure 14.4 is `beta`. -/
theorem adjacentRadialSpread_eq_beta (root : K)
    (rootSquare : root ^ 2 = 5) (twoNonzero : (2 : K) ≠ 0)
    (figure : Figure (K := K) root) :
    figure.adjacentRadialSpread = ChapterFourteenPentagonMetrics.beta root := by
  unfold adjacentRadialSpread
  calc
    Spread.spread
        (Incidence.lineThrough figure.corner.center figure.corner.second
          figure.corner.centerSecondDistinct)
        (Incidence.lineThrough figure.corner.center figure.corner.first
          figure.corner.centerFirstDistinct)
        figure.corner.centerSecondNonNull figure.corner.centerFirstNonNull =
      Spread.spread
        (Incidence.lineThrough figure.corner.center figure.corner.first
          figure.corner.centerFirstDistinct)
        (Incidence.lineThrough figure.corner.center figure.corner.second
          figure.corner.centerSecondDistinct)
        figure.corner.centerFirstNonNull figure.corner.centerSecondNonNull :=
      Spread.spread_symm _ _ _ _
    _ = 4 * ChapterFourteenPentagonMetrics.alpha root * (1 - ChapterFourteenPentagonMetrics.alpha root) :=
      figure.corner.doubleRadialSpread
    _ = ChapterFourteenPentagonMetrics.beta root :=
      (Radical.beta_logistic_alpha root rootSquare twoNonzero).symm

omit [Nontrivial K] in
/-- The supplied diagonal radial spread is exactly `alpha`. -/
theorem diagonalRadialSpread_eq_alpha (figure :
  Figure (K := K) root) :
    figure.diagonalRadialSpread = ChapterFourteenPentagonMetrics.alpha root := by
  exact figure.radialDiagonalSpread

/-- Exercise 14.4: `beta:alpha` is both the displayed spread proportion and the diagonal-to-side quadrance proportion.
-/
theorem exercise_14_4 (root : K) (rootNonzero : root ≠
  0)
    (rootSquare : root ^ 2 = 5) (twoNonzero : (2 : K) ≠ 0)
    (figure : Figure (K := K) root) :
    ChapterFourteenPentagonMetrics.beta root / ChapterFourteenPentagonMetrics.alpha root =
        figure.adjacentRadialSpread / figure.diagonalRadialSpread ∧
      ChapterFourteenPentagonMetrics.beta root / ChapterFourteenPentagonMetrics.alpha root =
        Quadrance.quadrance figure.corner.first figure.corner.third /
          figure.sideQuadrance := by
  have aNonzero := Radical.alpha_ne_zero root rootNonzero rootSquare twoNonzero
  have metric := exercise_14_3 root rootNonzero rootSquare twoNonzero
    figure
  have diagonalRatio := metric.2.2.2.2.2
  have sideNonzero : figure.sideQuadrance ≠ 0 := by
    intro sideZero
    apply figure.corner.firstSecondNonNull
    change Line.Basic.lineNorm
      (Incidence.lineThrough figure.corner.first figure.corner.second
        figure.corner.firstSecondDistinct) = 0
    rw [Quadrance.lineThrough_norm_eq_quadrance]
    calc
      Quadrance.quadrance figure.corner.first figure.corner.second =
          Quadrance.quadrance figure.corner.second figure.corner.first :=
        Quadrance.quadrance_symm _ _
      _ = figure.sideQuadrance := rfl
      _ = 0 := sideZero
  constructor
  · rw [adjacentRadialSpread_eq_beta root rootSquare twoNonzero
      figure,
      diagonalRadialSpread_eq_alpha figure]
  · apply ExplicitField.eq_of_mul_eq_mul_right sideNonzero
    calc
      (ChapterFourteenPentagonMetrics.beta root / ChapterFourteenPentagonMetrics.alpha root) * figure.sideQuadrance =
          ChapterFourteenPentagonMetrics.beta root * figure.sideQuadrance / ChapterFourteenPentagonMetrics.alpha root :=
            by
        simp only [ExplicitField.div_eq_mul_inv]
        ring1
      _ = Quadrance.quadrance figure.corner.first figure.corner.third :=
        diagonalRatio.symm
      _ = (Quadrance.quadrance figure.corner.first figure.corner.third /
          figure.sideQuadrance) * figure.sideQuadrance :=
        (ExplicitField.div_mul_cancel _ sideNonzero).symm

end Figure

end Purelib.Geometry.Polygons.Regular.Pentagon.Metrics

end
