module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Algebra.Group.Negation
public import Purelib.Geometry.Plane.Line.Affine
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Affine.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Affine

open Purelib.Geometry.Plane.Point

section
@[expose] public section

/-!
# Divine Proportions, §16.2: equal products

The source derives Theorem 106 from subtended spreads and the Spread law.  The
finite algebra underneath that proof is stronger: along any displayed chord,
the product of the two endpoint quadrances is the square of the intersection
point's circle-power.  This form needs no non-null hypotheses or division.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

/-- Equal endpoint radii turn the circle-power of a point on their line into the displayed, denominator-free chord
parameter product. -/
private theorem thalesPoint_circle_power
    (first second center : Plane.Point K) (circleQuadrance scale : K)
    (firstRadius : Quadrance.quadrance first center = circleQuadrance)
    (secondRadius : Quadrance.quadrance second center = circleQuadrance) :
    Quadrance.quadrance (Affine.thalesPoint scale first second) center - circleQuadrance =
      -(scale * (1 - scale) * Quadrance.quadrance first second) := by
  calc
    Quadrance.quadrance (Affine.thalesPoint scale first second) center - circleQuadrance =
        (1 - scale) * Quadrance.quadrance first center +
          scale * Quadrance.quadrance second center -
          scale * (1 - scale) * Quadrance.quadrance first second -
          circleQuadrance := by
      unfold Quadrance.quadrance Affine.thalesPoint Affine.affineCombination
      ring1
    _ = -(scale * (1 - scale) * Quadrance.quadrance first second) := by
      rw [firstRadius, secondRadius]
      ring1

/-- The signed, denominator-free circle-power formula along a chord. Keeping the Thales parameter retains the sign
information that is lost after squaring in the Equal products theorem. -/
theorem thalesPoint_circle_power_of_circle
    (circle : Conic K) (center first second : Plane.Point K)
    (circleQuadrance scale : K)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second) :
    Quadrance.quadrance (Affine.thalesPoint scale first second) center - circleQuadrance =
      -(scale * (1 - scale) * Quadrance.quadrance first second) := by
  have firstRadius : Quadrance.quadrance first center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center first circleQuadrance
      presentation).1 firstOnCircle
  have secondRadius : Quadrance.quadrance second center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center second circleQuadrance
      presentation).1 secondOnCircle
  exact thalesPoint_circle_power first second center circleQuadrance scale
    firstRadius secondRadius

/-- The denominator-free chord-power identity. It strengthens the algebraic core of Theorem 106 by allowing any circle
quadrance and any displayed chord, including a null chord. -/
theorem chord_quadrance_product_eq_circle_power [DecidableEq K]
    (circle : Conic K) (center : Plane.Point K) (circleQuadrance : K)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (first second point : Plane.Point K) (distinct : first ≠ second)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second)
    (pointOnLine :
      (Incidence.lineThrough first second distinct).Contains point) :
    Quadrance.quadrance first point * Quadrance.quadrance point second =
      (Quadrance.quadrance point center - circleQuadrance) ^ 2 := by
  have firstRadius : Quadrance.quadrance first center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center first circleQuadrance
      presentation).1 firstOnCircle
  have secondRadius : Quadrance.quadrance second center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center second circleQuadrance
      presentation).1 secondOnCircle
  rcases Conic.thalesPoint_exists_of_on_line first second point distinct pointOnLine with
    ⟨scale, pointFormula⟩
  subst point
  rw [Conic.quadrance_first_thalesPoint, Conic.quadrance_thalesPoint_second,
    thalesPoint_circle_power first second center circleQuadrance scale
      firstRadius secondRadius]
  ring1

/-- Theorem 106 (Equal products): the products cut out by two intersecting chords of a circle are equal. -/
theorem equal_products [DecidableEq K]
    (circle : Conic K) (center : Plane.Point K) (circleQuadrance : K)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (first second third fourth intersection : Plane.Point K)
    (distinct :
      first ≠ second ∧ first ≠ third ∧ first ≠ fourth ∧
        second ≠ third ∧ second ≠ fourth ∧ third ≠ fourth)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second)
    (thirdOnCircle : circle.Contains third)
    (fourthOnCircle : circle.Contains fourth)
    (intersectionOnFirstFourth :
      (Incidence.lineThrough first fourth distinct.2.2.1).Contains intersection)
    (intersectionOnSecondThird :
      (Incidence.lineThrough second third distinct.2.2.2.1).Contains intersection) :
    Quadrance.quadrance first intersection * Quadrance.quadrance intersection fourth =
      Quadrance.quadrance second intersection * Quadrance.quadrance intersection third := by
  calc
    Quadrance.quadrance first intersection * Quadrance.quadrance intersection fourth =
        (Quadrance.quadrance intersection center - circleQuadrance) ^ 2 :=
      chord_quadrance_product_eq_circle_power circle center circleQuadrance
        presentation first fourth intersection distinct.2.2.1
        firstOnCircle fourthOnCircle intersectionOnFirstFourth
    _ = Quadrance.quadrance second intersection * Quadrance.quadrance intersection third :=
      (chord_quadrance_product_eq_circle_power circle center circleQuadrance
        presentation second third intersection distinct.2.2.2.1
        secondOnCircle thirdOnCircle intersectionOnSecondThird).symm

end

end Purelib.Curves.Plane.Conic

end
