module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Geometry.Circles.Diameter.Quadrance
public import Purelib.Geometry.Plane.Line.Altitude
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Affine.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Dot
import Purelib.Geometry.Plane.Point.Quadrance
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

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Point.Affine

section
@[expose] public section

/-!
# Divine Proportions, Theorem 117: the nine point circle

All nine points and the circle are explicit finite constructions.  The six
midpoint incidences follow from the cleared Euler relation `2C+O=A₁+A₂+A₃`.
For an altitude foot, the side-midpoint and vertex--orthocenter midpoint form
a diameter: a denominator-cleared dot-product lemma supplies the right-angle
calculation even when the foot coincides with a diameter endpoint.
-/

namespace Purelib.Geometry.Quadrilaterals.EightPointCircle

variable {K : Type*} [ExplicitField K]

/-- The midpoint of the side `A₁A₂` of a displayed quadrilateral. -/
def quadrilateralSideMidpoint12
    (first second _third _fourth : Plane.Point K) : Plane.Point K :=
  Affine.midpoint first second

/-- The midpoint of the side `A₂A₃` of a displayed quadrilateral. -/
def quadrilateralSideMidpoint23
    (_first second third _fourth : Plane.Point K) : Plane.Point K :=
  Affine.midpoint second third

/-- The midpoint of the side `A₃A₄` of a displayed quadrilateral. -/
def quadrilateralSideMidpoint34
    (_first _second third fourth : Plane.Point K) : Plane.Point K :=
  Affine.midpoint third fourth

/-- The midpoint of the side `A₁A₄` of a displayed quadrilateral. -/
def quadrilateralSideMidpoint14
    (first _second _third fourth : Plane.Point K) : Plane.Point K :=
  Affine.midpoint first fourth

/-- Midpoint of the midpoints of two opposite quadrilateral sides.

The same point is obtained from the other pair of opposite side midpoints. -/
def eightPointCenter (first second third fourth :
  Plane.Point K) : Plane.Point K :=
  Affine.midpoint (quadrilateralSideMidpoint12 first second third fourth)
    (quadrilateralSideMidpoint34 first second third fourth)

/-- Circle centered at the quadrilateral midpoint center and passing through the first side midpoint.

This construction is defined for arbitrary vertices; perpendicular diagonals and non-null sides supply the eight
incidence guarantees proved separately. -/
def eightPointCircle [Nontrivial K]
    (first second third fourth : Plane.Point K) : Conic K :=
  let center := eightPointCenter first second third fourth
  Conic.circleConic center
    (Quadrance.quadrance center
      (quadrilateralSideMidpoint12 first second third fourth))

/-- The two pairs of opposite side midpoints of any quadrilateral have the same midpoint. This is the finite coordinate
form of the parallelogram-center observation behind the eight-point circle. -/
theorem quadrilateral_opposite_midpoint_centers_eq
    (first second third fourth : Plane.Point K) :
    Affine.midpoint (quadrilateralSideMidpoint12 first second third fourth)
        (quadrilateralSideMidpoint34 first second third fourth) =
      Affine.midpoint (quadrilateralSideMidpoint23 first second third fourth)
        (quadrilateralSideMidpoint14 first second third fourth) := by
  apply Plane.Point.ext
  · simp only [quadrilateralSideMidpoint12,
      quadrilateralSideMidpoint23,
      quadrilateralSideMidpoint34,
        quadrilateralSideMidpoint14, Affine.midpoint,
      ExplicitField.div_eq_mul_inv]
    ring1
  · simp only [quadrilateralSideMidpoint12,
      quadrilateralSideMidpoint23,
      quadrilateralSideMidpoint34,
        quadrilateralSideMidpoint14, Affine.midpoint,
      ExplicitField.div_eq_mul_inv]
    ring1

/-- Perpendicular diagonals make the corner at `M₁₂` of the midpoint parallelogram right. No division is cancelled in
this calculation. -/
theorem quadrilateral_midpoint_right_angle
    [DecidableEq K]
    (first second third fourth : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondFourthDistinct : second ≠ fourth)
    (diagonalsPerpendicular :
      (Incidence.lineThrough first third firstThirdDistinct).Perpendicular
        (Incidence.lineThrough second fourth secondFourthDistinct)) :
    Dot.pointVectorDot
        (quadrilateralSideMidpoint12 first second third fourth)
        (quadrilateralSideMidpoint23 first second third fourth)
        (quadrilateralSideMidpoint14 first second third fourth) = 0 := by
  unfold Plane.Line.Perpendicular Incidence.lineThrough at diagonalsPerpendicular
  simp only [quadrilateralSideMidpoint12,
    quadrilateralSideMidpoint23,
    quadrilateralSideMidpoint14, Dot.pointVectorDot, Affine.midpoint,
    ExplicitField.div_eq_mul_inv]
  calc
    (((second.x + third.x) * (2 : K)⁻¹ -
            (first.x + second.x) * (2 : K)⁻¹) *
          ((first.x + fourth.x) * (2 : K)⁻¹ -
            (first.x + second.x) * (2 : K)⁻¹) +
        ((second.y + third.y) * (2 : K)⁻¹ -
            (first.y + second.y) * (2 : K)⁻¹) *
          ((first.y + fourth.y) * (2 : K)⁻¹ -
            (first.y + second.y) * (2 : K)⁻¹)) =
      ((first.y - third.y) * (second.y - fourth.y) +
          (third.x - first.x) * (fourth.x - second.x)) *
        ((2 : K)⁻¹ * (2 : K)⁻¹) := by ring1
    _ = 0 := by rw [diagonalsPerpendicular]; ring1

/-- Exercise 18.3 (Eight point circle): if the two displayed diagonals are perpendicular and all four target sides are
non-null, the four side midpoints and the four altitude feet from them to the opposite sides lie on one explicitly
constructed circle. -/
theorem exercise_18_3
    [Nontrivial K] [DecidableEq K]
    (first second third fourth : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (secondThirdDistinct : second ≠ third)
    (thirdFourthDistinct : third ≠ fourth)
    (firstFourthDistinct : first ≠ fourth)
    (firstThirdDistinct : first ≠ third)
    (secondFourthDistinct : second ≠ fourth)
    (twoNonzero : (2 : K) ≠ 0)
    (diagonalsPerpendicular :
      (Incidence.lineThrough first third firstThirdDistinct).Perpendicular
        (Incidence.lineThrough second fourth secondFourthDistinct))
    (firstSideNonNull :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull)
    (secondSideNonNull :
      ¬ (Incidence.lineThrough second third secondThirdDistinct).IsNull)
    (thirdSideNonNull :
      ¬ (Incidence.lineThrough third fourth thirdFourthDistinct).IsNull)
    (fourthSideNonNull :
      ¬ (Incidence.lineThrough first fourth firstFourthDistinct).IsNull) :
    let midpoint12 := quadrilateralSideMidpoint12 first second third fourth
    let midpoint23 := quadrilateralSideMidpoint23 first second third fourth
    let midpoint34 := quadrilateralSideMidpoint34 first second third fourth
    let midpoint14 := quadrilateralSideMidpoint14 first second third fourth
    let circle := eightPointCircle first second third fourth
    circle.Contains midpoint12 ∧
      circle.Contains midpoint23 ∧
      circle.Contains midpoint34 ∧
      circle.Contains midpoint14 ∧
      circle.Contains (Altitude.altitudeFoot midpoint12
        (Incidence.lineThrough third fourth thirdFourthDistinct) thirdSideNonNull) ∧
      circle.Contains (Altitude.altitudeFoot midpoint23
        (Incidence.lineThrough first fourth firstFourthDistinct) fourthSideNonNull) ∧
      circle.Contains (Altitude.altitudeFoot midpoint34
        (Incidence.lineThrough first second firstSecondDistinct) firstSideNonNull) ∧
      circle.Contains (Altitude.altitudeFoot midpoint14
        (Incidence.lineThrough second third secondThirdDistinct) secondSideNonNull) := by
  dsimp only
  let midpoint12 := quadrilateralSideMidpoint12 first second third fourth
  let midpoint23 := quadrilateralSideMidpoint23 first second third fourth
  let midpoint34 := quadrilateralSideMidpoint34 first second third fourth
  let midpoint14 := quadrilateralSideMidpoint14 first second third fourth
  let center := eightPointCenter first second third fourth
  let radius := Quadrance.quadrance center midpoint12
  let circle := eightPointCircle first second third fourth
  have centersEqual : center = Affine.midpoint midpoint23 midpoint14 := by
    exact quadrilateral_opposite_midpoint_centers_eq first second third fourth
  have midpoint34Quadrance :
      Quadrance.quadrance center midpoint34 = radius := by
    exact (Quadrance.midpoint_equal_quadrance midpoint12 midpoint34 twoNonzero).symm
  have rightAngle : Dot.pointVectorDot midpoint12 midpoint23 midpoint14 = 0 :=
    quadrilateral_midpoint_right_angle first second third fourth
      firstThirdDistinct secondFourthDistinct diagonalsPerpendicular
  have midpoint23QuadranceRaw := Circles.Diameter.Quadrance.midpoint_right_quadrance_of_dot_zero
    midpoint23 midpoint14 midpoint12 twoNonzero rightAngle
  rw [← centersEqual] at midpoint23QuadranceRaw
  have midpoint23Quadrance : Quadrance.quadrance center midpoint23 = radius :=
    midpoint23QuadranceRaw
  have midpoint14Pair := Quadrance.midpoint_equal_quadrance midpoint23 midpoint14
    twoNonzero
  rw [← centersEqual] at midpoint14Pair
  have midpoint14Quadrance : Quadrance.quadrance center midpoint14 = radius :=
    midpoint14Pair.symm.trans midpoint23Quadrance
  have foot12Quadrance :
      Quadrance.quadrance center
          (Altitude.altitudeFoot midpoint12
            (Incidence.lineThrough third fourth thirdFourthDistinct)
            thirdSideNonNull) = radius :=
    Circles.Diameter.Quadrance.altitudeFoot_diameter_quadrance midpoint12 third fourth
      thirdFourthDistinct twoNonzero thirdSideNonNull
  have foot23Raw :
      Quadrance.quadrance (Affine.midpoint midpoint23 midpoint14)
          (Altitude.altitudeFoot midpoint23
            (Incidence.lineThrough first fourth firstFourthDistinct)
            fourthSideNonNull) =
        Quadrance.quadrance (Affine.midpoint midpoint23 midpoint14) midpoint23 :=
    Circles.Diameter.Quadrance.altitudeFoot_diameter_quadrance midpoint23 first fourth
      firstFourthDistinct twoNonzero fourthSideNonNull
  have foot23Quadrance :
      Quadrance.quadrance center
          (Altitude.altitudeFoot midpoint23
            (Incidence.lineThrough first fourth firstFourthDistinct)
            fourthSideNonNull) = radius := by
    rw [← centersEqual] at foot23Raw
    exact foot23Raw.trans midpoint23Quadrance
  have foot34Raw :
      Quadrance.quadrance (Affine.midpoint midpoint34 midpoint12)
          (Altitude.altitudeFoot midpoint34
            (Incidence.lineThrough first second firstSecondDistinct)
            firstSideNonNull) =
        Quadrance.quadrance (Affine.midpoint midpoint34 midpoint12) midpoint34 :=
    Circles.Diameter.Quadrance.altitudeFoot_diameter_quadrance midpoint34 first second
      firstSecondDistinct twoNonzero firstSideNonNull
  have foot34Quadrance :
      Quadrance.quadrance center
          (Altitude.altitudeFoot midpoint34
            (Incidence.lineThrough first second firstSecondDistinct)
            firstSideNonNull) = radius := by
    rw [Affine.midpoint_symm midpoint34 midpoint12] at foot34Raw
    exact foot34Raw.trans midpoint34Quadrance
  have foot14Raw :
      Quadrance.quadrance (Affine.midpoint midpoint14 midpoint23)
          (Altitude.altitudeFoot midpoint14
            (Incidence.lineThrough second third secondThirdDistinct)
            secondSideNonNull) =
        Quadrance.quadrance (Affine.midpoint midpoint14 midpoint23) midpoint14 :=
    Circles.Diameter.Quadrance.altitudeFoot_diameter_quadrance midpoint14 second third
      secondThirdDistinct twoNonzero secondSideNonNull
  have foot14Quadrance :
      Quadrance.quadrance center
          (Altitude.altitudeFoot midpoint14
            (Incidence.lineThrough second third secondThirdDistinct)
            secondSideNonNull) = radius := by
    rw [Affine.midpoint_symm midpoint14 midpoint23, ← centersEqual] at foot14Raw
    exact foot14Raw.trans midpoint14Quadrance
  have presentation := Conic.circleConic_isCirclePresentation center radius
  have containsOfQuadrance := fun (point : Plane.Point K)
      (pointQuadrance : Quadrance.quadrance center point = radius) =>
    (Conic.contains_iff_quadrance_eq circle center point radius
      presentation).2 ((Quadrance.quadrance_symm point center).trans pointQuadrance)
  exact ⟨containsOfQuadrance midpoint12 rfl,
    containsOfQuadrance midpoint23 midpoint23Quadrance,
    containsOfQuadrance midpoint34 midpoint34Quadrance,
    containsOfQuadrance midpoint14 midpoint14Quadrance,
    containsOfQuadrance _ foot12Quadrance,
    containsOfQuadrance _ foot23Quadrance,
    containsOfQuadrance _ foot34Quadrance,
    containsOfQuadrance _ foot14Quadrance⟩

end Purelib.Geometry.Quadrilaterals.EightPointCircle

end
