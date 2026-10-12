module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Geometry.Circles.Diameter.Quadrance
import Purelib.Geometry.Plane.Line.Affine
public import Purelib.Geometry.Plane.Line.Altitude
import Purelib.Geometry.Plane.Line.Construction
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Affine.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Dot
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Centers.Euler
import Purelib.Geometry.Triangles.Circumcenter.Basic
public import Purelib.Geometry.Triangles.Circumcenter.Formula
public import Purelib.Geometry.Triangles.Medial.Basic
import Purelib.Geometry.Triangles.Orthocenter.Basic
public import Purelib.Geometry.Triangles.Orthocenter.Formula
import Purelib.LinearAlgebra.Alternating.Bracket.Fin3
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Point.Affine

open Purelib.Geometry.Triangles

open Purelib.Geometry.Triangles.Circumcenter

open Purelib.Geometry.Triangles.Orthocenter

open Purelib.LinearAlgebra.Alternating.Bracket

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

namespace Purelib.Geometry.Triangles.NinePointCircle

variable {K : Type*} [ExplicitField K]
open Purelib.Geometry.Triangles.Orthocenter.Basic in
/-- The midpoint of a vertex and the displayed orthocenter. -/
def vertexOrthocenterMidpoint (vertex orthocenter :
  Plane.Point K) : Plane.Point K :=
  Affine.midpoint vertex orthocenter

section
open Purelib.Geometry.Triangles.Circumcenter.Basic Purelib.Geometry.Triangles.Orthocenter.Basic
/-- Exercise 18.2's nine-point center, the midpoint of circumcenter and orthocenter. -/
def ninePointCenter (circumcenter orthocenter :
  Plane.Point K) : Plane.Point K :=
  Affine.midpoint circumcenter orthocenter

/-- The explicit circle used in Theorem 117. -/
def ninePointCircle
    [Nontrivial K]
    (circumcenter orthocenter : Plane.Point K) (circleQuadrance : K) : Conic K :=
  Conic.circleConic (ninePointCenter circumcenter orthocenter)
    circleQuadrance

end

/-- The bracket-numerator coordinate formula printed in Exercise 18.2. -/
def ninePointCenterFormula (first second third :
  Plane.Point K) : Plane.Point K :=
  let denominator := Fin3.antisymmetricTripleProduct
    first.x second.x third.x first.y second.y third.y
  ⟨(Formula.circumcenterXNumerator first second third +
      2 * Formula.orthocenterXNumerator first second third) / (4 * denominator),
    (Formula.circumcenterYNumerator first second third +
      2 * Formula.orthocenterYNumerator first second third) / (4 * denominator)⟩

/-- Exercise 18.2's coordinate calculation: the midpoint of the displayed circumcenter and orthocenter is exactly the
printed bracket formula. -/
theorem exercise_18_2_formula
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    ninePointCenter
        (Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear)
        (Orthocenter.Basic.orthocenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear) =
      ninePointCenterFormula first second third := by
  rw [Formula.circumcenter_formula first second third firstThirdDistinct
    secondThirdDistinct notCollinear twoNonzero]
  rw [Formula.orthocenter_formula first second third firstThirdDistinct
    secondThirdDistinct notCollinear]
  let denominator := Fin3.antisymmetricTripleProduct
    first.x second.x third.x first.y second.y third.y
  let circumcenterX := Formula.circumcenterXNumerator first second third
  let circumcenterY := Formula.circumcenterYNumerator first second third
  let orthocenterX := Formula.orthocenterXNumerator first second third
  let orthocenterY := Formula.orthocenterYNumerator first second third
  have denominatorEqualsDeterminant :
      denominator = Incidence.pointDeterminant first second third := by
    exact (Incidence.pointDeterminant_eq_antisymmetricTripleProduct
      first second third).symm
  have denominatorNonzero : denominator ≠ 0 := by
    rw [denominatorEqualsDeterminant]
    intro determinantZero
    apply notCollinear
    exact (Incidence.collinear_iff_pointDeterminant_eq_zero first second third).2
      determinantZero
  have twiceDenominatorNonzero : 2 * denominator ≠ 0 :=
    ExplicitField.mul_ne_zero twoNonzero denominatorNonzero
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero :=
      ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero
  have fourDenominatorNonzero : 4 * denominator ≠ 0 :=
    ExplicitField.mul_ne_zero fourNonzero denominatorNonzero
  apply Plane.Point.ext
  · change ((circumcenterX / (2 * denominator) +
          orthocenterX / denominator) / 2) =
        (circumcenterX + 2 * orthocenterX) / (4 * denominator)
    apply ExplicitField.eq_of_mul_eq_mul_right fourDenominatorNonzero
    calc
      ((circumcenterX / (2 * denominator) + orthocenterX / denominator) /
          2) * (4 * denominator) =
        (circumcenterX / (2 * denominator)) * (2 * denominator) +
          2 * ((orthocenterX / denominator) * denominator) := by
            simp only [ExplicitField.div_eq_mul_inv]
            have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
              ExplicitField.mul_inv_cancel 2 twoNonzero
            rw [show (4 : K) = 2 * 2 by ring1]
            calc
              (circumcenterX * (2 * denominator)⁻¹ +
                    orthocenterX * denominator⁻¹) * 2⁻¹ *
                  (2 * 2 * denominator) =
                (2 * 2⁻¹) *
                  (circumcenterX * (2 * denominator)⁻¹ *
                      (2 * denominator) +
                    2 * (orthocenterX * denominator⁻¹ * denominator)) := by
                      ring1
              _ = _ := by rw [twoCancel]; ring1
      _ = circumcenterX + 2 * orthocenterX := by
        rw [ExplicitField.div_mul_cancel circumcenterX
            twiceDenominatorNonzero,
          ExplicitField.div_mul_cancel orthocenterX denominatorNonzero]
      _ = ((circumcenterX + 2 * orthocenterX) / (4 * denominator)) *
          (4 * denominator) := by
        exact (ExplicitField.div_mul_cancel _
          fourDenominatorNonzero).symm
  · change ((circumcenterY / (2 * denominator) +
          orthocenterY / denominator) / 2) =
        (circumcenterY + 2 * orthocenterY) / (4 * denominator)
    apply ExplicitField.eq_of_mul_eq_mul_right fourDenominatorNonzero
    calc
      ((circumcenterY / (2 * denominator) + orthocenterY / denominator) /
          2) * (4 * denominator) =
        (circumcenterY / (2 * denominator)) * (2 * denominator) +
          2 * ((orthocenterY / denominator) * denominator) := by
            simp only [ExplicitField.div_eq_mul_inv]
            have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
              ExplicitField.mul_inv_cancel 2 twoNonzero
            rw [show (4 : K) = 2 * 2 by ring1]
            calc
              (circumcenterY * (2 * denominator)⁻¹ +
                    orthocenterY * denominator⁻¹) * 2⁻¹ *
                  (2 * 2 * denominator) =
                (2 * 2⁻¹) *
                  (circumcenterY * (2 * denominator)⁻¹ *
                      (2 * denominator) +
                    2 * (orthocenterY * denominator⁻¹ * denominator)) := by
                      ring1
              _ = _ := by rw [twoCancel]; ring1
      _ = circumcenterY + 2 * orthocenterY := by
        rw [ExplicitField.div_mul_cancel circumcenterY
            twiceDenominatorNonzero,
          ExplicitField.div_mul_cancel orthocenterY denominatorNonzero]
      _ = ((circumcenterY + 2 * orthocenterY) / (4 * denominator)) *
          (4 * denominator) := by
        exact (ExplicitField.div_mul_cancel _
          fourDenominatorNonzero).symm

open Purelib.Geometry.Triangles.Circumcenter.Basic Purelib.Geometry.Triangles.Orthocenter.Basic
/-- Exercise 18.2's deduction: the nine-point center is the midpoint of `OC`, hence is collinear with the two Euler-line
centers. -/
theorem exercise_18_2_center_on_euler_line
    [Nontrivial K] [DecidableEq K]
    (circumcenter orthocenter : Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0) :
    Incidence.Collinear circumcenter orthocenter
      (ninePointCenter circumcenter orthocenter) := by
  have weightsSum : (1 / 2 : K) + 1 / 2 = 1 := by
    apply ExplicitField.eq_of_mul_eq_mul_right twoNonzero
    calc
      ((1 / 2 : K) + 1 / 2) * 2 =
          (1 / 2 : K) * 2 + (1 / 2 : K) * 2 := by ring1
      _ = 1 + 1 := by
        rw [ExplicitField.div_mul_cancel 1 twoNonzero]
      _ = 1 * 2 := by ring1
  have result := Affine.collinear_affineCombination circumcenter orthocenter
    ((1 : K) / 2) ((1 : K) / 2) weightsSum
  have midpointEquals :
      Affine.affineCombination ((1 : K) / 2) circumcenter ((1 : K) / 2)
          orthocenter = ninePointCenter circumcenter orthocenter := by
    apply Plane.Point.ext <;>
      simp only [Affine.affineCombination, ninePointCenter, Affine.midpoint,
        ExplicitField.div_eq_mul_inv] <;> ring1
  rw [midpointEquals] at result
  exact result
/-- The midpoint pair belonging to one vertex has the common nine-point center and the expected endpoint quadrances. -/
theorem ninePoint_midpoint_pair
    [DecidableEq K]
    (vertex sideFirst sideSecond circumcenter orthocenter : Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (centerX : 2 * circumcenter.x + orthocenter.x =
      vertex.x + sideFirst.x + sideSecond.x)
    (centerY : 2 * circumcenter.y + orthocenter.y =
      vertex.y + sideFirst.y + sideSecond.y) :
    let sideMidpoint := Affine.midpoint sideFirst sideSecond
    let oppositeMidpoint := Affine.midpoint vertex orthocenter
    let center := ninePointCenter circumcenter orthocenter
    Affine.midpoint sideMidpoint oppositeMidpoint = center ∧
      Quadrance.quadrance center sideMidpoint = Quadrance.quadrance circumcenter vertex / 4 ∧
      Quadrance.quadrance center oppositeMidpoint = Quadrance.quadrance circumcenter vertex / 4 := by
  dsimp only [ninePointCenter]
  let sideMidpoint := Affine.midpoint sideFirst sideSecond
  let oppositeMidpoint := Affine.midpoint vertex orthocenter
  let center := Affine.midpoint circumcenter orthocenter
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero :=
      ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero
  have midpointSumX :
      sideMidpoint.x + oppositeMidpoint.x =
        circumcenter.x + orthocenter.x := by
    apply ExplicitField.eq_of_mul_eq_mul_right twoNonzero
    calc
      (sideMidpoint.x + oppositeMidpoint.x) * 2 =
          sideFirst.x + sideSecond.x + vertex.x + orthocenter.x := by
        change (((sideFirst.x + sideSecond.x) / 2) +
          ((vertex.x + orthocenter.x) / 2)) * 2 = _
        calc
          (((sideFirst.x + sideSecond.x) / 2) +
              ((vertex.x + orthocenter.x) / 2)) * 2 =
            ((sideFirst.x + sideSecond.x) / 2) * 2 +
              ((vertex.x + orthocenter.x) / 2) * 2 := by ring1
          _ = _ := by
            rw [ExplicitField.div_mul_cancel _ twoNonzero,
              ExplicitField.div_mul_cancel _ twoNonzero]
            ring1
      _ = (circumcenter.x + orthocenter.x) * 2 := by
        calc
          sideFirst.x + sideSecond.x + vertex.x + orthocenter.x =
              (vertex.x + sideFirst.x + sideSecond.x) + orthocenter.x := by
            ring1
          _ = (2 * circumcenter.x + orthocenter.x) + orthocenter.x := by
            rw [← centerX]
          _ = (circumcenter.x + orthocenter.x) * 2 := by ring1
  have midpointSumY :
      sideMidpoint.y + oppositeMidpoint.y =
        circumcenter.y + orthocenter.y := by
    apply ExplicitField.eq_of_mul_eq_mul_right twoNonzero
    calc
      (sideMidpoint.y + oppositeMidpoint.y) * 2 =
          sideFirst.y + sideSecond.y + vertex.y + orthocenter.y := by
        change (((sideFirst.y + sideSecond.y) / 2) +
          ((vertex.y + orthocenter.y) / 2)) * 2 = _
        calc
          (((sideFirst.y + sideSecond.y) / 2) +
              ((vertex.y + orthocenter.y) / 2)) * 2 =
            ((sideFirst.y + sideSecond.y) / 2) * 2 +
              ((vertex.y + orthocenter.y) / 2) * 2 := by ring1
          _ = _ := by
            rw [ExplicitField.div_mul_cancel _ twoNonzero,
              ExplicitField.div_mul_cancel _ twoNonzero]
            ring1
      _ = (circumcenter.y + orthocenter.y) * 2 := by
        calc
          sideFirst.y + sideSecond.y + vertex.y + orthocenter.y =
              (vertex.y + sideFirst.y + sideSecond.y) + orthocenter.y := by
            ring1
          _ = (2 * circumcenter.y + orthocenter.y) + orthocenter.y := by
            rw [← centerY]
          _ = (circumcenter.y + orthocenter.y) * 2 := by ring1
  have pairCenter : Affine.midpoint sideMidpoint oppositeMidpoint = center := by
    apply Plane.Point.ext
    · change (sideMidpoint.x + oppositeMidpoint.x) / 2 =
          (circumcenter.x + orthocenter.x) / 2
      rw [midpointSumX]
    · change (sideMidpoint.y + oppositeMidpoint.y) / 2 =
          (circumcenter.y + orthocenter.y) / 2
      rw [midpointSumY]
  have displacementX :
      sideMidpoint.x - oppositeMidpoint.x = circumcenter.x - vertex.x := by
    apply ExplicitField.eq_of_mul_eq_mul_right twoNonzero
    calc
      (sideMidpoint.x - oppositeMidpoint.x) * 2 =
          sideFirst.x + sideSecond.x - vertex.x - orthocenter.x := by
        change (((sideFirst.x + sideSecond.x) / 2) -
          ((vertex.x + orthocenter.x) / 2)) * 2 = _
        calc
          (((sideFirst.x + sideSecond.x) / 2) -
              ((vertex.x + orthocenter.x) / 2)) * 2 =
            ((sideFirst.x + sideSecond.x) / 2) * 2 -
              ((vertex.x + orthocenter.x) / 2) * 2 := by ring1
          _ = _ := by
            rw [ExplicitField.div_mul_cancel _ twoNonzero,
              ExplicitField.div_mul_cancel _ twoNonzero]
            ring1
      _ = (circumcenter.x - vertex.x) * 2 := by
        calc
          sideFirst.x + sideSecond.x - vertex.x - orthocenter.x =
              (vertex.x + sideFirst.x + sideSecond.x) -
                2 * vertex.x - orthocenter.x := by ring1
          _ = (2 * circumcenter.x + orthocenter.x) -
                2 * vertex.x - orthocenter.x := by rw [← centerX]
          _ = (circumcenter.x - vertex.x) * 2 := by ring1
  have displacementY :
      sideMidpoint.y - oppositeMidpoint.y = circumcenter.y - vertex.y := by
    apply ExplicitField.eq_of_mul_eq_mul_right twoNonzero
    calc
      (sideMidpoint.y - oppositeMidpoint.y) * 2 =
          sideFirst.y + sideSecond.y - vertex.y - orthocenter.y := by
        change (((sideFirst.y + sideSecond.y) / 2) -
          ((vertex.y + orthocenter.y) / 2)) * 2 = _
        calc
          (((sideFirst.y + sideSecond.y) / 2) -
              ((vertex.y + orthocenter.y) / 2)) * 2 =
            ((sideFirst.y + sideSecond.y) / 2) * 2 -
              ((vertex.y + orthocenter.y) / 2) * 2 := by ring1
          _ = _ := by
            rw [ExplicitField.div_mul_cancel _ twoNonzero,
              ExplicitField.div_mul_cancel _ twoNonzero]
            ring1
      _ = (circumcenter.y - vertex.y) * 2 := by
        calc
          sideFirst.y + sideSecond.y - vertex.y - orthocenter.y =
              (vertex.y + sideFirst.y + sideSecond.y) -
                2 * vertex.y - orthocenter.y := by ring1
          _ = (2 * circumcenter.y + orthocenter.y) -
                2 * vertex.y - orthocenter.y := by rw [← centerY]
          _ = (circumcenter.y - vertex.y) * 2 := by ring1
  have pairQuadrance :
      Quadrance.quadrance sideMidpoint oppositeMidpoint =
        Quadrance.quadrance circumcenter vertex := by
    unfold Quadrance.quadrance
    calc
      (oppositeMidpoint.x - sideMidpoint.x) ^ 2 +
          (oppositeMidpoint.y - sideMidpoint.y) ^ 2 =
        (sideMidpoint.x - oppositeMidpoint.x) ^ 2 +
          (sideMidpoint.y - oppositeMidpoint.y) ^ 2 := by ring1
      _ = (circumcenter.x - vertex.x) ^ 2 +
          (circumcenter.y - vertex.y) ^ 2 := by
        rw [displacementX, displacementY]
      _ = (vertex.x - circumcenter.x) ^ 2 +
          (vertex.y - circumcenter.y) ^ 2 := by ring1
  have sideQuadrance := Quadrance.midpoint_quadrance
    sideMidpoint oppositeMidpoint twoNonzero
  rw [pairCenter, pairQuadrance] at sideQuadrance
  have equalEndpointQuadrances := Quadrance.midpoint_equal_quadrance
    sideMidpoint oppositeMidpoint twoNonzero
  rw [pairCenter] at equalEndpointQuadrances
  exact ⟨pairCenter, sideQuadrance,
    equalEndpointQuadrances.symm.trans sideQuadrance⟩
/-- The altitude foot belonging to one vertex lies at the same nine-point quadrance as the corresponding side midpoint.
-/
theorem ninePoint_altitude_foot_quadrance
    [DecidableEq K]
    (vertex sideFirst sideSecond circumcenter orthocenter : Plane.Point K)
    (sideDistinct : sideFirst ≠ sideSecond)
    (twoNonzero : (2 : K) ≠ 0)
    (sideNonNull : ¬ (Incidence.lineThrough sideFirst sideSecond sideDistinct).IsNull)
    (centerX : 2 * circumcenter.x + orthocenter.x =
      vertex.x + sideFirst.x + sideSecond.x)
    (centerY : 2 * circumcenter.y + orthocenter.y =
      vertex.y + sideFirst.y + sideSecond.y)
    (orthocenterOnAltitude :
      (Construction.altitudeThrough vertex
        (Incidence.lineThrough sideFirst sideSecond sideDistinct)).Contains orthocenter) :
    let center := ninePointCenter circumcenter orthocenter
    let foot := Altitude.altitudeFoot vertex
      (Incidence.lineThrough sideFirst sideSecond sideDistinct) sideNonNull
    Quadrance.quadrance center foot = Quadrance.quadrance circumcenter vertex / 4 := by
  dsimp only
  let sideLine := Incidence.lineThrough sideFirst sideSecond sideDistinct
  let sideMidpoint := Affine.midpoint sideFirst sideSecond
  let oppositeMidpoint := Affine.midpoint vertex orthocenter
  let center := ninePointCenter circumcenter orthocenter
  let foot := Altitude.altitudeFoot vertex sideLine sideNonNull
  have pair := ninePoint_midpoint_pair vertex sideFirst sideSecond
    circumcenter orthocenter twoNonzero centerX centerY
  dsimp only at pair
  have sideMidpointOnLine : sideLine.Contains sideMidpoint :=
    Affine.line_contains_midpoint sideLine sideFirst sideSecond twoNonzero
      (Incidence.lineThrough_contains_first sideFirst sideSecond sideDistinct)
      (Incidence.lineThrough_contains_second sideFirst sideSecond sideDistinct)
  have footOnLine : sideLine.Contains foot := by
    exact Altitude.altitudeFoot_on_line vertex sideLine sideNonNull
  have oppositeMidpointOnAltitude :
      (Construction.altitudeThrough vertex sideLine).Contains oppositeMidpoint :=
    Affine.line_contains_midpoint (Construction.altitudeThrough vertex sideLine) vertex
      orthocenter twoNonzero (Construction.altitudeThrough_contains vertex sideLine)
      orthocenterOnAltitude
  have footOnAltitude :
      (Construction.altitudeThrough vertex sideLine).Contains foot := by
    exact Altitude.altitudeFoot_on_altitude vertex sideLine sideNonNull
  have rightAngle : Dot.pointVectorDot foot sideMidpoint oppositeMidpoint = 0 :=
    Altitude.pointVectorDot_eq_zero_of_line_altitude sideLine vertex sideMidpoint
      oppositeMidpoint foot sideNonNull sideMidpointOnLine footOnLine
      oppositeMidpointOnAltitude footOnAltitude
  have rightQuadrance := Circles.Diameter.Quadrance.midpoint_right_quadrance_of_dot_zero
    sideMidpoint oppositeMidpoint foot twoNonzero rightAngle
  rw [pair.1] at rightQuadrance
  exact rightQuadrance.symm.trans pair.2.1

/-- Theorem 117 (Nine point circle): for a non-null triangle, all three side midpoints, all three altitude feet, and all
three vertex--orthocenter midpoints lie on one explicitly constructed circle. -/
theorem nine_point_circle
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (firstSideNonNull :
      ¬ (Incidence.lineThrough second third secondThirdDistinct).IsNull)
    (secondSideNonNull :
      ¬ (Incidence.lineThrough first third firstThirdDistinct).IsNull)
    (thirdSideNonNull :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull) :
    let circumcenter :=
      Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear
    let orthocenter :=
      Orthocenter.Basic.orthocenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear
    let circleQuadrance := Quadrance.quadrance circumcenter first / 4
    let circle := ninePointCircle circumcenter orthocenter circleQuadrance
    circle.Contains (Medial.Basic.sideMidpointOppositeFirst first second third) ∧
      circle.Contains (Medial.Basic.sideMidpointOppositeSecond first second third) ∧
      circle.Contains (Medial.Basic.sideMidpointOppositeThird first second third) ∧
      circle.Contains (Altitude.altitudeFoot first
        (Incidence.lineThrough second third secondThirdDistinct) firstSideNonNull) ∧
      circle.Contains (Altitude.altitudeFoot second
        (Incidence.lineThrough first third firstThirdDistinct) secondSideNonNull) ∧
      circle.Contains (Altitude.altitudeFoot third
        (Incidence.lineThrough first second firstSecondDistinct) thirdSideNonNull) ∧
      circle.Contains (vertexOrthocenterMidpoint first orthocenter) ∧
      circle.Contains (vertexOrthocenterMidpoint second orthocenter) ∧
      circle.Contains (vertexOrthocenterMidpoint third orthocenter) := by
  dsimp only
  let circumcenter :=
    Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear
  let orthocenter :=
    Orthocenter.Basic.orthocenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear
  let center := ninePointCenter circumcenter orthocenter
  let circleQuadrance := Quadrance.quadrance circumcenter first / 4
  let circle := ninePointCircle circumcenter orthocenter circleQuadrance
  have clearedCenters := Centers.Euler.euler_center_cleared_coordinates first second third
    firstThirdDistinct secondThirdDistinct notCollinear twoNonzero
  have firstPair := ninePoint_midpoint_pair first second third circumcenter
    orthocenter twoNonzero clearedCenters.1 clearedCenters.2
  have secondCenterX : 2 * circumcenter.x + orthocenter.x =
      second.x + first.x + third.x := by
    rw [clearedCenters.1]
    ring1
  have secondCenterY : 2 * circumcenter.y + orthocenter.y =
      second.y + first.y + third.y := by
    rw [clearedCenters.2]
    ring1
  have secondPair := ninePoint_midpoint_pair second first third circumcenter
    orthocenter twoNonzero secondCenterX secondCenterY
  have thirdCenterX : 2 * circumcenter.x + orthocenter.x =
      third.x + first.x + second.x := by
    rw [clearedCenters.1]
    ring1
  have thirdCenterY : 2 * circumcenter.y + orthocenter.y =
      third.y + first.y + second.y := by
    rw [clearedCenters.2]
    ring1
  have thirdPair := ninePoint_midpoint_pair third first second circumcenter
    orthocenter twoNonzero thirdCenterX thirdCenterY
  dsimp only at firstPair secondPair thirdPair
  have centerFacts := Circumcenter.Basic.circumcenter first second third
    firstSecondDistinct firstThirdDistinct secondThirdDistinct notCollinear
    twoNonzero
  dsimp only at centerFacts
  have secondRadius : Quadrance.quadrance circumcenter second =
      Quadrance.quadrance circumcenter first := centerFacts.2.2.2.1.symm
  have thirdRadius : Quadrance.quadrance circumcenter third =
      Quadrance.quadrance circumcenter first :=
    centerFacts.2.2.2.2.symm.trans secondRadius
  have orthocenterFacts := Orthocenter.Basic.orthocenter first second third
    firstSecondDistinct firstThirdDistinct secondThirdDistinct notCollinear
  dsimp only at orthocenterFacts
  have firstFoot := ninePoint_altitude_foot_quadrance first second third
    circumcenter orthocenter secondThirdDistinct twoNonzero firstSideNonNull
    clearedCenters.1 clearedCenters.2 orthocenterFacts.1
  have secondFootRaw := ninePoint_altitude_foot_quadrance second first third
    circumcenter orthocenter firstThirdDistinct twoNonzero secondSideNonNull
    secondCenterX secondCenterY orthocenterFacts.2.1
  have secondFoot :
      Quadrance.quadrance center
          (Altitude.altitudeFoot second (Incidence.lineThrough first third firstThirdDistinct)
            secondSideNonNull) = circleQuadrance := by
    calc
      Quadrance.quadrance center
          (Altitude.altitudeFoot second (Incidence.lineThrough first third firstThirdDistinct)
            secondSideNonNull) = Quadrance.quadrance circumcenter second / 4 :=
        secondFootRaw
      _ = circleQuadrance := by rw [secondRadius]
  have thirdFootRaw := ninePoint_altitude_foot_quadrance third first second
    circumcenter orthocenter firstSecondDistinct twoNonzero thirdSideNonNull
    thirdCenterX thirdCenterY orthocenterFacts.2.2
  have thirdFoot :
      Quadrance.quadrance center
          (Altitude.altitudeFoot third (Incidence.lineThrough first second firstSecondDistinct)
            thirdSideNonNull) = circleQuadrance := by
    calc
      Quadrance.quadrance center
          (Altitude.altitudeFoot third (Incidence.lineThrough first second firstSecondDistinct)
            thirdSideNonNull) = Quadrance.quadrance circumcenter third / 4 :=
        thirdFootRaw
      _ = circleQuadrance := by rw [thirdRadius]
  have presentation := Conic.circleConic_isCirclePresentation
    center circleQuadrance
  have containsOfQuadrance := fun (point : Plane.Point K)
      (pointQuadrance : Quadrance.quadrance center point = circleQuadrance) =>
    (Conic.contains_iff_quadrance_eq circle center point circleQuadrance
      presentation).2 ((Quadrance.quadrance_symm point center).trans pointQuadrance)
  refine ⟨containsOfQuadrance _ firstPair.2.1,
    containsOfQuadrance _ (secondPair.2.1.trans (congrArg (fun value => value / 4)
      secondRadius)),
    containsOfQuadrance _ (thirdPair.2.1.trans (congrArg (fun value => value / 4)
      thirdRadius)),
    containsOfQuadrance _ firstFoot,
    containsOfQuadrance _ secondFoot,
    containsOfQuadrance _ thirdFoot,
    containsOfQuadrance _ firstPair.2.2,
    containsOfQuadrance _ (secondPair.2.2.trans (congrArg (fun value => value / 4)
      secondRadius)),
    containsOfQuadrance _ (thirdPair.2.2.trans (congrArg (fun value => value / 4)
      thirdRadius))⟩
end Purelib.Geometry.Triangles.NinePointCircle

end
