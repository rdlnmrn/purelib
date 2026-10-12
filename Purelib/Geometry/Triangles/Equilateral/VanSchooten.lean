module
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Circles.Concyclic.Determinant
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Quadrea.Basic
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic

import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
public import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

open Purelib.Geometry.Trigonometry

/-!
# Divine Proportions, Exercise 16.4: Van Schooten's theorem

The proof is entirely denominator-free until its final cancellation of the
equilateral triangle's nonzero common quadrance.  Concyclicity supplies one
finite determinant equation, and two-dimensional determinant identities turn
its square into Archimedes' quad-triple polynomial.
-/

@[expose] public section

namespace Purelib.Geometry.Triangles.Equilateral.VanSchooten

open Purelib.Algebra

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Conic

/-- The squared circle residual from the equilateral Gram identities.

The six scalar observations remain abstract while the three retained identities resolve their products.
-/
private theorem determinantSquare_of_gram_identities
    (q r u v a d : K)
    (radial : d ^ 2 = r * q - (u - v) ^ 2)
    (cross : 2 * a * d = -q * (u + v))
    (side : 4 * a ^ 2 = 3 * q ^ 2) :
    4 * (q * d - r * a) ^ 2 =
      q ^ 2 * (3 * r ^ 2 + 4 * r * (u + v) + 4 * r * q - 4 * (u - v) ^ 2) := by
  calc
    4 * (q * d - r * a) ^ 2 =
        4 * q ^ 2 * d ^ 2 - 4 * q * r * (2 * a * d) + r ^ 2 * (4 * a ^ 2) := by ring1
    _ = 4 * q ^ 2 * (r * q - (u - v) ^ 2) -
        4 * q * r * (-q * (u + v)) + r ^ 2 * (3 * q ^ 2) := by rw [radial, cross, side]
    _ = _ := by ring1

/-- Archimedes' polynomial in a retained radial norm and the two radial dot products. -/
private theorem archimedes_radial_formula (q r u v : K) :
    QuadTriple.Basic.archimedesFunction r (r + 2 * u + q) (r + 2 * v + q) =
      3 * r ^ 2 + 4 * r * (u + v) + 4 * r * q - 4 * (u - v) ^ 2 := by
  unfold QuadTriple.Basic.archimedesFunction
  ring1

/-- Exercise 16.4 (Van Schooten): the three quadrances from a point on the circumcircle of an equilateral triangle form
a quad triple. -/
theorem exercise_16_4 [Nontrivial K] [DecidableEq K]
    (circle : Conic K) (center : Plane.Point K) (circleQuadrance : K)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (first second third point : Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (secondThirdQuadrance :
      Quadrance.quadrance second third = Quadrance.quadrance first second)
    (firstThirdQuadrance :
      Quadrance.quadrance first third = Quadrance.quadrance first second)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second)
    (thirdOnCircle : circle.Contains third)
    (pointOnCircle : circle.Contains point) :
    Trigonometry.QuadTriple (Quadrance.quadrance first point) (Quadrance.quadrance second point)
      (Quadrance.quadrance third point) := by
  let commonQuadrance := Quadrance.quadrance first second
  let radialX := first.x - point.x
  let radialY := first.y - point.y
  let secondSideX := second.x - first.x
  let secondSideY := second.y - first.y
  let thirdSideX := third.x - first.x
  let thirdSideY := third.y - first.y
  let radialSquare := radialX ^ 2 + radialY ^ 2
  let secondDot := radialX * secondSideX + radialY * secondSideY
  let thirdDot := radialX * thirdSideX + radialY * thirdSideY
  let sideDot := secondSideX * thirdSideX + secondSideY * thirdSideY
  let sideDeterminant :=
    secondSideX * thirdSideY - secondSideY * thirdSideX
  let radialDeterminantDifference :=
    (radialX * secondSideY - radialY * secondSideX) -
      (radialX * thirdSideY - radialY * thirdSideX)
  have commonQuadranceNonzero : commonQuadrance ≠ 0 := by
    intro commonZero
    have triangleQuadreaNonzero :=
      (Quadrea.Basic.quadrea_ne_zero_iff_not_collinear first second third twoNonzero).2
        notCollinear
    apply triangleQuadreaNonzero
    unfold Quadrea.Basic.quadrea
    rw [secondThirdQuadrance, firstThirdQuadrance]
    change QuadTriple.Basic.archimedesFunction commonQuadrance commonQuadrance
      commonQuadrance = 0
    rw [commonZero]
    unfold QuadTriple.Basic.archimedesFunction
    ring1
  have firstRadialFormula :
      Quadrance.quadrance first point = radialSquare := by
    unfold radialSquare radialX radialY Quadrance.quadrance
    ring1
  have secondRadialFormula :
      Quadrance.quadrance second point =
        radialSquare + 2 * secondDot + commonQuadrance := by
    unfold radialSquare secondDot radialX radialY secondSideX secondSideY
      commonQuadrance Quadrance.quadrance
    ring1
  have thirdRadialFormula :
      Quadrance.quadrance third point =
        radialSquare + 2 * thirdDot + commonQuadrance := by
    calc
      Quadrance.quadrance third point =
          radialSquare + 2 * thirdDot + Quadrance.quadrance first third := by
        unfold radialSquare thirdDot radialX radialY thirdSideX thirdSideY
          Quadrance.quadrance
        ring1
      _ = radialSquare + 2 * thirdDot + commonQuadrance := by
        rw [firstThirdQuadrance]
  have secondSideNorm :
      secondSideX ^ 2 + secondSideY ^ 2 = commonQuadrance := by
    unfold secondSideX secondSideY commonQuadrance Quadrance.quadrance
    ring1
  have thirdSideNorm :
      thirdSideX ^ 2 + thirdSideY ^ 2 = commonQuadrance := by
    calc
      thirdSideX ^ 2 + thirdSideY ^ 2 =
          Quadrance.quadrance first third := by
        unfold thirdSideX thirdSideY Quadrance.quadrance
        ring1
      _ = commonQuadrance := firstThirdQuadrance
  have sideDifferenceNorm :
      (secondSideX - thirdSideX) ^ 2 +
          (secondSideY - thirdSideY) ^ 2 = commonQuadrance := by
    calc
      (secondSideX - thirdSideX) ^ 2 +
          (secondSideY - thirdSideY) ^ 2 =
          Quadrance.quadrance second third := by
        unfold secondSideX thirdSideX secondSideY thirdSideY Quadrance.quadrance
        ring1
      _ = commonQuadrance := secondThirdQuadrance
  have twoSideDot : 2 * sideDot = commonQuadrance := by
    calc
      2 * sideDot =
          (secondSideX ^ 2 + secondSideY ^ 2) +
            (thirdSideX ^ 2 + thirdSideY ^ 2) -
            ((secondSideX - thirdSideX) ^ 2 +
              (secondSideY - thirdSideY) ^ 2) := by
        unfold sideDot
        ring1
      _ = commonQuadrance + commonQuadrance - commonQuadrance := by
        rw [secondSideNorm, thirdSideNorm, sideDifferenceNorm]
      _ = commonQuadrance := by ring1
  have radialDeterminantSquare :
      radialDeterminantDifference ^ 2 +
          (secondDot - thirdDot) ^ 2 =
        radialSquare * commonQuadrance := by
    calc
      radialDeterminantDifference ^ 2 +
          (secondDot - thirdDot) ^ 2 =
          radialSquare *
            ((secondSideX - thirdSideX) ^ 2 +
              (secondSideY - thirdSideY) ^ 2) := by
        unfold radialDeterminantDifference secondDot thirdDot radialSquare
        ring1
      _ = radialSquare * commonQuadrance := by
        rw [sideDifferenceNorm]
  have radialDeterminantSquareResolved :
      radialDeterminantDifference ^ 2 =
        radialSquare * commonQuadrance -
          (secondDot - thirdDot) ^ 2 := by
    calc
      radialDeterminantDifference ^ 2 =
          (radialDeterminantDifference ^ 2 +
            (secondDot - thirdDot) ^ 2) -
            (secondDot - thirdDot) ^ 2 := by ring1
      _ = radialSquare * commonQuadrance -
          (secondDot - thirdDot) ^ 2 := by
        rw [radialDeterminantSquare]
  have determinantCrossGeneral :
      sideDeterminant * radialDeterminantDifference =
        secondDot * sideDot -
          (secondSideX ^ 2 + secondSideY ^ 2) * thirdDot -
          (secondDot * (thirdSideX ^ 2 + thirdSideY ^ 2) -
            sideDot * thirdDot) := by
    unfold sideDeterminant radialDeterminantDifference secondDot thirdDot
      sideDot
    ring1
  have twiceDeterminantCross :
      2 * sideDeterminant * radialDeterminantDifference =
        -commonQuadrance * (secondDot + thirdDot) := by
    calc
      2 * sideDeterminant * radialDeterminantDifference =
          2 * (sideDeterminant * radialDeterminantDifference) := by ring1
      _ =
          2 * (secondDot * sideDot -
            (secondSideX ^ 2 + secondSideY ^ 2) * thirdDot -
            (secondDot * (thirdSideX ^ 2 + thirdSideY ^ 2) -
              sideDot * thirdDot)) := by
        rw [determinantCrossGeneral]
      _ = secondDot * (2 * sideDot) -
          (2 * (secondSideX ^ 2 + secondSideY ^ 2)) * thirdDot -
          secondDot * (2 * (thirdSideX ^ 2 + thirdSideY ^ 2)) +
          (2 * sideDot) * thirdDot := by ring1
      _ = -commonQuadrance * (secondDot + thirdDot) := by
        rw [twoSideDot, secondSideNorm, thirdSideNorm]
        ring1
  have sideDeterminantSquare :
      4 * sideDeterminant ^ 2 = 3 * commonQuadrance ^ 2 := by
    calc
      4 * sideDeterminant ^ 2 =
          4 * (secondSideX ^ 2 + secondSideY ^ 2) *
            (thirdSideX ^ 2 + thirdSideY ^ 2) -
            (2 * sideDot) ^ 2 := by
        unfold sideDeterminant sideDot
        ring1
      _ = 3 * commonQuadrance ^ 2 := by
        rw [secondSideNorm, thirdSideNorm, twoSideDot]
        ring1
  have circleDeterminantZero :=
    Conic.fourPointCircleDeterminant_eq_zero circle center circleQuadrance
      presentation first second third point firstOnCircle secondOnCircle
      thirdOnCircle pointOnCircle
  have circleDeterminantFormula :
      Conic.fourPointCircleDeterminant first second third point =
        commonQuadrance * radialDeterminantDifference -
          radialSquare * sideDeterminant := by
    unfold Conic.fourPointCircleDeterminant
    rw [firstRadialFormula, secondRadialFormula, thirdRadialFormula]
    unfold Incidence.pointDeterminant radialDeterminantDifference sideDeterminant
      radialSquare secondDot thirdDot radialX radialY secondSideX secondSideY
      thirdSideX thirdSideY
    ring1
  have archimedesFormula :
      QuadTriple.Basic.archimedesFunction (Quadrance.quadrance first point) (Quadrance.quadrance second point)
          (Quadrance.quadrance third point) =
        3 * radialSquare ^ 2 +
          4 * radialSquare * (secondDot + thirdDot) +
          4 * radialSquare * commonQuadrance -
          4 * (secondDot - thirdDot) ^ 2 := by
    rw [firstRadialFormula, secondRadialFormula, thirdRadialFormula]
    exact archimedes_radial_formula commonQuadrance radialSquare secondDot thirdDot
  have determinantSquareFormula :
      4 * (commonQuadrance * radialDeterminantDifference -
          radialSquare * sideDeterminant) ^ 2 =
        commonQuadrance ^ 2 *
          (3 * radialSquare ^ 2 +
            4 * radialSquare * (secondDot + thirdDot) +
            4 * radialSquare * commonQuadrance -
            4 * (secondDot - thirdDot) ^ 2) :=
    determinantSquare_of_gram_identities commonQuadrance radialSquare secondDot thirdDot
      sideDeterminant radialDeterminantDifference radialDeterminantSquareResolved
      twiceDeterminantCross sideDeterminantSquare
  have commonQuadranceSquareNonzero : commonQuadrance ^ 2 ≠ 0 := by
    have productNonzero := Algebra.Field.ExplicitField.mul_ne_zero
      commonQuadranceNonzero commonQuadranceNonzero
    intro squareZero
    apply productNonzero
    calc
      commonQuadrance * commonQuadrance = commonQuadrance ^ 2 := by ring1
      _ = 0 := squareZero
  unfold Trigonometry.QuadTriple
  have clearedTriple :
      commonQuadrance ^ 2 *
          QuadTriple.Basic.archimedesFunction (Quadrance.quadrance first point) (Quadrance.quadrance second point)
            (Quadrance.quadrance third point) = 0 := by
    calc
      commonQuadrance ^ 2 *
          QuadTriple.Basic.archimedesFunction (Quadrance.quadrance first point) (Quadrance.quadrance second point)
            (Quadrance.quadrance third point) =
          commonQuadrance ^ 2 *
            (3 * radialSquare ^ 2 +
              4 * radialSquare * (secondDot + thirdDot) +
              4 * radialSquare * commonQuadrance -
              4 * (secondDot - thirdDot) ^ 2) := by
        rw [archimedesFormula]
      _ = 4 * (commonQuadrance * radialDeterminantDifference -
          radialSquare * sideDeterminant) ^ 2 :=
        determinantSquareFormula.symm
      _ = 4 *
          (Conic.fourPointCircleDeterminant first second third point) ^ 2 := by
        rw [circleDeterminantFormula]
      _ = 0 := by rw [circleDeterminantZero]; ring1
  by_cases tripleZero :
      QuadTriple.Basic.archimedesFunction (Quadrance.quadrance first point) (Quadrance.quadrance second point)
        (Quadrance.quadrance third point) = 0
  · exact tripleZero
  · exact False.elim
      ((Algebra.Field.ExplicitField.mul_ne_zero commonQuadranceSquareNonzero tripleZero)
        clearedTriple)

end Conic

end Purelib.Geometry.Triangles.Equilateral.VanSchooten

end
