import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Circles.EqualProducts
import DivineProportions.Trigonometry.Quadrea

/-!
# Divine Proportions, Exercise 16.4: Van Schooten's theorem

The proof is entirely denominator-free until its final cancellation of the
equilateral triangle's nonzero common quadrance.  Concyclicity supplies one
finite determinant equation, and two-dimensional determinant identities turn
its square into Archimedes' quad-triple polynomial.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

/-- Exercise 16.4 (Van Schooten): the three quadrances from a point on the
circumcircle of an equilateral triangle form a quad triple. -/
theorem exercise_16_4 [Nontrivial K] [DecidableEq K]
    (circle : Conic K) (center : Point K) (circleQuadrance : K)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (first second third point : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (notCollinear : ¬ Collinear first second third)
    (secondThirdQuadrance :
      quadrance second third = quadrance first second)
    (firstThirdQuadrance :
      quadrance first third = quadrance first second)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second)
    (thirdOnCircle : circle.Contains third)
    (pointOnCircle : circle.Contains point) :
    QuadTriple (quadrance first point) (quadrance second point)
      (quadrance third point) := by
  let commonQuadrance := quadrance first second
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
      (quadrea_ne_zero_iff_not_collinear first second third twoNonzero).2
        notCollinear
    apply triangleQuadreaNonzero
    unfold quadrea
    rw [secondThirdQuadrance, firstThirdQuadrance]
    change archimedesFunction commonQuadrance commonQuadrance
      commonQuadrance = 0
    rw [commonZero]
    unfold archimedesFunction
    ring1
  have firstRadialFormula :
      quadrance first point = radialSquare := by
    unfold radialSquare radialX radialY quadrance
    ring1
  have secondRadialFormula :
      quadrance second point =
        radialSquare + 2 * secondDot + commonQuadrance := by
    unfold radialSquare secondDot radialX radialY secondSideX secondSideY
      commonQuadrance quadrance
    ring1
  have thirdRadialFormula :
      quadrance third point =
        radialSquare + 2 * thirdDot + commonQuadrance := by
    calc
      quadrance third point =
          radialSquare + 2 * thirdDot + quadrance first third := by
        unfold radialSquare thirdDot radialX radialY thirdSideX thirdSideY
          quadrance
        ring1
      _ = radialSquare + 2 * thirdDot + commonQuadrance := by
        rw [firstThirdQuadrance]
  have secondSideNorm :
      secondSideX ^ 2 + secondSideY ^ 2 = commonQuadrance := by
    unfold secondSideX secondSideY commonQuadrance quadrance
    ring1
  have thirdSideNorm :
      thirdSideX ^ 2 + thirdSideY ^ 2 = commonQuadrance := by
    calc
      thirdSideX ^ 2 + thirdSideY ^ 2 =
          quadrance first third := by
        unfold thirdSideX thirdSideY quadrance
        ring1
      _ = commonQuadrance := firstThirdQuadrance
  have sideDifferenceNorm :
      (secondSideX - thirdSideX) ^ 2 +
          (secondSideY - thirdSideY) ^ 2 = commonQuadrance := by
    calc
      (secondSideX - thirdSideX) ^ 2 +
          (secondSideY - thirdSideY) ^ 2 =
          quadrance second third := by
        unfold secondSideX thirdSideX secondSideY thirdSideY quadrance
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
    fourPointCircleDeterminant_eq_zero circle center circleQuadrance
      presentation first second third point firstOnCircle secondOnCircle
      thirdOnCircle pointOnCircle
  have circleDeterminantFormula :
      fourPointCircleDeterminant first second third point =
        commonQuadrance * radialDeterminantDifference -
          radialSquare * sideDeterminant := by
    unfold fourPointCircleDeterminant
    rw [firstRadialFormula, secondRadialFormula, thirdRadialFormula]
    unfold pointDeterminant radialDeterminantDifference sideDeterminant
      radialSquare secondDot thirdDot radialX radialY secondSideX secondSideY
      thirdSideX thirdSideY
    ring1
  have archimedesFormula :
      archimedesFunction (quadrance first point) (quadrance second point)
          (quadrance third point) =
        3 * radialSquare ^ 2 +
          4 * radialSquare * (secondDot + thirdDot) +
          4 * radialSquare * commonQuadrance -
          4 * (secondDot - thirdDot) ^ 2 := by
    rw [firstRadialFormula, secondRadialFormula, thirdRadialFormula]
    unfold archimedesFunction
    ring1
  have determinantSquareFormula :
      4 * (commonQuadrance * radialDeterminantDifference -
          radialSquare * sideDeterminant) ^ 2 =
        commonQuadrance ^ 2 *
          (3 * radialSquare ^ 2 +
            4 * radialSquare * (secondDot + thirdDot) +
            4 * radialSquare * commonQuadrance -
            4 * (secondDot - thirdDot) ^ 2) := by
    calc
      4 * (commonQuadrance * radialDeterminantDifference -
          radialSquare * sideDeterminant) ^ 2 =
          4 * commonQuadrance ^ 2 * radialDeterminantDifference ^ 2 -
            4 * commonQuadrance * radialSquare *
              (2 * sideDeterminant * radialDeterminantDifference) +
            radialSquare ^ 2 * (4 * sideDeterminant ^ 2) := by ring1
      _ = 4 * commonQuadrance ^ 2 *
            (radialSquare * commonQuadrance -
              (secondDot - thirdDot) ^ 2) -
          4 * commonQuadrance * radialSquare *
            (-commonQuadrance * (secondDot + thirdDot)) +
          radialSquare ^ 2 * (3 * commonQuadrance ^ 2) := by
        rw [radialDeterminantSquareResolved, twiceDeterminantCross,
          sideDeterminantSquare]
      _ = commonQuadrance ^ 2 *
          (3 * radialSquare ^ 2 +
            4 * radialSquare * (secondDot + thirdDot) +
            4 * radialSquare * commonQuadrance -
            4 * (secondDot - thirdDot) ^ 2) := by ring1
  have commonQuadranceSquareNonzero : commonQuadrance ^ 2 ≠ 0 := by
    have productNonzero := RFAP.ExplicitField.mul_ne_zero
      commonQuadranceNonzero commonQuadranceNonzero
    intro squareZero
    apply productNonzero
    calc
      commonQuadrance * commonQuadrance = commonQuadrance ^ 2 := by ring1
      _ = 0 := squareZero
  unfold QuadTriple
  have clearedTriple :
      commonQuadrance ^ 2 *
          archimedesFunction (quadrance first point) (quadrance second point)
            (quadrance third point) = 0 := by
    calc
      commonQuadrance ^ 2 *
          archimedesFunction (quadrance first point) (quadrance second point)
            (quadrance third point) =
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
          (fourPointCircleDeterminant first second third point) ^ 2 := by
        rw [circleDeterminantFormula]
      _ = 0 := by rw [circleDeterminantZero]; ring1
  by_cases tripleZero :
      archimedesFunction (quadrance first point) (quadrance second point)
        (quadrance third point) = 0
  · exact tripleZero
  · exact False.elim
      ((RFAP.ExplicitField.mul_ne_zero commonQuadranceSquareNonzero tripleZero)
        clearedTriple)

end Conic

end DivineProportions
