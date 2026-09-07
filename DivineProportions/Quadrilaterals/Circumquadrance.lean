import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Quadrilaterals.CyclicSpreads
import DivineProportions.Trigonometry.Quadrea

/-!
# Divine Proportions, Theorem 111: quadrilateral circumquadrance

The three printed coefficient polynomials are stored literally.  The proof
keeps the book's substitution `Q_ij = 4*K*r_ij`, but avoids its division and
later cancellation: one homogeneous polynomial identity shows directly that
the requested quadratic is `256*K^6` times the Quadruple-spread relation.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Quadrilateral

/-- The coefficient `p`, the Quadruple-quad function of the four side
quadrances. -/
def circumquadranceCoefficientP (q₁₂ q₂₃ q₃₄ q₁₄ : K) : K :=
  quadrupleQuadFunction q₁₂ q₂₃ q₃₄ q₁₄

/-- The coefficient `q` in Theorem 111, in the source's three-term form. -/
def circumquadranceCoefficientQ (q₁₂ q₂₃ q₃₄ q₁₄ : K) : K :=
  (q₁₂ * q₁₄ - q₂₃ * q₃₄) *
      (q₂₃ * q₁₄ - q₁₂ * q₃₄) *
      (q₁₂ + q₂₃ - q₃₄ - q₁₄) +
    (q₁₂ * q₁₄ - q₂₃ * q₃₄) *
      (q₃₄ * q₁₄ - q₁₂ * q₂₃) *
      (q₁₂ - q₂₃ + q₃₄ - q₁₄) +
    (q₁₂ * q₂₃ - q₃₄ * q₁₄) *
      (q₂₃ * q₁₄ - q₁₂ * q₃₄) *
      (q₁₂ - q₂₃ - q₃₄ + q₁₄)

/-- The coefficient `r` in Theorem 111. -/
def circumquadranceCoefficientR (q₁₂ q₂₃ q₃₄ q₁₄ : K) : K :=
  (q₁₂ * q₁₄ - q₂₃ * q₃₄) *
    (q₂₃ * q₁₄ - q₁₂ * q₃₄) *
    (q₁₂ * q₂₃ - q₃₄ * q₁₄)

/-- The homogeneous substitution identity behind Theorem 111. -/
theorem circumquadrance_polynomial_scaled_spread
    (r₁₂ r₂₃ r₃₄ r₁₄ circleQuadrance : K) :
    circumquadranceCoefficientP
          (4 * circleQuadrance * r₁₂) (4 * circleQuadrance * r₂₃)
          (4 * circleQuadrance * r₃₄) (4 * circleQuadrance * r₁₄) *
        circleQuadrance ^ 2 -
      2 * circumquadranceCoefficientQ
          (4 * circleQuadrance * r₁₂) (4 * circleQuadrance * r₂₃)
          (4 * circleQuadrance * r₃₄) (4 * circleQuadrance * r₁₄) *
        circleQuadrance +
      circumquadranceCoefficientR
          (4 * circleQuadrance * r₁₂) (4 * circleQuadrance * r₂₃)
          (4 * circleQuadrance * r₃₄) (4 * circleQuadrance * r₁₄) =
    256 * circleQuadrance ^ 6 *
      quadrupleSpreadFunction r₁₂ r₂₃ r₃₄ r₁₄ := by
  unfold circumquadranceCoefficientP circumquadranceCoefficientQ
    circumquadranceCoefficientR quadrupleQuadFunction
    quadrupleSpreadFunction quadrupleSpreadCore
  ring1

/-- Scalar form of Theorem 111.  Cleared relations `Q_ij=4*K*r_ij` and the
Quadruple-spread equation imply the requested circumquadrance polynomial;
neither division nor cancellation is required. -/
theorem quadrilateral_circumquadrance_of_scaled_spreads
    (q₁₂ q₂₃ q₃₄ q₁₄ r₁₂ r₂₃ r₃₄ r₁₄ circleQuadrance : K)
    (firstScaled : q₁₂ = 4 * circleQuadrance * r₁₂)
    (secondScaled : q₂₃ = 4 * circleQuadrance * r₂₃)
    (thirdScaled : q₃₄ = 4 * circleQuadrance * r₃₄)
    (fourthScaled : q₁₄ = 4 * circleQuadrance * r₁₄)
    (spreadRelation :
      quadrupleSpreadFunction r₁₂ r₂₃ r₃₄ r₁₄ = 0) :
    circumquadranceCoefficientP q₁₂ q₂₃ q₃₄ q₁₄ *
        circleQuadrance ^ 2 -
      2 * circumquadranceCoefficientQ q₁₂ q₂₃ q₃₄ q₁₄ *
        circleQuadrance +
      circumquadranceCoefficientR q₁₂ q₂₃ q₃₄ q₁₄ = 0 := by
  rw [firstScaled, secondScaled, thirdScaled, fourthScaled,
    circumquadrance_polynomial_scaled_spread, spreadRelation]
  ring1

/-- Theorem 111 (Quadrilateral circumquadrance), specialized to the four side
quadrances of an explicit cyclic quadrilateral on a non-null circle. -/
theorem quadrilateral_circumquadrance
    [Nontrivial K] [DecidableEq K]
    (quadrilateral : Quadrilateral K)
    (circle : Conic K) (center : Point K) (circleQuadrance : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (firstOnCircle : circle.Contains quadrilateral.first)
    (secondOnCircle : circle.Contains quadrilateral.second)
    (thirdOnCircle : circle.Contains quadrilateral.third)
    (fourthOnCircle : circle.Contains quadrilateral.fourth) :
    let q₁₂ := quadrance quadrilateral.first quadrilateral.second
    let q₂₃ := quadrance quadrilateral.second quadrilateral.third
    let q₃₄ := quadrance quadrilateral.third quadrilateral.fourth
    let q₁₄ := quadrance quadrilateral.first quadrilateral.fourth
    circumquadranceCoefficientP q₁₂ q₂₃ q₃₄ q₁₄ *
        circleQuadrance ^ 2 -
      2 * circumquadranceCoefficientQ q₁₂ q₂₃ q₃₄ q₁₄ *
        circleQuadrance +
      circumquadranceCoefficientR q₁₂ q₂₃ q₃₄ q₁₄ = 0 := by
  dsimp only
  let spreads := normalizedCyclicSubtendedSpreads quadrilateral circle center
    circleQuadrance twoNonzero quadranceNonzero presentation firstOnCircle
    secondOnCircle thirdOnCircle fourthOnCircle
  have spreadRelation :
      quadrupleSpreadFunction spreads.r₁₂ spreads.r₂₃ spreads.r₃₄
        spreads.r₁₄ = 0 :=
    (cyclic_quadrilateral_spreads spreads twoNonzero).1
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    intro fourZero
    apply productNonzero
    calc
      (2 : K) * 2 = 4 := by ring1
      _ = 0 := fourZero
  have scaleNonzero : 4 * circleQuadrance ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero fourNonzero quadranceNonzero
  have firstScaled :
      quadrance quadrilateral.first quadrilateral.second =
        4 * circleQuadrance * spreads.r₁₂ := by
    change quadrance quadrilateral.first quadrilateral.second =
      4 * circleQuadrance *
        (quadrance quadrilateral.first quadrilateral.second /
          (4 * circleQuadrance))
    calc
      quadrance quadrilateral.first quadrilateral.second =
          (quadrance quadrilateral.first quadrilateral.second /
            (4 * circleQuadrance)) * (4 * circleQuadrance) :=
        (RFAP.ExplicitField.div_mul_cancel _ scaleNonzero).symm
      _ = 4 * circleQuadrance *
          (quadrance quadrilateral.first quadrilateral.second /
            (4 * circleQuadrance)) := by ring1
  have secondScaled :
      quadrance quadrilateral.second quadrilateral.third =
        4 * circleQuadrance * spreads.r₂₃ := by
    change quadrance quadrilateral.second quadrilateral.third =
      4 * circleQuadrance *
        (quadrance quadrilateral.second quadrilateral.third /
          (4 * circleQuadrance))
    calc
      quadrance quadrilateral.second quadrilateral.third =
          (quadrance quadrilateral.second quadrilateral.third /
            (4 * circleQuadrance)) * (4 * circleQuadrance) :=
        (RFAP.ExplicitField.div_mul_cancel _ scaleNonzero).symm
      _ = 4 * circleQuadrance *
          (quadrance quadrilateral.second quadrilateral.third /
            (4 * circleQuadrance)) := by ring1
  have thirdScaled :
      quadrance quadrilateral.third quadrilateral.fourth =
        4 * circleQuadrance * spreads.r₃₄ := by
    change quadrance quadrilateral.third quadrilateral.fourth =
      4 * circleQuadrance *
        (quadrance quadrilateral.third quadrilateral.fourth /
          (4 * circleQuadrance))
    calc
      quadrance quadrilateral.third quadrilateral.fourth =
          (quadrance quadrilateral.third quadrilateral.fourth /
            (4 * circleQuadrance)) * (4 * circleQuadrance) :=
        (RFAP.ExplicitField.div_mul_cancel _ scaleNonzero).symm
      _ = 4 * circleQuadrance *
          (quadrance quadrilateral.third quadrilateral.fourth /
            (4 * circleQuadrance)) := by ring1
  have fourthScaled :
      quadrance quadrilateral.first quadrilateral.fourth =
        4 * circleQuadrance * spreads.r₁₄ := by
    change quadrance quadrilateral.first quadrilateral.fourth =
      4 * circleQuadrance *
        (quadrance quadrilateral.first quadrilateral.fourth /
          (4 * circleQuadrance))
    calc
      quadrance quadrilateral.first quadrilateral.fourth =
          (quadrance quadrilateral.first quadrilateral.fourth /
            (4 * circleQuadrance)) * (4 * circleQuadrance) :=
        (RFAP.ExplicitField.div_mul_cancel _ scaleNonzero).symm
      _ = 4 * circleQuadrance *
          (quadrance quadrilateral.first quadrilateral.fourth /
            (4 * circleQuadrance)) := by ring1
  exact quadrilateral_circumquadrance_of_scaled_spreads
    (quadrance quadrilateral.first quadrilateral.second)
    (quadrance quadrilateral.second quadrilateral.third)
    (quadrance quadrilateral.third quadrilateral.fourth)
    (quadrance quadrilateral.first quadrilateral.fourth)
    spreads.r₁₂ spreads.r₂₃ spreads.r₃₄ spreads.r₁₄ circleQuadrance
    firstScaled secondScaled thirdScaled fourthScaled spreadRelation

/-- Exercise 17.1: the discriminant of the circumquadrance quadratic factors
into the four side quadrances and the three printed squared linear factors. -/
theorem exercise_17_1 (q₁₂ q₂₃ q₃₄ q₁₄ : K) :
    (2 * circumquadranceCoefficientQ q₁₂ q₂₃ q₃₄ q₁₄) ^ 2 -
        4 * circumquadranceCoefficientP q₁₂ q₂₃ q₃₄ q₁₄ *
          circumquadranceCoefficientR q₁₂ q₂₃ q₃₄ q₁₄ =
      4 * q₁₂ * q₂₃ * q₃₄ * q₁₄ *
        (q₁₂ + q₂₃ - q₃₄ - q₁₄) ^ 2 *
        (q₁₂ - q₂₃ + q₃₄ - q₁₄) ^ 2 *
        (q₁₂ - q₂₃ - q₃₄ + q₁₄) ^ 2 := by
  unfold circumquadranceCoefficientP circumquadranceCoefficientQ
    circumquadranceCoefficientR quadrupleQuadFunction
  ring1

end Quadrilateral

end DivineProportions
