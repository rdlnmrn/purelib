module
public import Purelib.Geometry.Trigonometry.QuadTriple.Quadruple
public import Purelib.Geometry.Trigonometry.Spread.Quadruple

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Nat.Order
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open scoped Purelib.Data.Nat

open Purelib

open Purelib.Geometry.Trigonometry.QuadTriple

open Purelib.Geometry.Trigonometry.Spread

section
@[expose] public section

/-!
# Divine Proportions, Theorem 111: quadrilateral circumquadrance

The three printed coefficient polynomials are stored literally.  The proof
keeps the book's substitution `Q_ij = 4*K*r_ij`, but avoids its division and
later cancellation: one homogeneous polynomial identity shows directly that
the requested quadratic is `256*K^6` times the Quadruple-spread relation.
-/

namespace Purelib.Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial

open Purelib.Algebra

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Quadrilateral

/-- The coefficient `p`, the Quadruple-quad function of the four side quadrances. -/
def circumquadranceCoefficientP
  (q₁₂ q₂₃ q₃₄ q₁₄ : K) : K :=
  Quadruple.quadrupleQuadFunction q₁₂ q₂₃ q₃₄ q₁₄

/-- The middle coefficient of the cyclic quadrilateral circumquadrance polynomial.

It is the sum of three products of opposite-side quadrance differences and signed side-quadrance sums. -/
def circumquadranceCoefficientQ
  (q₁₂ q₂₃ q₃₄ q₁₄ : K) : K :=
  (q₁₂ * q₁₄ - q₂₃ * q₃₄) *
      (q₂₃ * q₁₄ - q₁₂ * q₃₄) *
      (q₁₂ + q₂₃ - q₃₄ - q₁₄) +
    (q₁₂ * q₁₄ - q₂₃ * q₃₄) *
      (q₃₄ * q₁₄ - q₁₂ * q₂₃) *
      (q₁₂ - q₂₃ + q₃₄ - q₁₄) +
    (q₁₂ * q₂₃ - q₃₄ * q₁₄) *
      (q₂₃ * q₁₄ - q₁₂ * q₃₄) *
      (q₁₂ - q₂₃ - q₃₄ + q₁₄)

/-- The constant coefficient of the cyclic quadrilateral circumquadrance polynomial.

It is the product of the three displayed differences of side-quadrance products. -/
def circumquadranceCoefficientR
  (q₁₂ q₂₃ q₃₄ q₁₄ : K) : K :=
  (q₁₂ * q₁₄ - q₂₃ * q₃₄) *
    (q₂₃ * q₁₄ - q₁₂ * q₃₄) *
    (q₁₂ * q₂₃ - q₃₄ * q₁₄)

/-- Substituting four scaled spreads gives the quadruple-spread polynomial times its homogeneous scale.

Each side quadrance is `4` times the displayed circle quadrance and its
spread. The resulting polynomial equals the quadruple-spread relation
multiplied by `256` and the sixth power of the circle quadrance. -/
theorem
  circumquadrance_polynomial_scaled_spread
    (r₁₂ r₂₃ r₃₄ r₁₄ circleQuadrance : K) :
    Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientP
          (4 * circleQuadrance * r₁₂) (4 * circleQuadrance * r₂₃)
          (4 * circleQuadrance * r₃₄) (4 * circleQuadrance * r₁₄) *
        circleQuadrance ^ 2 -
      2 * Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientQ
          (4 * circleQuadrance * r₁₂) (4 * circleQuadrance * r₂₃)
          (4 * circleQuadrance * r₃₄) (4 * circleQuadrance * r₁₄) *
        circleQuadrance +
      Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientR
          (4 * circleQuadrance * r₁₂) (4 * circleQuadrance * r₂₃)
          (4 * circleQuadrance * r₃₄) (4 * circleQuadrance * r₁₄) =
    256 * circleQuadrance ^ 6 *
      Quadruple.quadrupleSpreadFunction r₁₂ r₂₃ r₃₄ r₁₄ := by
  unfold Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientP
    Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientQ
    Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientR
      Quadruple.quadrupleQuadFunction
    Quadruple.quadrupleSpreadFunction Quadruple.quadrupleSpreadCore
  ring1

/-- Four scaled side quadrances satisfying the quadruple-spread relation satisfy the circumquadrance polynomial.

The displayed equations `Q_ij=4*K*r_ij` identify the quadrances with the
retained spreads and circle quadrance. Substitution gives the quadratic
relation without an additional nonzero or characteristic hypothesis. -/
theorem
  quadrilateral_circumquadrance_of_scaled_spreads
    (q₁₂ q₂₃ q₃₄ q₁₄ r₁₂ r₂₃ r₃₄ r₁₄ circleQuadrance : K)
    (firstScaled : q₁₂ = 4 * circleQuadrance * r₁₂)
    (secondScaled : q₂₃ = 4 * circleQuadrance * r₂₃)
    (thirdScaled : q₃₄ = 4 * circleQuadrance * r₃₄)
    (fourthScaled : q₁₄ = 4 * circleQuadrance * r₁₄)
    (spreadRelation :
      Quadruple.quadrupleSpreadFunction r₁₂ r₂₃ r₃₄ r₁₄ = 0) :
    Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientP q₁₂ q₂₃ q₃₄ q₁₄
      *
        circleQuadrance ^ 2 -
      2 * Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientQ q₁₂ q₂₃
        q₃₄ q₁₄ *
        circleQuadrance +
      Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientR q₁₂ q₂₃ q₃₄
        q₁₄ = 0 := by
  rw [firstScaled, secondScaled, thirdScaled, fourthScaled,
    Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadrance_polynomial_scaled_spread,
      spreadRelation]
  ring1

/-- The circumquadrance discriminant factors into the side quadrances and squared signed sums.

The difference of the squared middle coefficient and four times the other
two coefficients equals four times the product of the side quadrances and
three explicit signed-sum squares. The identity holds over the displayed field. -/
theorem exercise_17_1 (q₁₂ q₂₃
  q₃₄ q₁₄ : K) :
    (2 * Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientQ q₁₂ q₂₃ q₃₄
      q₁₄) ^ 2 -
        4 * Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientP q₁₂ q₂₃
          q₃₄ q₁₄ *
          Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientR q₁₂ q₂₃
            q₃₄ q₁₄ =
      4 * q₁₂ * q₂₃ * q₃₄ * q₁₄ *
        (q₁₂ + q₂₃ - q₃₄ - q₁₄) ^ 2 *
        (q₁₂ - q₂₃ + q₃₄ - q₁₄) ^ 2 *
        (q₁₂ - q₂₃ - q₃₄ + q₁₄) ^ 2 := by
  unfold Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientP
    Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientQ
    Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientR
      Quadruple.quadrupleQuadFunction
  ring1

end Quadrilateral

end Purelib.Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial

end
