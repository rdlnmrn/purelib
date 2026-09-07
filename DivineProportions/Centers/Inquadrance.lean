import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Centers.IncenterSpread

/-!
# Divine Proportions, §12.5: inquadrance

First we expose the common point-to-side quadrance implied by two concurrent
vertex bisectors.  The numerical theorem is then the source proof with every
division cleared: Spread law, the double-spread relation at the third vertex,
and Extended spread law leave one visible factor `1-u₃`, which is cancelled
only in the printed theorem.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- A point on bisectors at two vertices has the same quadrance to all three
triangle side lines. -/
theorem incenter_common_inquadrance
    [Nontrivial K] [DecidableEq K]
    (firstSide secondSide thirdSide : Line K)
    (firstSideNonNull : ¬ firstSide.IsNull)
    (secondSideNonNull : ¬ secondSide.IsNull)
    (thirdSideNonNull : ¬ thirdSide.IsNull)
    (firstVertexNonparallel : ¬ thirdSide.Parallel secondSide)
    (secondVertexNonparallel : ¬ thirdSide.Parallel firstSide)
    (firstBisector secondBisector : Line K)
    (isFirstBisector :
      IsVertexBisector thirdSide secondSide firstBisector
        thirdSideNonNull secondSideNonNull firstVertexNonparallel)
    (isSecondBisector :
      IsVertexBisector thirdSide firstSide secondBisector
        thirdSideNonNull firstSideNonNull secondVertexNonparallel)
    (center : Point K)
    (centerOnFirst : firstBisector.Contains center)
    (centerOnSecond : secondBisector.Contains center) :
    pointLineQuadrance center firstSide firstSideNonNull =
        pointLineQuadrance center secondSide secondSideNonNull ∧
      pointLineQuadrance center secondSide secondSideNonNull =
        pointLineQuadrance center thirdSide thirdSideNonNull := by
  have equalThirdSecond :=
    equal_pointLineQuadrance_of_isVertexBisector_contains
      thirdSide secondSide firstBisector thirdSideNonNull secondSideNonNull
      firstVertexNonparallel isFirstBisector center centerOnFirst
  have equalThirdFirst :=
    equal_pointLineQuadrance_of_isVertexBisector_contains
      thirdSide firstSide secondBisector thirdSideNonNull firstSideNonNull
      secondVertexNonparallel isSecondBisector center centerOnSecond
  exact ⟨equalThirdFirst.symm.trans equalThirdSecond,
    equalThirdSecond.symm⟩

private theorem cancel_right_nonzero
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by rw [mul_one]
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel, mul_one]

/-- The denominator-free calculation behind Theorem 90. -/
theorem inquadrance_cleared
    (u₁ u₂ u₃ q₃ s₃ circumquadranceValue
      secondVertexQuadrance inquadranceValue : K)
    (inquadranceFromSpread :
      inquadranceValue = u₂ * secondVertexQuadrance)
    (spreadLawCleared :
      secondVertexQuadrance * (1 - u₃) = u₁ * q₃)
    (bisectedThirdSpread : s₃ = 4 * u₃ * (1 - u₃))
    (extendedSpreadCleared :
      q₃ = 4 * circumquadranceValue * s₃) :
    inquadranceValue * (1 - u₃) =
      (16 * circumquadranceValue * u₁ * u₂ * u₃) * (1 - u₃) := by
  calc
    inquadranceValue * (1 - u₃) =
        u₂ * (secondVertexQuadrance * (1 - u₃)) := by
          rw [inquadranceFromSpread]
          ring1
    _ = u₂ * (u₁ * q₃) := by rw [spreadLawCleared]
    _ = u₂ * (u₁ * (4 * circumquadranceValue * s₃)) := by
      rw [extendedSpreadCleared]
    _ = u₂ *
        (u₁ * (4 * circumquadranceValue *
          (4 * u₃ * (1 - u₃)))) := by rw [bisectedThirdSpread]
    _ = (16 * circumquadranceValue * u₁ * u₂ * u₃) *
        (1 - u₃) := by ring1

/-- Theorem 90 (Inquadrance), in the exact printed form
`R = 16K u₁u₂u₃`.  Its hypotheses are precisely the four displayed steps in
the source proof. -/
theorem inquadrance
    [Nontrivial K]
    (u₁ u₂ u₃ q₃ s₃ circumquadranceValue
      secondVertexQuadrance inquadranceValue : K)
    (oneMinusThirdNonzero : 1 - u₃ ≠ 0)
    (thirdSpreadNonzero : s₃ ≠ 0)
    (inquadranceFromSpread :
      inquadranceValue = u₂ * secondVertexQuadrance)
    (spreadLaw :
      secondVertexQuadrance = u₁ * q₃ / (1 - u₃))
    (bisectedThirdSpread : s₃ = 4 * u₃ * (1 - u₃))
    (extendedSpread :
      q₃ / s₃ = 4 * circumquadranceValue) :
    inquadranceValue = 16 * circumquadranceValue * u₁ * u₂ * u₃ := by
  have spreadLawCleared :
      secondVertexQuadrance * (1 - u₃) = u₁ * q₃ := by
    calc
      secondVertexQuadrance * (1 - u₃) =
          (u₁ * q₃ / (1 - u₃)) * (1 - u₃) := by rw [spreadLaw]
      _ = u₁ * q₃ :=
        RFAP.ExplicitField.div_mul_cancel _ oneMinusThirdNonzero
  have extendedSpreadCleared :
      q₃ = 4 * circumquadranceValue * s₃ := by
    calc
      q₃ = (q₃ / s₃) * s₃ := by
        rw [RFAP.ExplicitField.div_mul_cancel q₃ thirdSpreadNonzero]
      _ = (4 * circumquadranceValue) * s₃ := by rw [extendedSpread]
  apply cancel_right_nonzero oneMinusThirdNonzero
  exact inquadrance_cleared u₁ u₂ u₃ q₃ s₃ circumquadranceValue
    secondVertexQuadrance inquadranceValue inquadranceFromSpread
    spreadLawCleared bisectedThirdSpread extendedSpreadCleared

end DivineProportions
