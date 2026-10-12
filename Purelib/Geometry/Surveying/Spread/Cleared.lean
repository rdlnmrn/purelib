module
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Ratio.Complement
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Trigonometry

open Purelib.Geometry.Trigonometry.Spread.Triple

section
@[expose] public section

/-!
# Divine Proportions, Chapter 24: surveying

Every construction is expressed by its finite quadrance/spread equations.
Decimal readings are retained as exact integer coefficient pairs, with
integer interval certificates for the source's numerical approximations.
-/

namespace Purelib.Geometry.Surveying.Spread.Cleared

section

variable {K : Type*} [ExplicitField K]

/-! ## Problems 17--19: heights -/

/-- Problem 17: the complementary Spread-law equation gives the vertical quadrance `Q=sP/(1-s)`. -/
theorem problem_17 (spread horizontalQuadrance verticalQuadrance : K)
    (complementNonzero : 1 - spread ≠ 0)
    (spreadLawCleared :
      verticalQuadrance * (1 - spread) = spread * horizontalQuadrance) :
    verticalQuadrance = spread * horizontalQuadrance / (1 - spread) := by
  apply ExplicitField.eq_of_mul_eq_mul_right complementNonzero
  calc
    verticalQuadrance * (1 - spread) =
        spread * horizontalQuadrance := spreadLawCleared
    _ = (spread * horizontalQuadrance / (1 - spread)) *
        (1 - spread) :=
      (ExplicitField.div_mul_cancel
        (spread * horizontalQuadrance) complementNonzero).symm

/-- Problem 18. Once a selected third spread satisfies the Triple-spread equation, two Spread-law steps give the
inaccessible height. -/
theorem problem_18
    (firstSpread secondSpread thirdSpread knownQuadrance
      slopingQuadrance verticalQuadrance : K)
    (thirdSpreadNonzero : thirdSpread ≠ 0)
    (_spreadTriple : TripleSpread.SpreadTriple firstSpread secondSpread thirdSpread)
    (firstSpreadLaw :
      thirdSpread * slopingQuadrance = firstSpread * knownQuadrance)
    (rightTriangle : verticalQuadrance = secondSpread * slopingQuadrance) :
    verticalQuadrance =
      firstSpread * secondSpread * knownQuadrance / thirdSpread := by
  apply ExplicitField.eq_of_mul_eq_mul_right thirdSpreadNonzero
  calc
    verticalQuadrance * thirdSpread =
        secondSpread * (thirdSpread * slopingQuadrance) := by
          rw [rightTriangle]
          ring1
    _ = secondSpread * (firstSpread * knownQuadrance) := by
      rw [firstSpreadLaw]
    _ = (firstSpread * secondSpread * knownQuadrance / thirdSpread) *
        thirdSpread := by
      rw [ExplicitField.div_mul_cancel
        (firstSpread * secondSpread * knownQuadrance) thirdSpreadNonzero]
      ring1

/-- Problem 19's two right-triangle substitutions and the final collinear quad triple, all with their denominators
cleared. -/
theorem problem_19
    (firstSpread secondSpread thirdSpread lowerSpread knownQuadrance
      slopingQuadrance upperHeight lowerHeight totalHeight : K)
    (firstSpreadLaw :
      thirdSpread * slopingQuadrance = firstSpread * knownQuadrance)
    (upperRightTriangle : upperHeight = secondSpread * slopingQuadrance)
    (horizontalRightTriangle :
      lowerSpread * (1 - secondSpread) * slopingQuadrance =
        (1 - lowerSpread) * lowerHeight)
    (heightQuadTriple : Geometry.Trigonometry.QuadTriple totalHeight lowerHeight upperHeight) :
    thirdSpread * upperHeight =
        firstSpread * secondSpread * knownQuadrance ∧
      thirdSpread * (1 - lowerSpread) * lowerHeight =
        firstSpread * (1 - secondSpread) * lowerSpread * knownQuadrance ∧
      Geometry.Trigonometry.QuadTriple totalHeight lowerHeight upperHeight := by
  constructor
  · calc
      thirdSpread * upperHeight =
          secondSpread * (thirdSpread * slopingQuadrance) := by
            rw [upperRightTriangle]
            ring1
      _ = secondSpread * (firstSpread * knownQuadrance) := by
        rw [firstSpreadLaw]
      _ = firstSpread * secondSpread * knownQuadrance := by ring1
  constructor
  · calc
      thirdSpread * (1 - lowerSpread) * lowerHeight =
          thirdSpread * ((1 - lowerSpread) * lowerHeight) := by ring1
      _ = thirdSpread *
          (lowerSpread * (1 - secondSpread) * slopingQuadrance) := by
            rw [← horizontalRightTriangle]
      _ = thirdSpread * lowerSpread * (1 - secondSpread) *
          slopingQuadrance := by ring1
      _ = lowerSpread * (1 - secondSpread) *
          (thirdSpread * slopingQuadrance) := by ring1
      _ = firstSpread * (1 - secondSpread) * lowerSpread *
          knownQuadrance := by rw [firstSpreadLaw]; ring1
  · exact heightQuadTriple

/-! ## Problem 20: Regiomontanus' problem -/

/-- The rational window-spread expression `Q * P / ((P + Q₁) * (P + Q₂))`. -/
def regiomontanusSpread (P Q Q₁ Q₂ : K) : K :=
  Q * P / ((P + Q₁) * (P + Q₂))

/-- The reduced window-spread denominator `Q₁ + Q₂ + P + Q₁Q₂/P`. -/
def regiomontanusReducedDenominator (P Q₁ Q₂ : K) : K :=
  Q₁ + Q₂ + P + Q₁ * Q₂ / P

/-- The two displayed forms of the window spread are equal. -/
theorem regiomontanus_spread_rewrite
    (P Q Q₁ Q₂ : K)
    (PNonzero : P ≠ 0)
    (firstDenominatorNonzero : (P + Q₁) * (P + Q₂) ≠ 0)
    (secondDenominatorNonzero :
      regiomontanusReducedDenominator P Q₁ Q₂ ≠ 0) :
    regiomontanusSpread P Q Q₁ Q₂ =
      Q / regiomontanusReducedDenominator P Q₁ Q₂ := by
  unfold regiomontanusSpread
  apply Ratio.ratio_eq_of_cross_product firstDenominatorNonzero
    secondDenominatorNonzero
  unfold regiomontanusReducedDenominator
  have quotientCancel :=
    ExplicitField.div_mul_cancel (Q₁ * Q₂) PNonzero
  calc
    (Q * P) * (Q₁ + Q₂ + P + Q₁ * Q₂ / P) =
        Q * ((P + Q₁) * (P + Q₂)) +
          Q * ((Q₁ * Q₂ / P) * P - Q₁ * Q₂) := by ring1
    _ = Q * ((P + Q₁) * (P + Q₂)) := by
      rw [quotientCancel]
      ring1

/-- Problem 21: substituting the three right-triangle height formulas into Stewart's relation gives the printed
quadratic equation for `H`. -/
theorem problem_21
    (P₁ P₂ H r₁ r₂ r₃ Q₁ Q₂ P₃ : K)
    (r₁Nonzero : r₁ ≠ 0) (r₂Nonzero : r₂ ≠ 0)
    (r₃Nonzero : r₃ ≠ 0)
    (Q₂Value : Q₂ = (1 - r₁) * H / r₁)
    (Q₁Value : Q₁ = (1 - r₂) * H / r₂)
    (P₃Value : P₃ = (1 - r₃) * H / r₃)
    (stewartRelation :
      P₂ * (P₃ + P₁ - Q₂) ^ 2 =
        P₁ * (P₃ + P₂ - Q₁) ^ 2) :
    P₂ * (H * (1 / r₃ - 1 / r₁) + P₁) ^ 2 =
      P₁ * (H * (1 / r₃ - 1 / r₂) + P₂) ^ 2 := by
  rw [P₃Value, Q₂Value, Q₁Value] at stewartRelation
  rw [Ratio.Complement.scaled_complement_div r₁ H r₁Nonzero,
    Ratio.Complement.scaled_complement_div r₂ H r₂Nonzero,
    Ratio.Complement.scaled_complement_div r₃ H r₃Nonzero] at stewartRelation
  calc
    P₂ * (H * (1 / r₃ - 1 / r₁) + P₁) ^ 2 =
        P₂ * ((1 / r₃ - 1) * H + P₁ -
          (1 / r₁ - 1) * H) ^ 2 := by ring1
    _ = P₁ * ((1 / r₃ - 1) * H + P₂ -
          (1 / r₂ - 1) * H) ^ 2 := stewartRelation
    _ = P₁ * (H * (1 / r₃ - 1 / r₂) + P₂) ^ 2 := by
      ring1

/-- Problem 22's denominator-free vertical/horizontal spread relation. -/
theorem problem_22_cleared
    (s₁ s₂ r₁ r₂ Q₁ Q₂ H : K)
    (HNonzero : H ≠ 0)
    (horizontalSpreadLaw : s₁ * Q₂ = s₂ * Q₁)
    (firstVertical : r₁ * Q₂ = (1 - r₁) * H)
    (secondVertical : r₂ * Q₁ = (1 - r₂) * H) :
    s₁ * (1 - r₁) * r₂ = s₂ * (1 - r₂) * r₁ := by
  apply ExplicitField.eq_of_mul_eq_mul_right HNonzero
  calc
    (s₁ * (1 - r₁) * r₂) * H =
        s₁ * (r₁ * Q₂) * r₂ := by rw [firstVertical]; ring1
    _ = (s₁ * Q₂) * r₁ * r₂ := by ring1
    _ = (s₂ * Q₁) * r₁ * r₂ := by rw [horizontalSpreadLaw]
    _ = s₂ * (r₂ * Q₁) * r₁ := by ring1
    _ = (s₂ * (1 - r₂) * r₁) * H := by rw [secondVertical]; ring1

/-- Problem 22's final displayed quotient form. -/
theorem problem_22
    (s₁ s₂ r₁ r₂ : K)
    (r₁Nonzero : r₁ ≠ 0) (r₂Nonzero : r₂ ≠ 0)
    (cleared :
      s₁ * (1 - r₁) * r₂ = s₂ * (1 - r₂) * r₁) :
    s₁ / r₁ - s₂ / r₂ = s₁ - s₂ := by
  have productNonzero : r₁ * r₂ ≠ 0 :=
    ExplicitField.mul_ne_zero r₁Nonzero r₂Nonzero
  apply ExplicitField.eq_of_mul_eq_mul_right productNonzero
  have firstTerm : (s₁ / r₁) * (r₁ * r₂) = s₁ * r₂ := by
    calc
      (s₁ / r₁) * (r₁ * r₂) =
          ((s₁ / r₁) * r₁) * r₂ := by ring1
      _ = s₁ * r₂ := by
        rw [ExplicitField.div_mul_cancel s₁ r₁Nonzero]
  have secondTerm : (s₂ / r₂) * (r₁ * r₂) = s₂ * r₁ := by
    calc
      (s₂ / r₂) * (r₁ * r₂) =
          ((s₂ / r₂) * r₂) * r₁ := by ring1
      _ = s₂ * r₁ := by
        rw [ExplicitField.div_mul_cancel s₂ r₂Nonzero]
  calc
    (s₁ / r₁ - s₂ / r₂) * (r₁ * r₂) =
        (s₁ / r₁) * (r₁ * r₂) -
          (s₂ / r₂) * (r₁ * r₂) := by ring1
    _ = s₁ * r₂ - s₂ * r₁ := by rw [firstTerm, secondTerm]
    _ =
        (s₁ - s₂) * (r₁ * r₂) +
          (s₁ * (1 - r₁) * r₂ -
            s₂ * (1 - r₂) * r₁) := by ring1
    _ = (s₁ - s₂) * (r₁ * r₂) := by rw [cleared]; ring1

/-- Problem 23: the Cross law over a horizontal right triangle yields `1-s=r₁r₂`. -/
theorem problem_23
    (Q₁ Q₂ H spread r₁ r₂ : K)
    (firstTotalNonzero : Q₁ + H ≠ 0)
    (secondTotalNonzero : Q₂ + H ≠ 0)
    (crossLawCleared :
      4 * H ^ 2 = 4 * (Q₁ + H) * (Q₂ + H) * (1 - spread))
    (firstVertical : r₁ * (Q₂ + H) = H)
    (secondVertical : r₂ * (Q₁ + H) = H)
    (fourNonzero : (4 : K) ≠ 0) :
    1 - spread = r₁ * r₂ := by
  have denominatorNonzero :
      4 * ((Q₁ + H) * (Q₂ + H)) ≠ 0 :=
    ExplicitField.mul_ne_zero fourNonzero
      (ExplicitField.mul_ne_zero firstTotalNonzero secondTotalNonzero)
  have verticalProduct :
      (r₁ * r₂) * ((Q₁ + H) * (Q₂ + H)) = H ^ 2 := by
    calc
      (r₁ * r₂) * ((Q₁ + H) * (Q₂ + H)) =
          (r₂ * (Q₁ + H)) * (r₁ * (Q₂ + H)) := by ring1
      _ = H * H := by rw [firstVertical, secondVertical]
      _ = H ^ 2 := by ring1
  apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
  calc
    (1 - spread) * (4 * ((Q₁ + H) * (Q₂ + H))) =
        4 * (Q₁ + H) * (Q₂ + H) * (1 - spread) := by ring1
    _ = 4 * H ^ 2 := crossLawCleared.symm
    _ = (r₁ * r₂) * (4 * ((Q₁ + H) * (Q₂ + H))) := by
      rw [show (r₁ * r₂) *
          (4 * ((Q₁ + H) * (Q₂ + H))) =
        4 * ((r₁ * r₂) * ((Q₁ + H) * (Q₂ + H))) by ring1,
        verticalProduct]
end
end Purelib.Geometry.Surveying.Spread.Cleared

end
