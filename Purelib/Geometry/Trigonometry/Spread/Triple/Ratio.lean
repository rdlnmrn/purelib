module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Squares
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Trigonometry.Spread

open Purelib.Geometry.Trigonometry.Spread.Triple

section
@[expose] public section

/-!
# Divine Proportions, Chapter 7: the triple spread formula

The proof is performed directly on the six finite line coefficients.  A
single explicit common denominator replaces the book's auxiliary triangle,
and every cancellation is witnessed by the three non-null hypotheses.
-/

namespace Purelib.Geometry.Trigonometry.Spread.Triple.Ratio

variable {K : Type*} [ExplicitField K]

/-- The normal-form calculation at the heart of Theorem 48. -/
theorem spread_from_ratio_normal_form
    (s₁ s₂ s₃ ratio : K)
    (s₂Nonzero : s₂ ≠ 0)
    (triple : TripleSpread.SpreadTriple s₁ s₂ s₃)
    (givenRatio : s₁ / s₂ = ratio) :
    (s₃ / s₂ - ratio - 1) ^ 2 = 4 * ratio * (1 - s₃) := by
  have firstEquation : s₁ = ratio * s₂ := by
    calc
      s₁ = (s₁ / s₂) * s₂ :=
        (ExplicitField.div_mul_cancel s₁ s₂Nonzero).symm
      _ = ratio * s₂ := by rw [givenRatio]
  have tripleForm := (Triple.exercise_7_6 triple).2.2.2.1
  let normalized := s₃ / s₂ - ratio - 1
  have scaledNormalized : normalized * s₂ = s₃ - s₁ - s₂ := by
    unfold normalized
    calc
      (s₃ / s₂ - ratio - 1) * s₂ =
          (s₃ / s₂) * s₂ - ratio * s₂ - s₂ := by ring1
      _ = s₃ - s₁ - s₂ := by
        rw [ExplicitField.div_mul_cancel s₃ s₂Nonzero, firstEquation]
  have s₂SquareNonzero : s₂ ^ 2 ≠ 0 := by
    simpa [pow_two] using
      (ExplicitField.mul_ne_zero s₂Nonzero s₂Nonzero)
  change normalized ^ 2 = 4 * ratio * (1 - s₃)
  apply ExplicitField.eq_of_mul_eq_mul_right s₂SquareNonzero
  calc
    normalized ^ 2 * s₂ ^ 2 = (normalized * s₂) ^ 2 := by ring1
    _ = (s₃ - s₁ - s₂) ^ 2 := by rw [scaledNormalized]
    _ = 4 * s₁ * s₂ * (1 - s₃) := tripleForm
    _ = (4 * ratio * (1 - s₃)) * s₂ ^ 2 := by
      rw [firstEquation]
      ring1

/-- Theorem 48, square clause: the proof computes the root rather than selecting it. -/
theorem spread_from_ratio_square
    (s₁ s₂ s₃ ratio : K)
    (twoNonzero : (2 : K) ≠ 0)
    (s₂Nonzero : s₂ ≠ 0)
    (triple : TripleSpread.SpreadTriple s₁ s₂ s₃)
    (givenRatio : s₁ / s₂ = ratio) :
    Squares.IsSquare (ratio * (1 - s₃)) := by
  let normalized := s₃ / s₂ - ratio - 1
  have normalForm : normalized ^ 2 = 4 * ratio * (1 - s₃) :=
    spread_from_ratio_normal_form s₁ s₂ s₃ ratio s₂Nonzero triple givenRatio
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero := ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  refine ⟨normalized / 2, ?_⟩
  apply ExplicitField.eq_of_mul_eq_mul_right fourNonzero
  calc
    (ratio * (1 - s₃)) * 4 = normalized ^ 2 := by
      rw [normalForm]
      ring1
    _ = ((normalized / 2) * 2) ^ 2 := by
      rw [ExplicitField.div_mul_cancel normalized twoNonzero]
    _ = (normalized / 2) ^ 2 * 4 := by ring1

/-- Theorem 48, explicit `±` clause. Each branch also records that its displayed denominator is nonzero. -/
theorem spread_from_ratio_alternatives [DecidableEq K]
    (s₁ s₂ s₃ ratio root : K)
    (s₂Nonzero : s₂ ≠ 0) (s₃Nonzero : s₃ ≠ 0)
    (triple : TripleSpread.SpreadTriple s₁ s₂ s₃)
    (givenRatio : s₁ / s₂ = ratio)
    (rootEquation : ratio * (1 - s₃) = root ^ 2) :
    ((ratio + 1 + 2 * root ≠ 0) ∧
        s₂ = s₃ / (ratio + 1 + 2 * root)) ∨
      ((ratio + 1 - 2 * root ≠ 0) ∧
        s₂ = s₃ / (ratio + 1 - 2 * root)) := by
  let normalized := s₃ / s₂ - ratio - 1
  have normalForm : normalized ^ 2 = 4 * ratio * (1 - s₃) :=
    spread_from_ratio_normal_form s₁ s₂ s₃ ratio s₂Nonzero triple givenRatio
  have squareEquation : normalized ^ 2 = (2 * root) ^ 2 := by
    calc
      normalized ^ 2 = 4 * ratio * (1 - s₃) := normalForm
      _ = 4 * (ratio * (1 - s₃)) := by ring1
      _ = 4 * root ^ 2 := by rw [rootEquation]
      _ = (2 * root) ^ 2 := by ring1
  have factorProduct :
      (normalized - 2 * root) * (normalized + 2 * root) = 0 := by
    calc
      (normalized - 2 * root) * (normalized + 2 * root) =
          normalized ^ 2 - (2 * root) ^ 2 := by ring1
      _ = 0 := by rw [squareEquation]; ring1
  have quotientNonzero : s₃ / s₂ ≠ 0 :=
    ExplicitField.div_ne_zero s₃Nonzero s₂Nonzero
  by_cases positiveFactorZero : normalized - 2 * root = 0
  · left
    have denominatorEquation : ratio + 1 + 2 * root = s₃ / s₂ := by
      unfold normalized at positiveFactorZero
      calc
        ratio + 1 + 2 * root =
            s₃ / s₂ - (s₃ / s₂ - ratio - 1 - 2 * root) := by ring1
        _ = s₃ / s₂ := by rw [positiveFactorZero]; ring1
    have denominatorNonzero : ratio + 1 + 2 * root ≠ 0 := by
      rw [denominatorEquation]
      exact quotientNonzero
    refine ⟨denominatorNonzero, ?_⟩
    apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
    calc
      s₂ * (ratio + 1 + 2 * root) = s₂ * (s₃ / s₂) := by
        rw [denominatorEquation]
      _ = (s₃ / s₂) * s₂ := by ring1
      _ = s₃ := ExplicitField.div_mul_cancel s₃ s₂Nonzero
      _ = (s₃ / (ratio + 1 + 2 * root)) *
          (ratio + 1 + 2 * root) :=
        (ExplicitField.div_mul_cancel s₃ denominatorNonzero).symm
  · right
    have negativeFactorZero : normalized + 2 * root = 0 := by
      by_cases factorZero : normalized + 2 * root = 0
      · exact factorZero
      · exact False.elim
          ((ExplicitField.mul_ne_zero positiveFactorZero factorZero)
            factorProduct)
    have denominatorEquation : ratio + 1 - 2 * root = s₃ / s₂ := by
      unfold normalized at negativeFactorZero
      calc
        ratio + 1 - 2 * root =
            s₃ / s₂ - (s₃ / s₂ - ratio - 1 + 2 * root) := by ring1
        _ = s₃ / s₂ := by rw [negativeFactorZero]; ring1
    have denominatorNonzero : ratio + 1 - 2 * root ≠ 0 := by
      rw [denominatorEquation]
      exact quotientNonzero
    refine ⟨denominatorNonzero, ?_⟩
    apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
    calc
      s₂ * (ratio + 1 - 2 * root) = s₂ * (s₃ / s₂) := by
        rw [denominatorEquation]
      _ = (s₃ / s₂) * s₂ := by ring1
      _ = s₃ := ExplicitField.div_mul_cancel s₃ s₂Nonzero
      _ = (s₃ / (ratio + 1 - 2 * root)) *
          (ratio + 1 - 2 * root) :=
        (ExplicitField.div_mul_cancel s₃ denominatorNonzero).symm

/-- Theorem 48 (Spread from ratio), packaged exactly as the square conclusion followed by the formula for any supplied
square root. -/
theorem spread_from_ratio [DecidableEq K]
    (s₁ s₂ s₃ ratio : K)
    (twoNonzero : (2 : K) ≠ 0)
    (s₂Nonzero : s₂ ≠ 0) (s₃Nonzero : s₃ ≠ 0)
    (triple : TripleSpread.SpreadTriple s₁ s₂ s₃)
    (givenRatio : s₁ / s₂ = ratio) :
    Squares.IsSquare (ratio * (1 - s₃)) ∧
      ∀ root : K, ratio * (1 - s₃) = root ^ 2 →
        ((ratio + 1 + 2 * root ≠ 0) ∧
            s₂ = s₃ / (ratio + 1 + 2 * root)) ∨
          ((ratio + 1 - 2 * root ≠ 0) ∧
            s₂ = s₃ / (ratio + 1 - 2 * root)) := by
  exact ⟨spread_from_ratio_square s₁ s₂ s₃ ratio twoNonzero s₂Nonzero
      triple givenRatio,
    fun root rootEquation => spread_from_ratio_alternatives s₁ s₂ s₃ ratio
      root s₂Nonzero s₃Nonzero triple givenRatio rootEquation⟩
end Purelib.Geometry.Trigonometry.Spread.Triple.Ratio

end
