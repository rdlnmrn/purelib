module
public import Purelib.Data.Nat.Order
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Operations
import Purelib.Tactic.Ring
import Purelib.Algebra.Group.Basic

open Purelib.Algebra
open Purelib.Algebra.Field

open Purelib.Geometry.Trigonometry

public section

/-!
# Equal ratios and bisectors for two struts

Finite quad-triple identities determine equal-ratio equations and the retained
bisector relation over an explicitly supplied field.
-/

namespace Purelib.Algebra.Proportions.TwoStruts.Exercises

variable {K : Type*} [ExplicitField K]

/-- Normalize an equal-parameter quad triple to a quadratic equation.

The base parameter is nonzero, allowing its square to be cancelled from the Archimedes identity. -/
private theorem equal_parameter_equation [DecidableEq K]
    (r x : K) (rNonzero : r ≠ 0)
    (triple : Geometry.Trigonometry.QuadTriple r (r * r) (x * r)) :
    (x - r - 1) ^ 2 = 4 * r := by
  have rSquareNonzero : r ^ 2 ≠ 0 := by
    rw [pow_two]
    exact ExplicitField.mul_ne_zero rNonzero rNonzero
  have scaledDifference :
      r ^ 2 * ((x - r - 1) ^ 2 - 4 * r) = 0 := by
    calc
      r ^ 2 * ((x - r - 1) ^ 2 - 4 * r) =
          -QuadTriple.Basic.archimedesFunction r (r * r) (x * r) := by
        unfold QuadTriple.Basic.archimedesFunction
        ring1
      _ = 0 := by
        unfold Geometry.Trigonometry.QuadTriple at triple
        rw [triple]
        exact neg_zero
  have differenceZero : (x - r - 1) ^ 2 - 4 * r = 0 := by
    by_cases zero : (x - r - 1) ^ 2 - 4 * r = 0
    · exact zero
    · exact False.elim
        ((ExplicitField.mul_ne_zero rSquareNonzero zero)
          scaledDifference)
  exact Group.eq_of_sub_eq_zero differenceZero

/-- Equal nonzero input ratios give the same quadratic equation for both outputs.

Each of the two supplied quad triples normalizes to a square equal to four times the common ratio. -/
theorem exercise_11_2
    [DecidableEq K]
    (p r m n : K) (rNonzero : r ≠ 0) (equalRatios : p = r)
    (strutTriples :
      Geometry.Trigonometry.QuadTriple r (r * p) (m * p) ∧
        Geometry.Trigonometry.QuadTriple p (r * p) (n * r)) :
    (m - r - 1) ^ 2 = 4 * r ∧
      (n - r - 1) ^ 2 = 4 * r := by
  subst p
  exact ⟨equal_parameter_equation r m rNonzero strutTriples.1,
    equal_parameter_equation r n rNonzero strutTriples.2⟩

/-- A quad triple with two equal scaled entries forces four times the ratio to equal one.

The common base parameter is nonzero; the conclusion requires no division by four. -/
theorem exercise_11_3_cleared
    [DecidableEq K]
    (p r : K) (rNonzero : r ≠ 0)
    (triple : Geometry.Trigonometry.QuadTriple r (r * p) (r * p)) : 4 * p = 1 := by
  have rSquareNonzero : r ^ 2 ≠ 0 := by
    rw [pow_two]
    exact ExplicitField.mul_ne_zero rNonzero rNonzero
  have scaledDifference : r ^ 2 * (4 * p - 1) = 0 := by
    calc
      r ^ 2 * (4 * p - 1) =
          QuadTriple.Basic.archimedesFunction r (r * p) (r * p) := by
        unfold QuadTriple.Basic.archimedesFunction
        ring1
      _ = 0 := triple
  have differenceZero : 4 * p - 1 = 0 := by
    by_cases zero : 4 * p - 1 = 0
    · exact zero
    · exact False.elim
        ((ExplicitField.mul_ne_zero rSquareNonzero zero)
          scaledDifference)
  exact Group.eq_of_sub_eq_zero differenceZero

/-- A quad triple with two equal scaled entries has ratio one quarter.

The common base parameter and four are both nonzero, permitting cancellation and the final division. -/
theorem exercise_11_3
    [DecidableEq K]
    (p r : K) (rNonzero : r ≠ 0) (fourNonzero : (4 : K) ≠ 0)
    (triple : Geometry.Trigonometry.QuadTriple r (r * p) (r * p)) : p = 1 / 4 := by
  apply ExplicitField.eq_of_mul_eq_mul_right fourNonzero
  calc
    p * 4 = 4 * p := by ring1
    _ = 1 := exercise_11_3_cleared p r rNonzero triple
    _ = (1 / 4) * 4 :=
      (ExplicitField.div_mul_cancel 1 fourNonzero).symm

/-- Transport the first strut quad triple through two retained bisector ratios.

The common spread is nonzero, so scaling and normalization give the ordered triple of first spread, common spread, and
scaled first output. -/
private theorem first_bisector_quadTriple
    (p r m s₁ s₂ s₃ : K) (s₃Nonzero : s₃ ≠ 0)
    (firstBisectorRatio : r * s₂ = s₃)
    (secondBisectorRatio : p * s₁ = s₃)
    (triple : Geometry.Trigonometry.QuadTriple r (r * p) (m * p)) :
    Geometry.Trigonometry.QuadTriple s₁ s₃ (m * s₂) := by
  have scaled := QuadTriple.Operations.quadTriple_scale r (r * p) (m * p) (s₁ * s₂) triple
  have firstValue : (s₁ * s₂) * r = s₁ * s₃ := by
    calc
      (s₁ * s₂) * r = s₁ * (r * s₂) := by ring1
      _ = s₁ * s₃ := by rw [firstBisectorRatio]
  have secondValue : (s₁ * s₂) * (r * p) = s₃ * s₃ := by
    calc
      (s₁ * s₂) * (r * p) = (r * s₂) * (p * s₁) := by ring1
      _ = s₃ * s₃ := by rw [firstBisectorRatio, secondBisectorRatio]
  have thirdValue : (s₁ * s₂) * (m * p) = (m * s₂) * s₃ := by
    calc
      (s₁ * s₂) * (m * p) = (m * s₂) * (p * s₁) := by ring1
      _ = (m * s₂) * s₃ := by rw [secondBisectorRatio]
  rw [firstValue, secondValue, thirdValue] at scaled
  have normalized := QuadTriple.Operations.quadTriple_normalize (s₁ * s₃) (s₃ * s₃)
    ((m * s₂) * s₃) s₃ scaled
  rw [ExplicitField.mul_div_cancel_right s₁ s₃ s₃Nonzero,
    ExplicitField.mul_div_cancel_right s₃ s₃ s₃Nonzero,
    ExplicitField.mul_div_cancel_right (m * s₂) s₃ s₃Nonzero] at normalized
  exact normalized

/-- Transport the second strut quad triple through two retained bisector ratios.

The common spread is nonzero, so scaling and normalization give the ordered triple of second spread, common spread, and
scaled second output. -/
private theorem second_bisector_quadTriple
    (p r n s₁ s₂ s₃ : K) (s₃Nonzero : s₃ ≠ 0)
    (firstBisectorRatio : r * s₂ = s₃)
    (secondBisectorRatio : p * s₁ = s₃)
    (triple : Geometry.Trigonometry.QuadTriple p (r * p) (n * r)) :
    Geometry.Trigonometry.QuadTriple s₂ s₃ (n * s₁) := by
  have scaled := QuadTriple.Operations.quadTriple_scale p (r * p) (n * r) (s₁ * s₂) triple
  have firstValue : (s₁ * s₂) * p = s₂ * s₃ := by
    calc
      (s₁ * s₂) * p = s₂ * (p * s₁) := by ring1
      _ = s₂ * s₃ := by rw [secondBisectorRatio]
  have secondValue : (s₁ * s₂) * (r * p) = s₃ * s₃ := by
    calc
      (s₁ * s₂) * (r * p) = (r * s₂) * (p * s₁) := by ring1
      _ = s₃ * s₃ := by rw [firstBisectorRatio, secondBisectorRatio]
  have thirdValue : (s₁ * s₂) * (n * r) = (n * s₁) * s₃ := by
    calc
      (s₁ * s₂) * (n * r) = (n * s₁) * (r * s₂) := by ring1
      _ = (n * s₁) * s₃ := by rw [firstBisectorRatio]
  rw [firstValue, secondValue, thirdValue] at scaled
  have normalized := QuadTriple.Operations.quadTriple_normalize (s₂ * s₃) (s₃ * s₃)
    ((n * s₁) * s₃) s₃ scaled
  rw [ExplicitField.mul_div_cancel_right s₂ s₃ s₃Nonzero,
    ExplicitField.mul_div_cancel_right s₃ s₃ s₃Nonzero,
    ExplicitField.mul_div_cancel_right (n * s₁) s₃ s₃Nonzero] at normalized
  exact normalized

/-- Derive both bisector square identities with every square term retained.

Two strut quad triples and two cleared bisector ratios determine the identities when their common spread is nonzero. -/
theorem exercise_11_4_corrected
    (p r m n s₁ s₂ s₃ : K) (s₃Nonzero : s₃ ≠ 0)
    (firstBisectorRatio : r * s₂ = s₃)
    (secondBisectorRatio : p * s₁ = s₃)
    (strutTriples :
      Geometry.Trigonometry.QuadTriple r (r * p) (m * p) ∧
        Geometry.Trigonometry.QuadTriple p (r * p) (n * r)) :
    (m * s₂ + s₁ + s₃) ^ 2 =
        2 * ((m * s₂) ^ 2 + s₁ ^ 2 + s₃ ^ 2) ∧
      (n * s₁ + s₂ + s₃) ^ 2 =
        2 * ((n * s₁) ^ 2 + s₂ ^ 2 + s₃ ^ 2) := by
  have firstTriple := first_bisector_quadTriple p r m s₁ s₂ s₃
    s₃Nonzero firstBisectorRatio secondBisectorRatio strutTriples.1
  have secondTriple := second_bisector_quadTriple p r n s₁ s₂ s₃
    s₃Nonzero firstBisectorRatio secondBisectorRatio strutTriples.2
  constructor
  · unfold Geometry.Trigonometry.QuadTriple QuadTriple.Basic.archimedesFunction at firstTriple
    exact Group.eq_of_sub_eq_zero (by
      calc
        (m * s₂ + s₁ + s₃) ^ 2 -
            2 * ((m * s₂) ^ 2 + s₁ ^ 2 + s₃ ^ 2) =
          QuadTriple.Basic.archimedesFunction s₁ s₃ (m * s₂) := by
            unfold QuadTriple.Basic.archimedesFunction
            ring1
        _ = 0 := firstTriple)
  · unfold Geometry.Trigonometry.QuadTriple QuadTriple.Basic.archimedesFunction at secondTriple
    exact Group.eq_of_sub_eq_zero (by
      calc
        (n * s₁ + s₂ + s₃) ^ 2 -
            2 * ((n * s₁) ^ 2 + s₂ ^ 2 + s₃ ^ 2) =
          QuadTriple.Basic.archimedesFunction s₂ s₃ (n * s₁) := by
            unfold QuadTriple.Basic.archimedesFunction
            ring1
        _ = 0 := secondTriple)
end Purelib.Algebra.Proportions.TwoStruts.Exercises
