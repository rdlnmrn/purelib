module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Quadratic.CommonRoot.Centered
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

@[expose] public section

/-!
# Divine Proportions, Exercises 2.8–2.9

Both printed exercises omit genuine degenerate cases.  The determinant formula
in Exercise 2.8 is sufficient only when its displayed root denominator is
nonzero.  Exercise 2.9 uses `±2q` where the valid root-free condition is
`(p₁-p₂)²=4q`, and coincident equations still require `q` to be a square.
The corrected constructive statements and explicit rational counterexamples
are given below.
-/

namespace Purelib.Polynomial.Quadratic.CommonRoot.EqualRadius

variable {K : Type*} [ExplicitField K]

/-- Two centered quadratics with the same radius parameter share a root exactly under the stated coincident- or
distinct-center conditions.

Assuming two is nonzero, coincident centers require an explicit square witness; distinct centers require squared
separation equal to four times the radius parameter. -/
theorem exercise_2_9 [DecidableEq K]
    (p₁ p₂ q : K) (twoNonzero : (2 : K) ≠ 0) :
    Quadratic.CommonRoot.Centered.QuadraticsCompatible p₁ q p₂ q ↔
      (p₁ = p₂ ∧ ∃ root : K, root ^ 2 = q) ∨
        (p₁ ≠ p₂ ∧ (p₁ - p₂) ^ 2 = 4 * q) := by
  constructor
  · intro compatible
    by_cases centersEqual : p₁ = p₂
    · left
      rcases compatible with ⟨root, firstEquation, _⟩
      exact ⟨centersEqual, ⟨root - p₁, firstEquation⟩⟩
    · right
      have identity :=
        Quadratic.CommonRoot.Centered.quadraticCompatibilityIdentity_of_compatible compatible
      have differenceNonzero : p₁ - p₂ ≠ 0 := by
        intro differenceZero
        apply centersEqual
        calc
          p₁ = (p₁ - p₂) + p₂ := by ring1
          _ = p₂ := by rw [differenceZero]; ring1
      have differenceSquareNonzero :=
        ExplicitField.square_nonzero_of_nonzero differenceNonzero
      have productZero :
          (p₁ - p₂) ^ 2 * ((p₁ - p₂) ^ 2 - 4 * q) = 0 := by
        unfold Quadratic.CommonRoot.Centered.quadraticCompatibilityIdentity at identity
        calc
          (p₁ - p₂) ^ 2 * ((p₁ - p₂) ^ 2 - 4 * q) =
              (((p₁ - p₂) ^ 2 - (q + q)) ^ 2) - 4 * q * q := by
            ring1
          _ = 0 := by rw [identity]; ring1
      have differenceEquation :=
        ExplicitField.eq_zero_of_mul_eq_zero_left differenceSquareNonzero productZero
      refine ⟨centersEqual, ?_⟩
      calc
        (p₁ - p₂) ^ 2 =
            ((p₁ - p₂) ^ 2 - 4 * q) + 4 * q := by ring1
        _ = 4 * q := by rw [differenceEquation]; ring1
  · intro condition
    rcases condition with coincident | distinct
    · rcases coincident with ⟨centersEqual, root, rootSquare⟩
      subst p₂
      exact ⟨p₁ + root, by rw [show p₁ + root - p₁ = root by ring1,
        rootSquare], by rw [show p₁ + root - p₁ = root by ring1,
        rootSquare]⟩
    · rcases distinct with ⟨centersDistinct, separation⟩
      apply (Quadratic.CommonRoot.Centered.quadraticCompatibility_of_distinct_centres
        twoNonzero centersDistinct).2
      unfold Quadratic.CommonRoot.Centered.quadraticCompatibilityIdentity
      rw [separation]
      ring1

/-- For distinct centers and nonzero two, any common root of the equal-radius quadratics is their midpoint. -/
theorem exercise_2_9_commonRoot_unique
    {p₁ p₂ q x : K} (twoNonzero : (2 : K) ≠ 0)
    (centersDistinct : p₁ ≠ p₂)
    (firstEquation : (x - p₁) ^ 2 = q)
    (secondEquation : (x - p₂) ^ 2 = q) :
    x = (p₁ + p₂) / 2 := by
  have unique := Quadratic.CommonRoot.Centered.quadraticCommonRoot_unique twoNonzero centersDistinct
    firstEquation secondEquation
  calc
    x = Quadratic.CommonRoot.Centered.quadraticCommonRoot p₁ q p₂ q := unique
    _ = (p₁ + p₂) / 2 := by
      unfold Quadratic.CommonRoot.Centered.quadraticCommonRoot
      simp only [ExplicitField.div_eq_mul_inv]
      ring1
end Purelib.Polynomial.Quadratic.CommonRoot.EqualRadius

end
