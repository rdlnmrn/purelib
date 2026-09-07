import mathlib.RFAP.ExplicitField
import mathlib.RFAP.FiniteBinomial
import mathlib.Tactic.QuotientFreeRing

/-!
# Divine Proportions, §2.2–2.3: proportions and identities

The source's elementary identities are stated directly over constructive
commutative rings.  Its three-index antisymmetrization is an explicit six-term
operation, so none of these declarations uses permutations, finite sums, or a
global enumeration.
-/

namespace DivineProportions

variable {K : Type*}

/-- A displayed 3-proportion, retaining the source's requirement that its
three entries are not all zero. -/
structure ThreeProportion (K : Type*) [Zero K] where
  first : K
  second : K
  third : K
  nonzero : first ≠ 0 ∨ second ≠ 0 ∨ third ≠ 0

namespace ThreeProportion

variable [CommRing K]

def FirstCondition (left right : ThreeProportion K) : Prop :=
  left.first * right.second = right.first * left.second

def SecondCondition (left right : ThreeProportion K) : Prop :=
  left.second * right.third = right.second * left.third

def ThirdCondition (left right : ThreeProportion K) : Prop :=
  left.third * right.first = right.third * left.first

/-- The quotient-free equality test for two displayed 3-proportions. -/
def Equivalent (left right : ThreeProportion K) : Prop :=
  FirstCondition left right ∧ SecondCondition left right ∧
    ThirdCondition left right

end ThreeProportion

section ThreeProportionExamples

variable [CommRing K] [Nontrivial K]

private def exerciseTwoFourLeftFirst : ThreeProportion K :=
  ⟨1, 0, 0, Or.inl one_ne_zero⟩

private def exerciseTwoFourRightFirst : ThreeProportion K :=
  ⟨1, 1, 0, Or.inl one_ne_zero⟩

private def exerciseTwoFourLeftSecond : ThreeProportion K :=
  ⟨0, 1, 0, Or.inr (Or.inl one_ne_zero)⟩

private def exerciseTwoFourRightSecond : ThreeProportion K :=
  ⟨0, 1, 1, Or.inr (Or.inl one_ne_zero)⟩

private def exerciseTwoFourRightThird : ThreeProportion K :=
  ⟨1, 0, 1, Or.inl one_ne_zero⟩

/-- Exercise 2.4: none of the three cross-product conditions follows from
the other two.  Each conjunct supplies a valid pair for which the named
condition fails and the remaining two hold. -/
theorem exercise_2_4 :
    (¬ ThreeProportion.FirstCondition
        (exerciseTwoFourLeftFirst (K := K)) exerciseTwoFourRightFirst ∧
      ThreeProportion.SecondCondition
        (exerciseTwoFourLeftFirst (K := K)) exerciseTwoFourRightFirst ∧
      ThreeProportion.ThirdCondition
        (exerciseTwoFourLeftFirst (K := K)) exerciseTwoFourRightFirst) ∧
    (ThreeProportion.FirstCondition
        (exerciseTwoFourLeftSecond (K := K)) exerciseTwoFourRightSecond ∧
      ¬ ThreeProportion.SecondCondition
        (exerciseTwoFourLeftSecond (K := K)) exerciseTwoFourRightSecond ∧
      ThreeProportion.ThirdCondition
        (exerciseTwoFourLeftSecond (K := K)) exerciseTwoFourRightSecond) ∧
    (ThreeProportion.FirstCondition
        (exerciseTwoFourLeftFirst (K := K)) exerciseTwoFourRightThird ∧
      ThreeProportion.SecondCondition
        (exerciseTwoFourLeftFirst (K := K)) exerciseTwoFourRightThird ∧
      ¬ ThreeProportion.ThirdCondition
        (exerciseTwoFourLeftFirst (K := K)) exerciseTwoFourRightThird) := by
  unfold ThreeProportion.FirstCondition ThreeProportion.SecondCondition
    ThreeProportion.ThirdCondition exerciseTwoFourLeftFirst
    exerciseTwoFourRightFirst exerciseTwoFourLeftSecond
    exerciseTwoFourRightSecond exerciseTwoFourRightThird
  constructor
  · exact ⟨by simp, by ring1, by ring1⟩
  constructor
  · exact ⟨by ring1, by simp, by ring1⟩
  · exact ⟨by ring1, by ring1,
      by simp⟩

end ThreeProportionExamples

/-- Example 2.6: the rational proportion `3:7=(12/7):4`, recorded through
its quotient-free cross-product equation. -/
theorem example_2_6 [RFAP.ExplicitField K]
    (sevenNonzero : (7 : K) ≠ 0) :
    (3 : K) * 4 - (12 / 7) * 7 = 0 := by
  rw [RFAP.ExplicitField.div_mul_cancel 12 sevenNonzero]
  ring1

section Identities

variable [CommRing K]

/-- Example 2.7: the Binomial theorem as a sum over exactly the finite range
`0,…,n`, in the source's descending/ascending exponent order. -/
theorem example_2_7 (exponent : Nat) (x₁ x₂ : K) :
    (x₁ + x₂) ^ exponent =
      RFAP.finiteBinomialExpansion exponent x₁ x₂ :=
  RFAP.finite_binomial_theorem exponent x₁ x₂

/-- Example 2.8: the three-variable square identity. -/
theorem example_2_8 (x₁ x₂ x₃ : K) :
    (x₁ + x₂ + x₃) ^ 2 =
      x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 +
        2 * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) := by
  ring1

/-- Example 2.9: Fibonacci's identity. -/
theorem example_2_9 (x₁ y₁ x₂ y₂ : K) :
    (x₁ * y₂ - x₂ * y₁) ^ 2 + (x₁ * x₂ + y₁ * y₂) ^ 2 =
      (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2) := by
  ring1

/-- Example 2.10: Cauchy's three-coordinate extension of Fibonacci's
identity. -/
theorem example_2_10
    (x₁ y₁ z₁ x₂ y₂ z₂ : K) :
    (x₁ * y₂ - x₂ * y₁) ^ 2 +
        (y₁ * z₂ - y₂ * z₁) ^ 2 +
        (z₁ * x₂ - z₂ * x₁) ^ 2 +
        (x₁ * x₂ + y₁ * y₂ + z₁ * z₂) ^ 2 =
      (x₁ ^ 2 + y₁ ^ 2 + z₁ ^ 2) *
        (x₂ ^ 2 + y₂ ^ 2 + z₂ ^ 2) := by
  ring1

/-- Exercise 2.5: the two preceding identities and the requested plus/minus
variant, packaged exactly as three polynomial checks. -/
theorem exercise_2_5
    (x₁ y₁ z₁ x₂ y₂ z₂ : K) :
    ((x₁ * y₂ - x₂ * y₁) ^ 2 + (x₁ * x₂ + y₁ * y₂) ^ 2 =
      (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2)) ∧
    ((x₁ * y₂ - x₂ * y₁) ^ 2 +
        (y₁ * z₂ - y₂ * z₁) ^ 2 +
        (z₁ * x₂ - z₂ * x₁) ^ 2 +
        (x₁ * x₂ + y₁ * y₂ + z₁ * z₂) ^ 2 =
      (x₁ ^ 2 + y₁ ^ 2 + z₁ ^ 2) *
        (x₂ ^ 2 + y₂ ^ 2 + z₂ ^ 2)) ∧
    ((x₁ * y₂ + x₂ * y₁) ^ 2 + (x₁ * x₂ - y₁ * y₂) ^ 2 =
      (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2)) := by
  exact ⟨by ring1, by ring1, by ring1⟩

/-- Exercise 2.6: the coordinate-difference identity later used by the
Spread-ratio theorem. -/
theorem exercise_2_6
    (x₁ y₁ x₂ y₂ x₃ y₃ : K) :
    (y₁ - y₂) * (x₃ - x₁) - (y₁ - y₃) * (x₂ - x₁) =
      (y₁ - y₃) * (x₃ - x₂) - (y₂ - y₃) * (x₃ - x₁) := by
  ring1

/-- The book's three-index alternating bracket, with the six permutations
written explicitly in its stated sign order. -/
def alternatingThree
    (term : Fin 3 → Fin 3 → Fin 3 → K) : K :=
  term 0 1 2 - term 0 2 1 + term 1 2 0 -
    term 2 1 0 + term 2 0 1 - term 1 0 2

/-- Example 2.11: expansion of the ordinary three-by-three determinant. -/
theorem example_2_11 (x y z : Fin 3 → K) :
    alternatingThree (fun i j k => x i * y j * z k) =
      x 0 * y 1 * z 2 - x 0 * y 2 * z 1 +
        x 1 * y 2 * z 0 - x 2 * y 1 * z 0 +
        x 2 * y 0 * z 1 - x 1 * y 0 * z 2 := by
  rfl

/-- Example 2.12: the determinant with constant third column. -/
theorem example_2_12 (x y : Fin 3 → K) :
    alternatingThree (fun i j _ => x i * y j) =
      x 0 * y 1 - x 0 * y 2 + x 1 * y 2 -
        x 2 * y 1 + x 2 * y 0 - x 1 * y 0 := by
  rfl

/-- Example 2.13: expansion of `[x₁x₂⁵y₂]⁻₃`. -/
theorem example_2_13 (x y : Fin 3 → K) :
    alternatingThree (fun i j _ => x i * x j ^ 5 * y j) =
      x 0 * x 1 ^ 5 * y 1 - x 0 * x 2 ^ 5 * y 2 +
        x 1 * x 2 ^ 5 * y 2 - x 2 * x 1 ^ 5 * y 1 +
        x 2 * x 0 ^ 5 * y 0 - x 1 * x 0 ^ 5 * y 0 := by
  rfl

/-- Example 2.14: antisymmetrizing a one-index term gives zero. -/
theorem example_2_14 (x : Fin 3 → K) :
    alternatingThree (fun i _ _ => x i) = 0 := by
  unfold alternatingThree
  ring1

/-- Exercise 2.7: the displayed product rule for three-index alternating
brackets. -/
theorem exercise_2_7 (x y : Fin 3 → K) :
    alternatingThree (fun i j _ => x i ^ 2 * y j) +
        alternatingThree (fun i j _ => x i * x j * y j) =
      (x 0 + x 1 + x 2) *
        alternatingThree (fun i j _ => x i * y j) := by
  unfold alternatingThree
  ring1

/-- The source's four-index alternating bracket, expanded into its 24 signed
terms in the printed order. -/
def alternatingFour
    (term : Fin 4 → Fin 4 → Fin 4 → Fin 4 → K) : K :=
  term 0 1 2 3 - term 0 1 3 2 + term 0 2 3 1 - term 0 3 2 1 +
    term 0 3 1 2 - term 0 2 1 3 +
  term 1 2 0 3 - term 1 3 0 2 + term 2 3 0 1 - term 2 3 1 0 +
    term 1 3 2 0 - term 1 2 3 0 +
  term 2 1 3 0 - term 3 1 2 0 + term 3 2 1 0 - term 3 2 0 1 +
    term 3 1 0 2 - term 2 1 0 3 +
  term 2 0 1 3 - term 3 0 1 2 + term 3 0 2 1 - term 2 0 3 1 +
    term 1 0 3 2 - term 1 0 2 3

/-- Example 2.15: the printed 24-term expansion of `[x₁²x₂y₃]⁻₄`. -/
theorem example_2_15 (x y : Fin 4 → K) :
    alternatingFour (fun i j k _ => x i ^ 2 * x j * y k) =
      x 0 ^ 2 * x 1 * y 2 - x 0 ^ 2 * x 1 * y 3 +
      x 0 ^ 2 * x 2 * y 3 - x 0 ^ 2 * x 3 * y 2 +
      x 0 ^ 2 * x 3 * y 1 - x 0 ^ 2 * x 2 * y 1 +
      x 1 ^ 2 * x 2 * y 0 - x 1 ^ 2 * x 3 * y 0 +
      x 2 ^ 2 * x 3 * y 0 - x 2 ^ 2 * x 3 * y 1 +
      x 1 ^ 2 * x 3 * y 2 - x 1 ^ 2 * x 2 * y 3 +
      x 2 ^ 2 * x 1 * y 3 - x 3 ^ 2 * x 1 * y 2 +
      x 3 ^ 2 * x 2 * y 1 - x 3 ^ 2 * x 2 * y 0 +
      x 3 ^ 2 * x 1 * y 0 - x 2 ^ 2 * x 1 * y 0 +
      x 2 ^ 2 * x 0 * y 1 - x 3 ^ 2 * x 0 * y 1 +
      x 3 ^ 2 * x 0 * y 2 - x 2 ^ 2 * x 0 * y 3 +
      x 1 ^ 2 * x 0 * y 3 - x 1 ^ 2 * x 0 * y 2 := by
  rfl

end Identities

end DivineProportions
