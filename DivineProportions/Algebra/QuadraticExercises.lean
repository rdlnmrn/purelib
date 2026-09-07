import DivineProportions.Algebra.QuadraticCompatibility
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Exercises 2.8–2.9

Both printed exercises omit genuine degenerate cases.  The determinant formula
in Exercise 2.8 is sufficient only when its displayed root denominator is
nonzero.  Exercise 2.9 uses `±2q` where the valid root-free condition is
`(p₁-p₂)²=4q`, and coincident equations still require `q` to be a square.
The corrected constructive statements and explicit rational counterexamples
are given below.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Two displayed general-form quadratic equations have a common root. -/
def GeneralQuadraticsCompatible
    (a₁ b₁ c₁ a₂ b₂ c₂ : K) : Prop :=
  ∃ x : K,
    a₁ * x ^ 2 + b₁ * x + c₁ = 0 ∧
      a₂ * x ^ 2 + b₂ * x + c₂ = 0

/-- The determinant identity printed in Exercise 2.8. -/
def generalQuadraticCompatibilityIdentity
    (a₁ b₁ c₁ a₂ b₂ c₂ : K) : Prop :=
  (a₁ * c₂ - a₂ * c₁) ^ 2 =
    (a₁ * b₂ - a₂ * b₁) * (b₁ * c₂ - b₂ * c₁)

/-- The root displayed in Exercise 2.8. -/
def generalQuadraticCommonRoot
    (a₁ b₁ c₁ a₂ b₂ c₂ : K) : K :=
  (a₂ * c₁ - a₁ * c₂) / (a₁ * b₂ - a₂ * b₁)

private theorem eq_zero_of_nonzero_mul_left
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = 1 * value := by ring1
    _ = factor⁻¹ * (factor * value) := by rw [← factorCancel]; ring1
    _ = 0 := by rw [productZero]; ring1

/-- Any common root implies the Exercise 2.8 determinant identity, including
when the two displayed equations are proportional. -/
theorem generalQuadraticCompatibilityIdentity_of_compatible
    {a₁ b₁ c₁ a₂ b₂ c₂ : K}
    (compatible :
      GeneralQuadraticsCompatible a₁ b₁ c₁ a₂ b₂ c₂) :
    generalQuadraticCompatibilityIdentity a₁ b₁ c₁ a₂ b₂ c₂ := by
  rcases compatible with ⟨x, firstEquation, secondEquation⟩
  have firstConstant : c₁ = -(a₁ * x ^ 2 + b₁ * x) := by
    calc
      c₁ = (a₁ * x ^ 2 + b₁ * x + c₁) -
          (a₁ * x ^ 2 + b₁ * x) := by ring1
      _ = -(a₁ * x ^ 2 + b₁ * x) := by rw [firstEquation]; ring1
  have secondConstant : c₂ = -(a₂ * x ^ 2 + b₂ * x) := by
    calc
      c₂ = (a₂ * x ^ 2 + b₂ * x + c₂) -
          (a₂ * x ^ 2 + b₂ * x) := by ring1
      _ = -(a₂ * x ^ 2 + b₂ * x) := by rw [secondEquation]; ring1
  unfold generalQuadraticCompatibilityIdentity
  rw [firstConstant, secondConstant]
  ring1

private theorem generalQuadraticCommonRoot_first
    {a₁ b₁ c₁ a₂ b₂ c₂ : K}
    (denominatorNonzero : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (identity :
      generalQuadraticCompatibilityIdentity a₁ b₁ c₁ a₂ b₂ c₂) :
    a₁ * (generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂) ^ 2 +
        b₁ * generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂ + c₁ = 0 := by
  let denominator := a₁ * b₂ - a₂ * b₁
  let numerator := a₂ * c₁ - a₁ * c₂
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have residual :
      (a₁ * c₂ - a₂ * c₁) ^ 2 -
          denominator * (b₁ * c₂ - b₂ * c₁) = 0 := by
    unfold generalQuadraticCompatibilityIdentity at identity
    rw [identity]
    unfold denominator
    ring1
  have cleared :
      a₁ * numerator ^ 2 + b₁ * numerator * denominator +
          c₁ * denominator ^ 2 = 0 := by
    calc
      a₁ * numerator ^ 2 + b₁ * numerator * denominator +
          c₁ * denominator ^ 2 =
        a₁ * ((a₁ * c₂ - a₂ * c₁) ^ 2 -
          denominator * (b₁ * c₂ - b₂ * c₁)) := by
        unfold numerator denominator
        ring1
      _ = 0 := by rw [residual]; ring1
  have rootFormula :
      generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂ =
        numerator / denominator := rfl
  rw [rootFormula]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    a₁ * (numerator * denominator⁻¹) ^ 2 +
          b₁ * (numerator * denominator⁻¹) + c₁ =
        (a₁ * numerator ^ 2 + b₁ * numerator * denominator +
            c₁ * denominator ^ 2) * denominator⁻¹ ^ 2 +
          b₁ * numerator * denominator⁻¹ *
            (1 - denominator * denominator⁻¹) +
          c₁ * (1 - (denominator * denominator⁻¹) ^ 2) := by ring1
    _ = 0 := by rw [cleared, denominatorCancel]; ring1

private theorem generalQuadraticCommonRoot_second
    {a₁ b₁ c₁ a₂ b₂ c₂ : K}
    (denominatorNonzero : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (identity :
      generalQuadraticCompatibilityIdentity a₁ b₁ c₁ a₂ b₂ c₂) :
    a₂ * (generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂) ^ 2 +
        b₂ * generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂ + c₂ = 0 := by
  let denominator := a₁ * b₂ - a₂ * b₁
  let numerator := a₂ * c₁ - a₁ * c₂
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have residual :
      (a₁ * c₂ - a₂ * c₁) ^ 2 -
          denominator * (b₁ * c₂ - b₂ * c₁) = 0 := by
    unfold generalQuadraticCompatibilityIdentity at identity
    rw [identity]
    unfold denominator
    ring1
  have cleared :
      a₂ * numerator ^ 2 + b₂ * numerator * denominator +
          c₂ * denominator ^ 2 = 0 := by
    calc
      a₂ * numerator ^ 2 + b₂ * numerator * denominator +
          c₂ * denominator ^ 2 =
        a₂ * ((a₁ * c₂ - a₂ * c₁) ^ 2 -
          denominator * (b₁ * c₂ - b₂ * c₁)) := by
        unfold numerator denominator
        ring1
      _ = 0 := by rw [residual]; ring1
  have rootFormula :
      generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂ =
        numerator / denominator := rfl
  rw [rootFormula]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    a₂ * (numerator * denominator⁻¹) ^ 2 +
          b₂ * (numerator * denominator⁻¹) + c₂ =
        (a₂ * numerator ^ 2 + b₂ * numerator * denominator +
            c₂ * denominator ^ 2) * denominator⁻¹ ^ 2 +
          b₂ * numerator * denominator⁻¹ *
            (1 - denominator * denominator⁻¹) +
          c₂ * (1 - (denominator * denominator⁻¹) ^ 2) := by ring1
    _ = 0 := by rw [cleared, denominatorCancel]; ring1

/-- Exercise 2.8 in the nondegenerate case implicitly required by its
displayed division: the determinant condition is necessary and sufficient. -/
theorem exercise_2_8
    (a₁ b₁ c₁ a₂ b₂ c₂ : K)
    (denominatorNonzero : a₁ * b₂ - a₂ * b₁ ≠ 0) :
    GeneralQuadraticsCompatible a₁ b₁ c₁ a₂ b₂ c₂ ↔
      generalQuadraticCompatibilityIdentity a₁ b₁ c₁ a₂ b₂ c₂ := by
  constructor
  · exact generalQuadraticCompatibilityIdentity_of_compatible
  · intro identity
    exact ⟨generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂,
      generalQuadraticCommonRoot_first denominatorNonzero identity,
      generalQuadraticCommonRoot_second denominatorNonzero identity⟩

/-- The displayed Exercise 2.8 root is the unique common root whenever its
denominator is nonzero. -/
theorem exercise_2_8_commonRoot_unique
    {a₁ b₁ c₁ a₂ b₂ c₂ x : K}
    (denominatorNonzero : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (firstEquation : a₁ * x ^ 2 + b₁ * x + c₁ = 0)
    (secondEquation : a₂ * x ^ 2 + b₂ * x + c₂ = 0) :
    x = generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂ := by
  let denominator := a₁ * b₂ - a₂ * b₁
  let numerator := a₂ * c₁ - a₁ * c₂
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have linearEquation : denominator * x = numerator := by
    calc
      denominator * x =
          a₁ * (a₂ * x ^ 2 + b₂ * x + c₂) -
            a₂ * (a₁ * x ^ 2 + b₁ * x + c₁) + numerator := by
        unfold denominator numerator
        ring1
      _ = numerator := by rw [firstEquation, secondEquation]; ring1
  have rootFormula :
      generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂ =
        numerator / denominator := rfl
  rw [rootFormula]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    x = x * (denominator * denominator⁻¹) := by rw [denominatorCancel]; ring1
    _ = (denominator * x) * denominator⁻¹ := by ring1
    _ = numerator * denominator⁻¹ := by rw [linearEquation]

/-- Counterexample to the degenerate wording of Exercise 2.8: over the
constructive rationals, the identical equations `x²+1=0` satisfy the printed
determinant identity but have no common root. -/
theorem exercise_2_8_printed_counterexample :
    let R := RFAP.ConstructiveFraction.Rational
    generalQuadraticCompatibilityIdentity
        (1 : R) 0 1 1 0 1 ∧
      ¬ GeneralQuadraticsCompatible (1 : R) 0 1 1 0 1 := by
  dsimp only
  constructor
  · unfold generalQuadraticCompatibilityIdentity
    ring1
  · rintro ⟨root, firstEquation, _⟩
    have squareEqualsNegativeOne : root ^ 2 = (-1 :
        RFAP.ConstructiveFraction.Rational) := by
      calc
        root ^ 2 = (1 * root ^ 2 + 0 * root + 1) - 1 := by ring1
        _ = -1 := by rw [firstEquation]; ring1
    have squareNonnegative :=
      RFAP.ConstructiveFraction.sq_nonneg_direct root
    rw [squareEqualsNegativeOne] at squareNonnegative
    exact (by decide : ¬ ((0 : RFAP.ConstructiveFraction.Rational) ≤ -1))
      squareNonnegative

private theorem square_nonzero_of_nonzero {value : K} (nonzero : value ≠ 0) :
    value ^ 2 ≠ 0 := by
  simpa only [pow_two] using RFAP.ExplicitField.mul_ne_zero nonzero nonzero

/-- Corrected Exercise 2.9.  Coincident equations require a supplied square
witness for `q`; distinct centers are compatible exactly when their squared
separation is `4q`. -/
theorem exercise_2_9 [DecidableEq K]
    (p₁ p₂ q : K) (twoNonzero : (2 : K) ≠ 0) :
    QuadraticsCompatible p₁ q p₂ q ↔
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
        quadraticCompatibilityIdentity_of_compatible compatible
      have differenceNonzero : p₁ - p₂ ≠ 0 := by
        intro differenceZero
        apply centersEqual
        calc
          p₁ = (p₁ - p₂) + p₂ := by ring1
          _ = p₂ := by rw [differenceZero]; ring1
      have differenceSquareNonzero :=
        square_nonzero_of_nonzero differenceNonzero
      have productZero :
          (p₁ - p₂) ^ 2 * ((p₁ - p₂) ^ 2 - 4 * q) = 0 := by
        unfold quadraticCompatibilityIdentity at identity
        calc
          (p₁ - p₂) ^ 2 * ((p₁ - p₂) ^ 2 - 4 * q) =
              (((p₁ - p₂) ^ 2 - (q + q)) ^ 2) - 4 * q * q := by
            ring1
          _ = 0 := by rw [identity]; ring1
      have differenceEquation :=
        eq_zero_of_nonzero_mul_left differenceSquareNonzero productZero
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
      apply (quadraticCompatibility_of_distinct_centres
        twoNonzero centersDistinct).2
      unfold quadraticCompatibilityIdentity
      rw [separation]
      ring1

/-- In the distinct-center case of corrected Exercise 2.9, the source's
midpoint formula is the unique common root. -/
theorem exercise_2_9_commonRoot_unique
    {p₁ p₂ q x : K} (twoNonzero : (2 : K) ≠ 0)
    (centersDistinct : p₁ ≠ p₂)
    (firstEquation : (x - p₁) ^ 2 = q)
    (secondEquation : (x - p₂) ^ 2 = q) :
    x = (p₁ + p₂) / 2 := by
  have unique := quadraticCommonRoot_unique twoNonzero centersDistinct
    firstEquation secondEquation
  calc
    x = quadraticCommonRoot p₁ q p₂ q := unique
    _ = (p₁ + p₂) / 2 := by
      unfold quadraticCommonRoot
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      ring1

/-- Concrete refutation of Exercise 2.9 as printed: the compatible rational
equations `(x-0)²=4` and `(x-4)²=4` have center difference `-4`, not `±8`. -/
theorem exercise_2_9_printed_counterexample :
    let R := RFAP.ConstructiveFraction.Rational
    QuadraticsCompatible (0 : R) 4 4 4 ∧
      ¬ ((0 : R) = 4 ∨ 0 - 4 = 2 * 4 ∨ 0 - 4 = -(2 * 4)) := by
  dsimp only
  constructor
  · exact ⟨2, by ring1, by ring1⟩
  · decide

end DivineProportions
