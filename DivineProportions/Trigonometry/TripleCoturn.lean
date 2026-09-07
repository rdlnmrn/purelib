import DivineProportions.Trigonometry.TripleTwist

/-!
# Divine Proportions, Chapter 9: the triple coturn formula

Exercise 9.1 reverses the numerator and denominator in the turn quotient.
Its cyclic identity is first proved as a direct polynomial equation in the
six displayed line coefficients; the three nonparallel certificates are used
only to recover the source's quotients.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Coturn of an ordered pair of nonparallel lines. -/
def coturn (first second : Line K)
    (_notParallel : ¬ first.Parallel second) : K :=
  (first.a * second.a + first.b * second.b) /
    (first.a * second.b - second.a * first.b)

private theorem eq_of_mul_eq_mul_right
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

/-- Reversing the ordered line pair negates its coturn. -/
theorem coturn_reverse
    (first second : Line K)
    (firstSecondNotParallel : ¬ first.Parallel second)
    (secondFirstNotParallel : ¬ second.Parallel first) :
    coturn second first secondFirstNotParallel =
      -coturn first second firstSecondNotParallel := by
  unfold coturn
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  have inverseNegative := RFAP.ExplicitField.inv_neg
    (first.a * second.b - second.a * first.b)
  rw [show second.a * first.b - first.a * second.b =
      -(first.a * second.b - second.a * first.b) by ring1,
    inverseNegative]
  ring1

/-- Denominator-free core of the Triple coturn formula. -/
theorem triple_coturn_formula_cleared
    (first second third : Line K) :
    (second.a * third.a + second.b * third.b) *
          (third.a * first.a + third.b * first.b) *
          (first.a * second.b - second.a * first.b) +
        (third.a * first.a + third.b * first.b) *
          (first.a * second.a + first.b * second.b) *
          (second.a * third.b - third.a * second.b) +
        (first.a * second.a + first.b * second.b) *
          (second.a * third.a + second.b * third.b) *
          (third.a * first.b - first.a * third.b) =
      (second.a * third.b - third.a * second.b) *
        (third.a * first.b - first.a * third.b) *
        (first.a * second.b - second.a * first.b) := by
  ring1

/-- Exercise 9.1 (Triple coturn formula). -/
theorem exercise_9_1
    (first second third : Line K)
    (firstSecondNotParallel : ¬ first.Parallel second)
    (secondThirdNotParallel : ¬ second.Parallel third)
    (thirdFirstNotParallel : ¬ third.Parallel first) :
    let o₁ := coturn second third secondThirdNotParallel
    let o₂ := coturn third first thirdFirstNotParallel
    let o₃ := coturn first second firstSecondNotParallel
    o₁ * o₂ + o₂ * o₃ + o₃ * o₁ = 1 := by
  dsimp only
  let firstNumerator := second.a * third.a + second.b * third.b
  let secondNumerator := third.a * first.a + third.b * first.b
  let thirdNumerator := first.a * second.a + first.b * second.b
  let firstDenominator := second.a * third.b - third.a * second.b
  let secondDenominator := third.a * first.b - first.a * third.b
  let thirdDenominator := first.a * second.b - second.a * first.b
  let denominator := firstDenominator * secondDenominator * thirdDenominator
  have firstDenominatorNonzero : firstDenominator ≠ 0 :=
    secondThirdNotParallel
  have secondDenominatorNonzero : secondDenominator ≠ 0 :=
    thirdFirstNotParallel
  have thirdDenominatorNonzero : thirdDenominator ≠ 0 :=
    firstSecondNotParallel
  have denominatorNonzero : denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero firstDenominatorNonzero
        secondDenominatorNonzero)
      thirdDenominatorNonzero
  have firstCancel :
      firstNumerator / firstDenominator * firstDenominator =
        firstNumerator :=
    RFAP.ExplicitField.div_mul_cancel _ firstDenominatorNonzero
  have secondCancel :
      secondNumerator / secondDenominator * secondDenominator =
        secondNumerator :=
    RFAP.ExplicitField.div_mul_cancel _ secondDenominatorNonzero
  have thirdCancel :
      thirdNumerator / thirdDenominator * thirdDenominator =
        thirdNumerator :=
    RFAP.ExplicitField.div_mul_cancel _ thirdDenominatorNonzero
  have clearedIdentity :
      firstNumerator * secondNumerator * thirdDenominator +
          secondNumerator * thirdNumerator * firstDenominator +
          thirdNumerator * firstNumerator * secondDenominator =
        firstDenominator * secondDenominator * thirdDenominator := by
    exact triple_coturn_formula_cleared first second third
  unfold coturn
  change
    firstNumerator / firstDenominator *
          (secondNumerator / secondDenominator) +
        secondNumerator / secondDenominator *
          (thirdNumerator / thirdDenominator) +
        thirdNumerator / thirdDenominator *
          (firstNumerator / firstDenominator) = 1
  apply eq_of_mul_eq_mul_right denominatorNonzero
  calc
    (firstNumerator / firstDenominator *
            (secondNumerator / secondDenominator) +
          secondNumerator / secondDenominator *
            (thirdNumerator / thirdDenominator) +
          thirdNumerator / thirdDenominator *
            (firstNumerator / firstDenominator)) * denominator =
        (firstNumerator / firstDenominator * firstDenominator) *
            (secondNumerator / secondDenominator * secondDenominator) *
            thirdDenominator +
          (secondNumerator / secondDenominator * secondDenominator) *
            (thirdNumerator / thirdDenominator * thirdDenominator) *
            firstDenominator +
          (thirdNumerator / thirdDenominator * thirdDenominator) *
            (firstNumerator / firstDenominator * firstDenominator) *
            secondDenominator := by
      unfold denominator
      ring1
    _ = firstNumerator * secondNumerator * thirdDenominator +
          secondNumerator * thirdNumerator * firstDenominator +
          thirdNumerator * firstNumerator * secondDenominator := by
      rw [firstCancel, secondCancel, thirdCancel]
    _ = firstDenominator * secondDenominator * thirdDenominator :=
      clearedIdentity
    _ = 1 * denominator := by unfold denominator; ring1

end DivineProportions
