import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Trigonometry.TripleTwist
import DivineProportions.Plane.LineReflection

/-!
# Divine Proportions, §7.5: spread reflection

The proof clears the two finite spread denominators and factors the resulting
polynomial.  The two factors say respectively that the original lines are
parallel or that the reflected first line is parallel to the second.  The
common-point and distinctness hypotheses eliminate the former.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem ratio_eq_of_cross_product
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ rightNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
            rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

private theorem cross_product_of_ratio_eq
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (ratiosEqual :
      leftNumerator / leftDenominator =
        rightNumerator / rightDenominator) :
    leftNumerator * rightDenominator =
      rightNumerator * leftDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ rightNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv] at ratiosEqual
  calc
    leftNumerator * rightDenominator =
        (leftNumerator * leftDenominator⁻¹) *
          (leftDenominator * rightDenominator) := by
            calc
              leftNumerator * rightDenominator =
                  leftNumerator *
                    (leftDenominator * leftDenominator⁻¹) *
                      rightDenominator := by rw [leftCancel]; ring1
              _ = (leftNumerator * leftDenominator⁻¹) *
                  (leftDenominator * rightDenominator) := by ring1
    _ = (rightNumerator * rightDenominator⁻¹) *
        (leftDenominator * rightDenominator) := by rw [ratiosEqual]
    _ = rightNumerator * leftDenominator := by
      calc
        (rightNumerator * rightDenominator⁻¹) *
            (leftDenominator * rightDenominator) =
          rightNumerator * leftDenominator *
            (rightDenominator * rightDenominator⁻¹) := by ring1
        _ = rightNumerator * leftDenominator := by rw [rightCancel, mul_one]

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

private theorem reflection_spread_factorization
    (mirror first second : Line K) :
    lineNorm second *
          (first.a * mirror.b - mirror.a * first.b) ^ 2 -
        lineNorm first *
          (second.a * mirror.b - mirror.a * second.b) ^ 2 =
      -(first.a * second.b - second.a * first.b) *
        (reflectedLineA mirror first * second.b -
          second.a * reflectedLineB mirror first) := by
  unfold lineNorm reflectedLineA reflectedLineB
  ring1

/-- Reflecting a non-null target in a non-null mirror preserves its spread
with the mirror.  This direct coefficient form does not need an intersection
or a distinctness hypothesis and drives the finite reflection chain in
Theorem 58. -/
theorem spread_reflectLine_mirror [DecidableEq K]
    (mirror target : Line K)
    (mirrorNonNull : ¬ mirror.IsNull)
    (targetNonNull : ¬ target.IsNull) :
    let reflectedNonNull := reflectLine_nonNull mirror target mirrorNonNull
      targetNonNull
    spread (reflectLine mirror target mirrorNonNull) mirror
        reflectedNonNull mirrorNonNull =
      spread target mirror targetNonNull mirrorNonNull := by
  dsimp only
  let reflectedNonNull := reflectLine_nonNull mirror target mirrorNonNull
    targetNonNull
  have reflectedDenominatorNonzero :
      lineNorm (reflectLine mirror target mirrorNonNull) * lineNorm mirror ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero reflectedNonNull mirrorNonNull
  have targetDenominatorNonzero :
      lineNorm target * lineNorm mirror ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero targetNonNull mirrorNonNull
  unfold spread
  apply ratio_eq_of_cross_product reflectedDenominatorNonzero
    targetDenominatorNonzero
  unfold reflectLine reflectedLineA reflectedLineB lineNorm
  ring1

/-- Theorem 52 (Spread reflection).  `¬ first.Equivalent second` is the
quotient-free form of the book's distinct-line hypothesis. -/
theorem spread_reflection [DecidableEq K]
    (mirror first second : Line K) (point : Point K)
    (mirrorNonNull : ¬ mirror.IsNull)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (mirrorContains : mirror.Contains point)
    (firstContains : first.Contains point)
    (secondContains : second.Contains point)
    (distinct : ¬ first.Equivalent second) :
    (reflectLine mirror first mirrorNonNull).Equivalent second ↔
      spread first mirror firstNonNull mirrorNonNull =
        spread second mirror secondNonNull mirrorNonNull := by
  have firstDenominatorNonzero :
      lineNorm first * lineNorm mirror ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstNonNull mirrorNonNull
  have secondDenominatorNonzero :
      lineNorm second * lineNorm mirror ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero secondNonNull mirrorNonNull
  constructor
  · intro reflectedEquivalent
    have reflectedDeterminantZero :
        reflectedLineA mirror first * second.b -
            second.a * reflectedLineB mirror first = 0 := by
      unfold Line.Equivalent reflectLine at reflectedEquivalent
      calc
        reflectedLineA mirror first * second.b -
            second.a * reflectedLineB mirror first =
          second.a * reflectedLineB mirror first -
            second.a * reflectedLineB mirror first := by
              rw [reflectedEquivalent.1]
        _ = 0 := by ring1
    have balance :
        lineNorm second *
              (first.a * mirror.b - mirror.a * first.b) ^ 2 =
          lineNorm first *
              (second.a * mirror.b - mirror.a * second.b) ^ 2 := by
      have differenceZero :
          lineNorm second *
                (first.a * mirror.b - mirror.a * first.b) ^ 2 -
              lineNorm first *
                (second.a * mirror.b - mirror.a * second.b) ^ 2 = 0 := by
        calc
          lineNorm second *
                (first.a * mirror.b - mirror.a * first.b) ^ 2 -
              lineNorm first *
                (second.a * mirror.b - mirror.a * second.b) ^ 2 =
            -(first.a * second.b - second.a * first.b) *
              (reflectedLineA mirror first * second.b -
                second.a * reflectedLineB mirror first) :=
              reflection_spread_factorization mirror first second
          _ = 0 := by rw [reflectedDeterminantZero]; ring1
      exact sub_eq_zero.mp differenceZero
    unfold spread
    apply ratio_eq_of_cross_product firstDenominatorNonzero
      secondDenominatorNonzero
    calc
      (first.a * mirror.b - mirror.a * first.b) ^ 2 *
          (lineNorm second * lineNorm mirror) =
        (lineNorm second *
          (first.a * mirror.b - mirror.a * first.b) ^ 2) *
            lineNorm mirror := by ring1
      _ = (lineNorm first *
          (second.a * mirror.b - mirror.a * second.b) ^ 2) *
            lineNorm mirror := by rw [balance]
      _ = (second.a * mirror.b - mirror.a * second.b) ^ 2 *
          (lineNorm first * lineNorm mirror) := by ring1
  · intro equalSpreads
    unfold spread at equalSpreads
    have crossProduct := cross_product_of_ratio_eq firstDenominatorNonzero
      secondDenominatorNonzero equalSpreads
    have scaledDifference :
        (lineNorm second *
              (first.a * mirror.b - mirror.a * first.b) ^ 2 -
            lineNorm first *
              (second.a * mirror.b - mirror.a * second.b) ^ 2) *
          lineNorm mirror = 0 := by
      calc
        (lineNorm second *
                (first.a * mirror.b - mirror.a * first.b) ^ 2 -
              lineNorm first *
                (second.a * mirror.b - mirror.a * second.b) ^ 2) *
            lineNorm mirror =
          (first.a * mirror.b - mirror.a * first.b) ^ 2 *
              (lineNorm second * lineNorm mirror) -
            (second.a * mirror.b - mirror.a * second.b) ^ 2 *
              (lineNorm first * lineNorm mirror) := by ring1
        _ = 0 := by rw [crossProduct]; ring1
    have differenceZero :
        lineNorm second *
              (first.a * mirror.b - mirror.a * first.b) ^ 2 -
            lineNorm first *
              (second.a * mirror.b - mirror.a * second.b) ^ 2 = 0 := by
      apply eq_of_mul_eq_mul_right
        (show lineNorm mirror ≠ 0 from mirrorNonNull)
      simpa only [zero_mul] using scaledDifference
    have firstSecondDeterminantNonzero :
        first.a * second.b - second.a * first.b ≠ 0 := by
      intro determinantZero
      apply distinct
      apply line_equivalent_of_parallel_and_common_point first second point
      · exact determinantZero
      · exact firstContains
      · exact secondContains
    have reflectedProductZero :
        (first.a * second.b - second.a * first.b) *
          (reflectedLineA mirror first * second.b -
            second.a * reflectedLineB mirror first) = 0 := by
      calc
        (first.a * second.b - second.a * first.b) *
            (reflectedLineA mirror first * second.b -
              second.a * reflectedLineB mirror first) =
          -(lineNorm second *
                (first.a * mirror.b - mirror.a * first.b) ^ 2 -
              lineNorm first *
                (second.a * mirror.b - mirror.a * second.b) ^ 2) := by
            rw [reflection_spread_factorization mirror first second]
            ring1
        _ = 0 := by rw [differenceZero]; ring1
    have reflectedDeterminantZero :
        reflectedLineA mirror first * second.b -
            second.a * reflectedLineB mirror first = 0 := by
      by_cases determinantZero :
          reflectedLineA mirror first * second.b -
              second.a * reflectedLineB mirror first = 0
      · exact determinantZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero firstSecondDeterminantNonzero
            determinantZero) reflectedProductZero)
    have reflectedParallel :
        (reflectLine mirror first mirrorNonNull).Parallel second := by
      exact reflectedDeterminantZero
    have reflectedContains :
        (reflectLine mirror first mirrorNonNull).Contains point :=
      reflectLine_contains_common_point mirror first mirrorNonNull point
        mirrorContains firstContains
    exact line_equivalent_of_parallel_and_common_point
      (reflectLine mirror first mirrorNonNull) second point reflectedParallel
      reflectedContains secondContains

end DivineProportions
