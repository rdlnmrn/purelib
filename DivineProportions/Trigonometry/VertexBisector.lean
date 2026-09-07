import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Trigonometry.TriangleRatios

/-!
# Divine Proportions, §6.9: vertex bisectors

An explicit witness `r² = ‖l₁‖‖l₂‖` produces the two normalized
bisectors `r l₁ ± ‖l₁‖ l₂`.  This formulation is equivalent to the
book's longer coefficient display, but is symmetric enough that all finite
field cancellations remain visible.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_zero_of_mul_eq_zero_left [DecidableEq K]
    {left right : K} (leftNonzero : left ≠ 0) (productZero : left * right = 0) :
    right = 0 := by
  by_cases rightZero : right = 0
  · exact rightZero
  · exact False.elim
      ((RFAP.ExplicitField.mul_ne_zero leftNonzero rightZero) productZero)

private theorem ratio_eq_of_cross_mul [DecidableEq K]
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
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
          rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

private theorem cross_mul_of_ratio_eq [DecidableEq K]
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
    (productsEqual : left * factor = right * factor) :
    left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by rw [mul_one]
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel, mul_one]

/-- Dividing a nonzero square by a nonzero scalar produces a nonzero square
exactly when that scalar is itself a nonzero square.  Both directions return
the explicit quotient root; no square root is selected. -/
private theorem quotient_square_isNonzeroSquare_iff
    (numerator denominator : K)
    (numeratorNonzero : numerator ≠ 0)
    (denominatorNonzero : denominator ≠ 0) :
    IsNonzeroSquare (numerator ^ 2 / denominator) ↔
      IsNonzeroSquare denominator := by
  constructor
  · rintro ⟨quotientRoot, quotientRootNonzero, quotientEquation⟩
    have clearedEquation :
        numerator ^ 2 = quotientRoot ^ 2 * denominator := by
      calc
        numerator ^ 2 =
            (numerator ^ 2 / denominator) * denominator := by
              exact (RFAP.ExplicitField.div_mul_cancel
                (numerator ^ 2) denominatorNonzero).symm
        _ = quotientRoot ^ 2 * denominator := by rw [quotientEquation]
    have quotientRootSquareNonzero : quotientRoot ^ 2 ≠ 0 := by
      simpa [pow_two] using
        (RFAP.ExplicitField.mul_ne_zero quotientRootNonzero
          quotientRootNonzero)
    refine ⟨numerator / quotientRoot,
      RFAP.ExplicitField.div_ne_zero numeratorNonzero quotientRootNonzero, ?_⟩
    apply eq_of_mul_eq_mul_right quotientRootSquareNonzero
    calc
      denominator * quotientRoot ^ 2 =
          quotientRoot ^ 2 * denominator := by ring1
      _ = numerator ^ 2 := clearedEquation.symm
      _ = ((numerator / quotientRoot) * quotientRoot) ^ 2 := by
        rw [RFAP.ExplicitField.div_mul_cancel numerator quotientRootNonzero]
      _ = (numerator / quotientRoot) ^ 2 * quotientRoot ^ 2 := by ring1
  · rintro ⟨denominatorRoot, denominatorRootNonzero, denominatorEquation⟩
    refine ⟨numerator / denominatorRoot,
      RFAP.ExplicitField.div_ne_zero numeratorNonzero denominatorRootNonzero, ?_⟩
    apply eq_of_mul_eq_mul_right denominatorNonzero
    calc
      (numerator ^ 2 / denominator) * denominator = numerator ^ 2 :=
        RFAP.ExplicitField.div_mul_cancel
          (numerator ^ 2) denominatorNonzero
      _ = ((numerator / denominatorRoot) * denominatorRoot) ^ 2 := by
        rw [RFAP.ExplicitField.div_mul_cancel numerator denominatorRootNonzero]
      _ = (numerator / denominatorRoot) ^ 2 * denominatorRoot ^ 2 := by ring1
      _ = (numerator / denominatorRoot) ^ 2 * denominator := by
        rw [denominatorEquation]

private theorem determinant_ne_zero_of_not_parallel
    {first second : Line K} (notParallel : ¬ first.Parallel second) :
    first.a * second.b - second.a * first.b ≠ 0 := notParallel

/-- The square condition in Theorem 45, expressed in the two equivalent
finite forms used by the book and by the normalized construction. -/
theorem spread_isNonzeroSquare_iff_normProduct_isNonzeroSquare
    (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second) :
    IsNonzeroSquare (spread first second firstNonNull secondNonNull) ↔
      IsNonzeroSquare (lineNorm first * lineNorm second) := by
  unfold spread
  exact quotient_square_isNonzeroSquare_iff
    (first.a * second.b - second.a * first.b)
    (lineNorm first * lineNorm second)
    (determinant_ne_zero_of_not_parallel notParallel)
    (RFAP.ExplicitField.mul_ne_zero firstNonNull secondNonNull)

private theorem positiveBisector_direction_nonzero [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second) :
    root * first.a + lineNorm first * second.a ≠ 0 ∨
      root * first.b + lineNorm first * second.b ≠ 0 := by
  by_cases aNonzero :
      root * first.a + lineNorm first * second.a ≠ 0
  · exact Or.inl aNonzero
  · by_cases bNonzero :
        root * first.b + lineNorm first * second.b ≠ 0
    · exact Or.inr bNonzero
    · have aZero : root * first.a + lineNorm first * second.a = 0 := by
        by_cases equality : root * first.a + lineNorm first * second.a = 0
        · exact equality
        · exact False.elim (aNonzero equality)
      have bZero : root * first.b + lineNorm first * second.b = 0 := by
        by_cases equality : root * first.b + lineNorm first * second.b = 0
        · exact equality
        · exact False.elim (bNonzero equality)
      have normNonzero : lineNorm first ≠ 0 := firstNonNull
      have determinantNonzero :=
        determinant_ne_zero_of_not_parallel notParallel
      have productNonzero :=
        RFAP.ExplicitField.mul_ne_zero normNonzero determinantNonzero
      exact False.elim (productNonzero (by
        calc
          lineNorm first *
              (first.a * second.b - second.a * first.b) =
            first.a *
                (root * first.b + lineNorm first * second.b) -
              (root * first.a + lineNorm first * second.a) * first.b := by ring1
          _ = 0 := by rw [aZero, bZero]; ring1))

private theorem negativeBisector_direction_nonzero [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second) :
    root * first.a - lineNorm first * second.a ≠ 0 ∨
      root * first.b - lineNorm first * second.b ≠ 0 := by
  by_cases aNonzero :
      root * first.a - lineNorm first * second.a ≠ 0
  · exact Or.inl aNonzero
  · by_cases bNonzero :
        root * first.b - lineNorm first * second.b ≠ 0
    · exact Or.inr bNonzero
    · have aZero : root * first.a - lineNorm first * second.a = 0 := by
        by_cases equality : root * first.a - lineNorm first * second.a = 0
        · exact equality
        · exact False.elim (aNonzero equality)
      have bZero : root * first.b - lineNorm first * second.b = 0 := by
        by_cases equality : root * first.b - lineNorm first * second.b = 0
        · exact equality
        · exact False.elim (bNonzero equality)
      have normNonzero : lineNorm first ≠ 0 := firstNonNull
      have determinantNonzero :=
        determinant_ne_zero_of_not_parallel notParallel
      have productNonzero :=
        RFAP.ExplicitField.mul_ne_zero normNonzero determinantNonzero
      exact False.elim (productNonzero (by
        calc
          lineNorm first *
              (first.a * second.b - second.a * first.b) =
            -first.a *
                (root * first.b - lineNorm first * second.b) +
              (root * first.a - lineNorm first * second.a) * first.b := by ring1
          _ = 0 := by rw [aZero, bZero]; ring1))

/-- The positive normalized vertex-bisector candidate. -/
def positiveVertexBisector [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second) :
    Line K where
  a := root * first.a + lineNorm first * second.a
  b := root * first.b + lineNorm first * second.b
  c := root * first.c + lineNorm first * second.c
  direction_nonzero :=
    positiveBisector_direction_nonzero first second root firstNonNull notParallel

/-- The negative normalized vertex-bisector candidate. -/
def negativeVertexBisector [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second) :
    Line K where
  a := root * first.a - lineNorm first * second.a
  b := root * first.b - lineNorm first * second.b
  c := root * first.c - lineNorm first * second.c
  direction_nonzero :=
    negativeBisector_direction_nonzero first second root firstNonNull notParallel

private theorem root_ne_zero
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (rootEquation : root ^ 2 = lineNorm first * lineNorm second) :
    root ≠ 0 := by
  intro rootZero
  have productNonzero := RFAP.ExplicitField.mul_ne_zero
    (show lineNorm first ≠ 0 from firstNonNull)
    (show lineNorm second ≠ 0 from secondNonNull)
  apply productNonzero
  calc
    lineNorm first * lineNorm second = root ^ 2 := rootEquation.symm
    _ = 0 := by rw [rootZero]; ring1

private theorem determinant_square_add_dot_square
    (first second : Line K) :
    (first.a * second.b - second.a * first.b) ^ 2 +
      (first.a * second.a + first.b * second.b) ^ 2 =
        lineNorm first * lineNorm second := by
  unfold lineNorm
  ring1

theorem positiveVertexBisector_norm [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second)
    (rootEquation : root ^ 2 = lineNorm first * lineNorm second) :
    lineNorm (positiveVertexBisector first second root firstNonNull notParallel) =
      2 * lineNorm first * root *
        (root + (first.a * second.a + first.b * second.b)) := by
  unfold lineNorm positiveVertexBisector
  change
    (root * first.a + (first.a ^ 2 + first.b ^ 2) * second.a) ^ 2 +
      (root * first.b + (first.a ^ 2 + first.b ^ 2) * second.b) ^ 2 =
    2 * (first.a ^ 2 + first.b ^ 2) * root *
      (root + (first.a * second.a + first.b * second.b))
  calc
    (root * first.a + (first.a ^ 2 + first.b ^ 2) * second.a) ^ 2 +
        (root * first.b + (first.a ^ 2 + first.b ^ 2) * second.b) ^ 2 =
      root ^ 2 * (first.a ^ 2 + first.b ^ 2) +
        2 * root * (first.a ^ 2 + first.b ^ 2) *
          (first.a * second.a + first.b * second.b) +
        (first.a ^ 2 + first.b ^ 2) ^ 2 *
          (second.a ^ 2 + second.b ^ 2) := by ring1
    _ = 2 * (first.a ^ 2 + first.b ^ 2) *
        (root ^ 2 + root *
          (first.a * second.a + first.b * second.b)) := by
            rw [rootEquation]
            unfold lineNorm
            ring1
    _ = 2 * (first.a ^ 2 + first.b ^ 2) * root *
        (root + (first.a * second.a + first.b * second.b)) := by ring1

theorem negativeVertexBisector_norm [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second)
    (rootEquation : root ^ 2 = lineNorm first * lineNorm second) :
    lineNorm (negativeVertexBisector first second root firstNonNull notParallel) =
      2 * lineNorm first * root *
        (root - (first.a * second.a + first.b * second.b)) := by
  unfold lineNorm negativeVertexBisector
  change
    (root * first.a - (first.a ^ 2 + first.b ^ 2) * second.a) ^ 2 +
      (root * first.b - (first.a ^ 2 + first.b ^ 2) * second.b) ^ 2 =
    2 * (first.a ^ 2 + first.b ^ 2) * root *
      (root - (first.a * second.a + first.b * second.b))
  calc
    (root * first.a - (first.a ^ 2 + first.b ^ 2) * second.a) ^ 2 +
        (root * first.b - (first.a ^ 2 + first.b ^ 2) * second.b) ^ 2 =
      root ^ 2 * (first.a ^ 2 + first.b ^ 2) -
        2 * root * (first.a ^ 2 + first.b ^ 2) *
          (first.a * second.a + first.b * second.b) +
        (first.a ^ 2 + first.b ^ 2) ^ 2 *
          (second.a ^ 2 + second.b ^ 2) := by ring1
    _ = 2 * (first.a ^ 2 + first.b ^ 2) *
        (root ^ 2 - root *
          (first.a * second.a + first.b * second.b)) := by
            rw [rootEquation]
            unfold lineNorm
            ring1
    _ = 2 * (first.a ^ 2 + first.b ^ 2) * root *
        (root - (first.a * second.a + first.b * second.b)) := by ring1

private theorem root_add_dot_ne_zero [DecidableEq K]
    (first second : Line K) (root : K)
    (notParallel : ¬ first.Parallel second)
    (rootEquation : root ^ 2 = lineNorm first * lineNorm second) :
    root + (first.a * second.a + first.b * second.b) ≠ 0 := by
  intro sumZero
  have determinantNonzero := determinant_ne_zero_of_not_parallel notParallel
  apply (RFAP.ExplicitField.mul_ne_zero determinantNonzero determinantNonzero)
  have fibonacci := determinant_square_add_dot_square first second
  calc
    (first.a * second.b - second.a * first.b) *
        (first.a * second.b - second.a * first.b) =
      (first.a * second.b - second.a * first.b) ^ 2 := by ring1
    _ = lineNorm first * lineNorm second -
        (first.a * second.a + first.b * second.b) ^ 2 := by
          calc
            (first.a * second.b - second.a * first.b) ^ 2 =
              ((first.a * second.b - second.a * first.b) ^ 2 +
                (first.a * second.a + first.b * second.b) ^ 2) -
                (first.a * second.a + first.b * second.b) ^ 2 := by ring1
            _ = lineNorm first * lineNorm second -
                (first.a * second.a + first.b * second.b) ^ 2 := by rw [fibonacci]
    _ = root ^ 2 - (first.a * second.a + first.b * second.b) ^ 2 := by
      rw [← rootEquation]
    _ = 0 := by
      have dotValue : first.a * second.a + first.b * second.b = -root := by
        calc
          first.a * second.a + first.b * second.b =
              (root + (first.a * second.a + first.b * second.b)) - root := by
                ring1
          _ = -root := by rw [sumZero]; ring1
      rw [dotValue]
      ring1

private theorem root_sub_dot_ne_zero [DecidableEq K]
    (first second : Line K) (root : K)
    (notParallel : ¬ first.Parallel second)
    (rootEquation : root ^ 2 = lineNorm first * lineNorm second) :
    root - (first.a * second.a + first.b * second.b) ≠ 0 := by
  intro differenceZero
  have determinantNonzero := determinant_ne_zero_of_not_parallel notParallel
  apply (RFAP.ExplicitField.mul_ne_zero determinantNonzero determinantNonzero)
  have fibonacci := determinant_square_add_dot_square first second
  calc
    (first.a * second.b - second.a * first.b) *
        (first.a * second.b - second.a * first.b) =
      (first.a * second.b - second.a * first.b) ^ 2 := by ring1
    _ = lineNorm first * lineNorm second -
        (first.a * second.a + first.b * second.b) ^ 2 := by
          calc
            (first.a * second.b - second.a * first.b) ^ 2 =
              ((first.a * second.b - second.a * first.b) ^ 2 +
                (first.a * second.a + first.b * second.b) ^ 2) -
                (first.a * second.a + first.b * second.b) ^ 2 := by ring1
            _ = lineNorm first * lineNorm second -
                (first.a * second.a + first.b * second.b) ^ 2 := by rw [fibonacci]
    _ = root ^ 2 - (first.a * second.a + first.b * second.b) ^ 2 := by
      rw [← rootEquation]
    _ = 0 := by
      have dotValue : first.a * second.a + first.b * second.b = root := by
        calc
          first.a * second.a + first.b * second.b =
              root - (root -
                (first.a * second.a + first.b * second.b)) := by ring1
          _ = root := by rw [differenceZero]; ring1
      rw [dotValue]
      ring1

theorem positiveVertexBisector_nonNull [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation : root ^ 2 = lineNorm first * lineNorm second) :
    ¬ (positiveVertexBisector first second root firstNonNull notParallel).IsNull := by
  have normNonzero : lineNorm first ≠ 0 := firstNonNull
  have rootNonzero :=
    root_ne_zero first second root firstNonNull secondNonNull rootEquation
  have sumNonzero :=
    root_add_dot_ne_zero first second root notParallel rootEquation
  rw [line_isNull_iff_norm_eq_zero,
    positiveVertexBisector_norm first second root firstNonNull notParallel
      rootEquation]
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero twoNonzero normNonzero) rootNonzero)
    sumNonzero

theorem negativeVertexBisector_nonNull [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation : root ^ 2 = lineNorm first * lineNorm second) :
    ¬ (negativeVertexBisector first second root firstNonNull notParallel).IsNull := by
  have normNonzero : lineNorm first ≠ 0 := firstNonNull
  have rootNonzero :=
    root_ne_zero first second root firstNonNull secondNonNull rootEquation
  have differenceNonzero :=
    root_sub_dot_ne_zero first second root notParallel rootEquation
  rw [line_isNull_iff_norm_eq_zero,
    negativeVertexBisector_norm first second root firstNonNull notParallel
      rootEquation]
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero twoNonzero normNonzero) rootNonzero)
    differenceNonzero

theorem vertexBisectors_perpendicular [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second)
    (rootEquation : root ^ 2 = lineNorm first * lineNorm second) :
    (positiveVertexBisector first second root firstNonNull notParallel).Perpendicular
      (negativeVertexBisector first second root firstNonNull notParallel) := by
  unfold Line.Perpendicular positiveVertexBisector negativeVertexBisector
  change
    (root * first.a + lineNorm first * second.a) *
        (root * first.a - lineNorm first * second.a) +
      (root * first.b + lineNorm first * second.b) *
        (root * first.b - lineNorm first * second.b) = 0
  calc
    (root * first.a + lineNorm first * second.a) *
          (root * first.a - lineNorm first * second.a) +
        (root * first.b + lineNorm first * second.b) *
          (root * first.b - lineNorm first * second.b) =
      root ^ 2 * lineNorm first -
        lineNorm first ^ 2 * lineNorm second := by
          unfold lineNorm
          ring1
    _ = 0 := by rw [rootEquation]; ring1

/-- The book's definition of a bisector of the non-null, nonparallel vertex
`first second`.  The vertex is the explicitly computed line intersection, and
the non-null witness keeps both spread denominators executable. -/
def IsVertexBisector [DecidableEq K]
    (first second bisector : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second) : Prop :=
  ∃ bisectorNonNull : ¬ bisector.IsNull,
    bisector.Contains (lineIntersection first second notParallel) ∧
      spread first bisector firstNonNull bisectorNonNull =
        spread second bisector secondNonNull bisectorNonNull

theorem positiveVertexBisector_contains_common_point [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second)
    (point : Point K) (onFirst : first.Contains point)
    (onSecond : second.Contains point) :
    (positiveVertexBisector first second root firstNonNull notParallel).Contains point := by
  unfold Line.Contains at onFirst onSecond ⊢
  unfold positiveVertexBisector
  calc
    (root * first.a + lineNorm first * second.a) * point.x +
        (root * first.b + lineNorm first * second.b) * point.y +
        (root * first.c + lineNorm first * second.c) =
      root * (first.a * point.x + first.b * point.y + first.c) +
        lineNorm first *
          (second.a * point.x + second.b * point.y + second.c) := by ring1
    _ = 0 := by rw [onFirst, onSecond]; ring1

theorem negativeVertexBisector_contains_common_point [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second)
    (point : Point K) (onFirst : first.Contains point)
    (onSecond : second.Contains point) :
    (negativeVertexBisector first second root firstNonNull notParallel).Contains point := by
  unfold Line.Contains at onFirst onSecond ⊢
  unfold negativeVertexBisector
  calc
    (root * first.a - lineNorm first * second.a) * point.x +
        (root * first.b - lineNorm first * second.b) * point.y +
        (root * first.c - lineNorm first * second.c) =
      root * (first.a * point.x + first.b * point.y + first.c) -
        lineNorm first *
          (second.a * point.x + second.b * point.y + second.c) := by ring1
    _ = 0 := by rw [onFirst, onSecond]; ring1

theorem positiveVertexBisector_equal_spreads [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation : root ^ 2 = lineNorm first * lineNorm second) :
    let bisector := positiveVertexBisector first second root firstNonNull notParallel
    let bisectorNonNull := positiveVertexBisector_nonNull first second root
      firstNonNull secondNonNull notParallel twoNonzero rootEquation
    spread first bisector firstNonNull bisectorNonNull =
      spread second bisector secondNonNull bisectorNonNull := by
  dsimp only
  let bisector := positiveVertexBisector first second root firstNonNull notParallel
  have bisectorNonNull := positiveVertexBisector_nonNull first second root
    firstNonNull secondNonNull notParallel twoNonzero rootEquation
  have firstDenominatorNonzero : lineNorm first * lineNorm bisector ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstNonNull bisectorNonNull
  have secondDenominatorNonzero : lineNorm second * lineNorm bisector ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero secondNonNull bisectorNonNull
  have firstNumerator :
      (first.a * bisector.b - bisector.a * first.b) ^ 2 =
        (lineNorm first *
          (first.a * second.b - second.a * first.b)) ^ 2 := by
    unfold bisector positiveVertexBisector
    ring1
  have secondNumerator :
      (second.a * bisector.b - bisector.a * second.b) ^ 2 =
        (root * (first.a * second.b - second.a * first.b)) ^ 2 := by
    unfold bisector positiveVertexBisector
    ring1
  unfold spread
  apply ratio_eq_of_cross_mul
    firstDenominatorNonzero secondDenominatorNonzero
  rw [firstNumerator, secondNumerator]
  calc
    (lineNorm first *
          (first.a * second.b - second.a * first.b)) ^ 2 *
        (lineNorm second * lineNorm bisector) =
      lineNorm first ^ 2 * lineNorm second *
        (first.a * second.b - second.a * first.b) ^ 2 *
          lineNorm bisector := by ring1
    _ = root ^ 2 * lineNorm first *
        (first.a * second.b - second.a * first.b) ^ 2 *
          lineNorm bisector := by rw [rootEquation]; ring1
    _ = (root * (first.a * second.b - second.a * first.b)) ^ 2 *
        (lineNorm first * lineNorm bisector) := by ring1

theorem negativeVertexBisector_equal_spreads [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation : root ^ 2 = lineNorm first * lineNorm second) :
    let bisector := negativeVertexBisector first second root firstNonNull notParallel
    let bisectorNonNull := negativeVertexBisector_nonNull first second root
      firstNonNull secondNonNull notParallel twoNonzero rootEquation
    spread first bisector firstNonNull bisectorNonNull =
      spread second bisector secondNonNull bisectorNonNull := by
  dsimp only
  let bisector := negativeVertexBisector first second root firstNonNull notParallel
  have bisectorNonNull := negativeVertexBisector_nonNull first second root
    firstNonNull secondNonNull notParallel twoNonzero rootEquation
  have firstDenominatorNonzero : lineNorm first * lineNorm bisector ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstNonNull bisectorNonNull
  have secondDenominatorNonzero : lineNorm second * lineNorm bisector ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero secondNonNull bisectorNonNull
  have firstNumerator :
      (first.a * bisector.b - bisector.a * first.b) ^ 2 =
        (lineNorm first *
          (first.a * second.b - second.a * first.b)) ^ 2 := by
    unfold bisector negativeVertexBisector
    ring1
  have secondNumerator :
      (second.a * bisector.b - bisector.a * second.b) ^ 2 =
        (root * (first.a * second.b - second.a * first.b)) ^ 2 := by
    unfold bisector negativeVertexBisector
    ring1
  unfold spread
  apply ratio_eq_of_cross_mul
    firstDenominatorNonzero secondDenominatorNonzero
  rw [firstNumerator, secondNumerator]
  calc
    (lineNorm first *
          (first.a * second.b - second.a * first.b)) ^ 2 *
        (lineNorm second * lineNorm bisector) =
      lineNorm first ^ 2 * lineNorm second *
        (first.a * second.b - second.a * first.b) ^ 2 *
          lineNorm bisector := by ring1
    _ = root ^ 2 * lineNorm first *
        (first.a * second.b - second.a * first.b) ^ 2 *
          lineNorm bisector := by rw [rootEquation]; ring1
    _ = (root * (first.a * second.b - second.a * first.b)) ^ 2 *
        (lineNorm first * lineNorm bisector) := by ring1

/-- The positive explicit candidate satisfies the book's bisector
definition. -/
theorem positiveVertexBisector_isVertexBisector [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation : root ^ 2 = lineNorm first * lineNorm second) :
    IsVertexBisector first second
      (positiveVertexBisector first second root firstNonNull notParallel)
      firstNonNull secondNonNull notParallel := by
  let bisectorNonNull := positiveVertexBisector_nonNull first second root
    firstNonNull secondNonNull notParallel twoNonzero rootEquation
  refine ⟨bisectorNonNull, ?_, ?_⟩
  · exact positiveVertexBisector_contains_common_point first second root
      firstNonNull notParallel (lineIntersection first second notParallel)
      (lineIntersection_on_first first second notParallel)
      (lineIntersection_on_second first second notParallel)
  · exact positiveVertexBisector_equal_spreads first second root
      firstNonNull secondNonNull notParallel twoNonzero rootEquation

/-- The negative explicit candidate satisfies the book's bisector
definition. -/
theorem negativeVertexBisector_isVertexBisector [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation : root ^ 2 = lineNorm first * lineNorm second) :
    IsVertexBisector first second
      (negativeVertexBisector first second root firstNonNull notParallel)
      firstNonNull secondNonNull notParallel := by
  let bisectorNonNull := negativeVertexBisector_nonNull first second root
    firstNonNull secondNonNull notParallel twoNonzero rootEquation
  refine ⟨bisectorNonNull, ?_, ?_⟩
  · exact negativeVertexBisector_contains_common_point first second root
      firstNonNull notParallel (lineIntersection first second notParallel)
      (lineIntersection_on_first first second notParallel)
      (lineIntersection_on_second first second notParallel)
  · exact negativeVertexBisector_equal_spreads first second root
      firstNonNull secondNonNull notParallel twoNonzero rootEquation

private theorem equal_spreads_norm_balance [DecidableEq K]
    (first second bisector : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (bisectorNonNull : ¬ bisector.IsNull)
    (equalSpreads :
      spread first bisector firstNonNull bisectorNonNull =
        spread second bisector secondNonNull bisectorNonNull) :
    lineNorm second *
          (first.a * bisector.b - bisector.a * first.b) ^ 2 =
      lineNorm first *
          (second.a * bisector.b - bisector.a * second.b) ^ 2 := by
  have firstDenominatorNonzero :
      lineNorm first * lineNorm bisector ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstNonNull bisectorNonNull
  have secondDenominatorNonzero :
      lineNorm second * lineNorm bisector ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero secondNonNull bisectorNonNull
  unfold spread at equalSpreads
  have crossProduct := cross_mul_of_ratio_eq
    firstDenominatorNonzero secondDenominatorNonzero equalSpreads
  have scaledDifference :
      (lineNorm second *
          (first.a * bisector.b - bisector.a * first.b) ^ 2 -
        lineNorm first *
          (second.a * bisector.b - bisector.a * second.b) ^ 2) *
        lineNorm bisector = 0 := by
    calc
      (lineNorm second *
            (first.a * bisector.b - bisector.a * first.b) ^ 2 -
          lineNorm first *
            (second.a * bisector.b - bisector.a * second.b) ^ 2) *
          lineNorm bisector =
        (first.a * bisector.b - bisector.a * first.b) ^ 2 *
            (lineNorm second * lineNorm bisector) -
          (second.a * bisector.b - bisector.a * second.b) ^ 2 *
            (lineNorm first * lineNorm bisector) := by ring1
      _ = 0 := by rw [crossProduct]; ring1
  have differenceZero :
      lineNorm second *
          (first.a * bisector.b - bisector.a * first.b) ^ 2 -
        lineNorm first *
          (second.a * bisector.b - bisector.a * second.b) ^ 2 = 0 := by
    apply eq_of_mul_eq_mul_right
      (show lineNorm bisector ≠ 0 from bisectorNonNull)
    simpa only [zero_mul] using scaledDifference
  calc
    lineNorm second *
          (first.a * bisector.b - bisector.a * first.b) ^ 2 =
      (lineNorm second *
          (first.a * bisector.b - bisector.a * first.b) ^ 2 -
        lineNorm first *
          (second.a * bisector.b - bisector.a * second.b) ^ 2) +
        lineNorm first *
          (second.a * bisector.b - bisector.a * second.b) ^ 2 := by ring1
    _ = lineNorm first *
          (second.a * bisector.b - bisector.a * second.b) ^ 2 := by
      rw [differenceZero]
      ring1

/-- Two displayed equal-spread bisectors of the same nonparallel pair are
parallel or perpendicular.  This quotient-free algebraic form is stronger
than the incidence-specific observation used in Theorem 58. -/
theorem equal_spread_lines_parallel_or_perpendicular [DecidableEq K]
    (first second left right : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (leftNonNull : ¬ left.IsNull) (rightNonNull : ¬ right.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (leftEqual :
      spread first left firstNonNull leftNonNull =
        spread second left secondNonNull leftNonNull)
    (rightEqual :
      spread first right firstNonNull rightNonNull =
        spread second right secondNonNull rightNonNull) :
    left.Parallel right ∨ left.Perpendicular right := by
  let firstSecondDeterminant :=
    first.a * second.b - second.a * first.b
  let traceCoefficient :=
    -(first.a * second.b + first.b * second.a)
  let mixedCoefficient :=
    first.a * second.a - first.b * second.b
  let bisectorForm := fun candidate : Line K =>
    traceCoefficient * (candidate.a ^ 2 - candidate.b ^ 2) +
      2 * mixedCoefficient * candidate.a * candidate.b
  have determinantNonzero : firstSecondDeterminant ≠ 0 := notParallel
  have formZero (candidate : Line K)
      (candidateNonNull : ¬ candidate.IsNull)
      (equalSpreads :
        spread first candidate firstNonNull candidateNonNull =
          spread second candidate secondNonNull candidateNonNull) :
      bisectorForm candidate = 0 := by
    have balance := equal_spreads_norm_balance first second candidate
      firstNonNull secondNonNull candidateNonNull equalSpreads
    have differenceZero :
        lineNorm second *
              (first.a * candidate.b - candidate.a * first.b) ^ 2 -
            lineNorm first *
              (second.a * candidate.b - candidate.a * second.b) ^ 2 = 0 := by
      rw [balance]
      ring1
    have factored :
        firstSecondDeterminant * bisectorForm candidate = 0 := by
      calc
        firstSecondDeterminant * bisectorForm candidate =
            lineNorm second *
                (first.a * candidate.b - candidate.a * first.b) ^ 2 -
              lineNorm first *
                (second.a * candidate.b - candidate.a * second.b) ^ 2 := by
          unfold firstSecondDeterminant bisectorForm traceCoefficient
            mixedCoefficient lineNorm
          ring1
        _ = 0 := differenceZero
    by_cases formIsZero : bisectorForm candidate = 0
    · exact formIsZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero determinantNonzero formIsZero)
          factored)
  have leftFormZero := formZero left leftNonNull leftEqual
  have rightFormZero := formZero right rightNonNull rightEqual
  let betweenDeterminant := left.a * right.b - right.a * left.b
  let betweenDot := left.a * right.a + left.b * right.b
  have traceTimesProductZero :
      traceCoefficient * (betweenDeterminant * betweenDot) = 0 := by
    calc
      traceCoefficient * (betweenDeterminant * betweenDot) =
          bisectorForm left * right.a * right.b -
            bisectorForm right * left.a * left.b := by
        unfold bisectorForm betweenDeterminant betweenDot
        ring1
      _ = 0 := by rw [leftFormZero, rightFormZero]; ring1
  have twiceMixedTimesProductZero :
      2 * (mixedCoefficient * (betweenDeterminant * betweenDot)) = 0 := by
    calc
      2 * (mixedCoefficient * (betweenDeterminant * betweenDot)) =
          -(bisectorForm left * (right.a ^ 2 - right.b ^ 2) -
            bisectorForm right * (left.a ^ 2 - left.b ^ 2)) := by
        unfold bisectorForm betweenDeterminant betweenDot
        ring1
      _ = 0 := by rw [leftFormZero, rightFormZero]; ring1
  have mixedTimesProductZero :
      mixedCoefficient * (betweenDeterminant * betweenDot) = 0 := by
    by_cases productZero :
        mixedCoefficient * (betweenDeterminant * betweenDot) = 0
    · exact productZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero twoNonzero productZero)
          twiceMixedTimesProductZero)
  have coefficientSquares :
      traceCoefficient ^ 2 + mixedCoefficient ^ 2 =
        lineNorm first * lineNorm second := by
    unfold traceCoefficient mixedCoefficient lineNorm
    ring1
  have normTimesProductZero :
      (lineNorm first * lineNorm second) *
        (betweenDeterminant * betweenDot) = 0 := by
    calc
      (lineNorm first * lineNorm second) *
          (betweenDeterminant * betweenDot) =
        traceCoefficient *
            (traceCoefficient * (betweenDeterminant * betweenDot)) +
          mixedCoefficient *
            (mixedCoefficient * (betweenDeterminant * betweenDot)) := by
              rw [← coefficientSquares]
              ring1
      _ = 0 := by
        rw [traceTimesProductZero, mixedTimesProductZero]
        ring1
  have betweenProductZero : betweenDeterminant * betweenDot = 0 := by
    have normProductNonzero : lineNorm first * lineNorm second ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero firstNonNull secondNonNull
    by_cases productZero : betweenDeterminant * betweenDot = 0
    · exact productZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero normProductNonzero productZero)
          normTimesProductZero)
  by_cases determinantZero : betweenDeterminant = 0
  · left
    exact determinantZero
  · right
    by_cases dotZero : betweenDot = 0
    · exact dotZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero determinantZero dotZero)
          betweenProductZero)

/-- Classification clause of Theorem 45: once a displayed square root is
supplied, every bisector is one of the two normalized candidates, up to the
book's equality of ordered proportions. -/
theorem vertex_bisector_classification [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (rootEquation : root ^ 2 = lineNorm first * lineNorm second)
    (bisector : Line K)
    (isBisector : IsVertexBisector first second bisector
      firstNonNull secondNonNull notParallel) :
    bisector.Equivalent
        (positiveVertexBisector first second root firstNonNull notParallel) ∨
      bisector.Equivalent
        (negativeVertexBisector first second root firstNonNull notParallel) := by
  rcases isBisector with
    ⟨bisectorNonNull, bisectorContainsVertex, equalSpreads⟩
  have normBalance := equal_spreads_norm_balance first second bisector
    firstNonNull secondNonNull bisectorNonNull equalSpreads
  have factorProduct :
      (root * (first.a * bisector.b - bisector.a * first.b) -
          lineNorm first *
            (second.a * bisector.b - bisector.a * second.b)) *
        (root * (first.a * bisector.b - bisector.a * first.b) +
          lineNorm first *
            (second.a * bisector.b - bisector.a * second.b)) = 0 := by
    calc
      (root * (first.a * bisector.b - bisector.a * first.b) -
            lineNorm first *
              (second.a * bisector.b - bisector.a * second.b)) *
          (root * (first.a * bisector.b - bisector.a * first.b) +
            lineNorm first *
              (second.a * bisector.b - bisector.a * second.b)) =
        root ^ 2 *
            (first.a * bisector.b - bisector.a * first.b) ^ 2 -
          lineNorm first ^ 2 *
            (second.a * bisector.b - bisector.a * second.b) ^ 2 := by ring1
      _ =
        lineNorm first *
          (lineNorm second *
              (first.a * bisector.b - bisector.a * first.b) ^ 2 -
            lineNorm first *
              (second.a * bisector.b - bisector.a * second.b) ^ 2) := by
        rw [rootEquation]
        ring1
      _ = 0 := by rw [normBalance]; ring1
  let vertex := lineIntersection first second notParallel
  have firstContainsVertex : first.Contains vertex :=
    lineIntersection_on_first first second notParallel
  have secondContainsVertex : second.Contains vertex :=
    lineIntersection_on_second first second notParallel
  by_cases negativeFactorZero :
      root * (first.a * bisector.b - bisector.a * first.b) -
          lineNorm first *
            (second.a * bisector.b - bisector.a * second.b) = 0
  · right
    have candidateParallel :
        (negativeVertexBisector first second root firstNonNull notParallel).Parallel
          bisector := by
      unfold Line.Parallel negativeVertexBisector
      calc
        (root * first.a - lineNorm first * second.a) * bisector.b -
            bisector.a *
              (root * first.b - lineNorm first * second.b) =
          root * (first.a * bisector.b - bisector.a * first.b) -
            lineNorm first *
              (second.a * bisector.b - bisector.a * second.b) := by ring1
        _ = 0 := negativeFactorZero
    have candidateContainsVertex :
        (negativeVertexBisector first second root firstNonNull notParallel).Contains
          vertex :=
      negativeVertexBisector_contains_common_point first second root
        firstNonNull notParallel vertex firstContainsVertex secondContainsVertex
    exact Line.equivalent_symm
      (line_equivalent_of_parallel_and_common_point
        (negativeVertexBisector first second root firstNonNull notParallel)
        bisector vertex candidateParallel candidateContainsVertex
        bisectorContainsVertex)
  · left
    have positiveFactorZero :
        root * (first.a * bisector.b - bisector.a * first.b) +
            lineNorm first *
              (second.a * bisector.b - bisector.a * second.b) = 0 := by
      by_cases factorZero :
          root * (first.a * bisector.b - bisector.a * first.b) +
              lineNorm first *
                (second.a * bisector.b - bisector.a * second.b) = 0
      · exact factorZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero negativeFactorZero factorZero)
            factorProduct)
    have candidateParallel :
        (positiveVertexBisector first second root firstNonNull notParallel).Parallel
          bisector := by
      unfold Line.Parallel positiveVertexBisector
      calc
        (root * first.a + lineNorm first * second.a) * bisector.b -
            bisector.a *
              (root * first.b + lineNorm first * second.b) =
          root * (first.a * bisector.b - bisector.a * first.b) +
            lineNorm first *
              (second.a * bisector.b - bisector.a * second.b) := by ring1
        _ = 0 := positiveFactorZero
    have candidateContainsVertex :
        (positiveVertexBisector first second root firstNonNull notParallel).Contains
          vertex :=
      positiveVertexBisector_contains_common_point first second root
        firstNonNull notParallel vertex firstContainsVertex secondContainsVertex
    exact Line.equivalent_symm
      (line_equivalent_of_parallel_and_common_point
        (positiveVertexBisector first second root firstNonNull notParallel)
        bisector vertex candidateParallel candidateContainsVertex
        bisectorContainsVertex)

/-- Equal spreads against a non-null third line explicitly exhibit the
product of the first two line norms as a square.  The returned root is
`‖first‖ det(second,bisector) / det(first,bisector)`. -/
theorem normProduct_isNonzeroSquare_of_equal_spreads [DecidableEq K]
    (first second bisector : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (bisectorNonNull : ¬ bisector.IsNull)
    (notParallel : ¬ first.Parallel second)
    (equalSpreads :
      spread first bisector firstNonNull bisectorNonNull =
        spread second bisector secondNonNull bisectorNonNull) :
    IsNonzeroSquare (lineNorm first * lineNorm second) := by
  let firstCross := first.a * bisector.b - bisector.a * first.b
  let secondCross := second.a * bisector.b - bisector.a * second.b
  have normBalance :
      lineNorm second * firstCross ^ 2 =
        lineNorm first * secondCross ^ 2 := by
    exact equal_spreads_norm_balance first second bisector firstNonNull
      secondNonNull bisectorNonNull equalSpreads
  have firstCrossNonzero : firstCross ≠ 0 := by
    intro firstCrossZero
    have secondCrossSquareZero : secondCross ^ 2 = 0 := by
      have scaledZero : lineNorm first * secondCross ^ 2 = 0 := by
        calc
          lineNorm first * secondCross ^ 2 =
              lineNorm second * firstCross ^ 2 := normBalance.symm
          _ = 0 := by rw [firstCrossZero]; ring1
      exact eq_zero_of_mul_eq_zero_left firstNonNull scaledZero
    have secondCrossZero : secondCross = 0 := by
      by_cases crossZero : secondCross = 0
      · exact crossZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero crossZero crossZero) (by
            simpa [pow_two] using secondCrossSquareZero))
    have determinantTimesNormZero :
        (first.a * second.b - second.a * first.b) *
          lineNorm bisector = 0 := by
      calc
        (first.a * second.b - second.a * first.b) *
            lineNorm bisector =
          firstCross *
              (second.a * bisector.a + second.b * bisector.b) -
            secondCross *
              (first.a * bisector.a + first.b * bisector.b) := by
                unfold firstCross secondCross lineNorm
                ring1
        _ = 0 := by rw [firstCrossZero, secondCrossZero]; ring1
    exact (RFAP.ExplicitField.mul_ne_zero
      (determinant_ne_zero_of_not_parallel notParallel)
      (show lineNorm bisector ≠ 0 from bisectorNonNull))
      determinantTimesNormZero
  have secondCrossNonzero : secondCross ≠ 0 := by
    intro secondCrossZero
    have firstCrossSquareNonzero : firstCross ^ 2 ≠ 0 := by
      simpa [pow_two] using
        (RFAP.ExplicitField.mul_ne_zero firstCrossNonzero firstCrossNonzero)
    exact (RFAP.ExplicitField.mul_ne_zero secondNonNull
      firstCrossSquareNonzero) (by
        calc
          lineNorm second * firstCross ^ 2 =
              lineNorm first * secondCross ^ 2 := normBalance
          _ = 0 := by rw [secondCrossZero]; ring1)
  have firstCrossSquareNonzero : firstCross ^ 2 ≠ 0 := by
    simpa [pow_two] using
      (RFAP.ExplicitField.mul_ne_zero firstCrossNonzero firstCrossNonzero)
  refine ⟨lineNorm first * secondCross / firstCross,
    RFAP.ExplicitField.div_ne_zero
      (RFAP.ExplicitField.mul_ne_zero firstNonNull secondCrossNonzero)
      firstCrossNonzero, ?_⟩
  apply eq_of_mul_eq_mul_right firstCrossSquareNonzero
  calc
    (lineNorm first * lineNorm second) * firstCross ^ 2 =
        lineNorm first * (lineNorm second * firstCross ^ 2) := by ring1
    _ = lineNorm first * (lineNorm first * secondCross ^ 2) := by
      rw [normBalance]
    _ = (lineNorm first * secondCross) ^ 2 := by ring1
    _ =
        ((lineNorm first * secondCross / firstCross) * firstCross) ^ 2 := by
      rw [RFAP.ExplicitField.div_mul_cancel
        (lineNorm first * secondCross) firstCrossNonzero]
    _ = (lineNorm first * secondCross / firstCross) ^ 2 *
        firstCross ^ 2 := by ring1

/-- Any bisector supplies the square witness required by the normalized
construction. -/
theorem normProduct_isNonzeroSquare_of_isVertexBisector [DecidableEq K]
    (first second bisector : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (isBisector : IsVertexBisector first second bisector
      firstNonNull secondNonNull notParallel) :
    IsNonzeroSquare (lineNorm first * lineNorm second) := by
  rcases isBisector with ⟨bisectorNonNull, _containsVertex, equalSpreads⟩
  exact normProduct_isNonzeroSquare_of_equal_spreads first second bisector
    firstNonNull secondNonNull bisectorNonNull notParallel equalSpreads

/-- The two constructed bisectors are genuinely distinct ordered
proportions. -/
theorem vertexBisectors_not_equivalent [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation : root ^ 2 = lineNorm first * lineNorm second) :
    ¬ (positiveVertexBisector first second root firstNonNull notParallel).Equivalent
      (negativeVertexBisector first second root firstNonNull notParallel) := by
  let positive := positiveVertexBisector first second root
    firstNonNull notParallel
  let negative := negativeVertexBisector first second root
    firstNonNull notParallel
  have positiveNonNull : ¬ positive.IsNull :=
    positiveVertexBisector_nonNull first second root firstNonNull secondNonNull
      notParallel twoNonzero rootEquation
  have negativeNonNull : ¬ negative.IsNull :=
    negativeVertexBisector_nonNull first second root firstNonNull secondNonNull
      notParallel twoNonzero rootEquation
  have perpendicular : positive.Perpendicular negative :=
    vertexBisectors_perpendicular first second root firstNonNull notParallel
      rootEquation
  intro equivalent
  have determinantZero :
      positive.a * negative.b - negative.a * positive.b = 0 := by
    unfold Line.Equivalent at equivalent
    calc
      positive.a * negative.b - negative.a * positive.b =
          negative.a * positive.b - negative.a * positive.b := by
            rw [equivalent.1]
      _ = 0 := by ring1
  have dotZero : positive.a * negative.a + positive.b * negative.b = 0 := by
    exact perpendicular
  have normProductZero : lineNorm positive * lineNorm negative = 0 := by
    calc
      lineNorm positive * lineNorm negative =
          (positive.a * negative.b - negative.a * positive.b) ^ 2 +
            (positive.a * negative.a + positive.b * negative.b) ^ 2 := by
              unfold lineNorm
              ring1
      _ = 0 := by rw [determinantZero, dotZero]; ring1
  exact (RFAP.ExplicitField.mul_ne_zero positiveNonNull negativeNonNull)
    normProductZero

/-- Existence clause of Theorem 45: a bisector exists precisely when the
spread of the two vertex lines is a nonzero square.  Nonparallelity makes
the book's word “square” automatically nonzero. -/
theorem vertex_bisector_exists_iff_spread_isNonzeroSquare [DecidableEq K]
    (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0) :
    (∃ bisector : Line K,
        IsVertexBisector first second bisector
          firstNonNull secondNonNull notParallel) ↔
      IsNonzeroSquare
        (spread first second firstNonNull secondNonNull) := by
  constructor
  · rintro ⟨bisector, isBisector⟩
    apply (spread_isNonzeroSquare_iff_normProduct_isNonzeroSquare
      first second firstNonNull secondNonNull notParallel).2
    exact normProduct_isNonzeroSquare_of_isVertexBisector first second bisector
      firstNonNull secondNonNull notParallel isBisector
  · intro spreadSquare
    have normProductSquare :=
      (spread_isNonzeroSquare_iff_normProduct_isNonzeroSquare
        first second firstNonNull secondNonNull notParallel).1 spreadSquare
    rcases normProductSquare with ⟨root, _rootNonzero, normProductEquation⟩
    refine ⟨positiveVertexBisector first second root firstNonNull notParallel, ?_⟩
    exact positiveVertexBisector_isVertexBisector first second root firstNonNull
      secondNonNull notParallel twoNonzero normProductEquation.symm

/-- Theorem 45 (Vertex bisector), complete constructive form.  It combines
the square criterion with two explicit, distinct, perpendicular witnesses
and proves that every bisector is equivalent to one of them. -/
theorem vertex_bisector [DecidableEq K]
    (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0) :
    ((∃ bisector : Line K,
        IsVertexBisector first second bisector
          firstNonNull secondNonNull notParallel) ↔
      IsNonzeroSquare
        (spread first second firstNonNull secondNonNull)) ∧
      ∀ root : K, root ^ 2 = lineNorm first * lineNorm second →
        let positive := positiveVertexBisector first second root
          firstNonNull notParallel
        let negative := negativeVertexBisector first second root
          firstNonNull notParallel
        IsVertexBisector first second positive
            firstNonNull secondNonNull notParallel ∧
          IsVertexBisector first second negative
            firstNonNull secondNonNull notParallel ∧
          ¬ positive.Equivalent negative ∧
          positive.Perpendicular negative ∧
          ∀ bisector : Line K,
            IsVertexBisector first second bisector
                firstNonNull secondNonNull notParallel →
              bisector.Equivalent positive ∨ bisector.Equivalent negative := by
  constructor
  · exact vertex_bisector_exists_iff_spread_isNonzeroSquare first second
      firstNonNull secondNonNull notParallel twoNonzero
  · intro root rootEquation
    dsimp only
    exact ⟨
      positiveVertexBisector_isVertexBisector first second root firstNonNull
        secondNonNull notParallel twoNonzero rootEquation,
      negativeVertexBisector_isVertexBisector first second root firstNonNull
        secondNonNull notParallel twoNonzero rootEquation,
      vertexBisectors_not_equivalent first second root firstNonNull
        secondNonNull notParallel twoNonzero rootEquation,
      vertexBisectors_perpendicular first second root firstNonNull notParallel
        rootEquation,
      fun bisector isBisector => vertex_bisector_classification first second
        root firstNonNull secondNonNull notParallel rootEquation bisector
        isBisector⟩

/-- The constructive existence and perpendicularity clauses of Theorem 45.
The square root is input data rather than a choice-produced root. -/
theorem vertex_bisector_pair [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation : root ^ 2 = lineNorm first * lineNorm second) :
    let positive := positiveVertexBisector first second root firstNonNull notParallel
    let negative := negativeVertexBisector first second root firstNonNull notParallel
    ∃ positiveNonNull : ¬ positive.IsNull,
    ∃ negativeNonNull : ¬ negative.IsNull,
      spread first positive firstNonNull positiveNonNull =
          spread second positive secondNonNull positiveNonNull ∧
        spread first negative firstNonNull negativeNonNull =
          spread second negative secondNonNull negativeNonNull ∧
        positive.Perpendicular negative := by
  dsimp only
  let positiveNonNull := positiveVertexBisector_nonNull first second root
    firstNonNull secondNonNull notParallel twoNonzero rootEquation
  let negativeNonNull := negativeVertexBisector_nonNull first second root
    firstNonNull secondNonNull notParallel twoNonzero rootEquation
  exact ⟨positiveNonNull, negativeNonNull,
    positiveVertexBisector_equal_spreads first second root firstNonNull
      secondNonNull notParallel twoNonzero rootEquation,
    negativeVertexBisector_equal_spreads first second root firstNonNull
      secondNonNull notParallel twoNonzero rootEquation,
    vertexBisectors_perpendicular first second root firstNonNull notParallel
      rootEquation⟩

/-- Theorem 46 (Equal quadrance to two lines), in its constructive factorized
form: the equal-quadrance locus is exactly the union of the two explicit
bisector lines. -/
theorem equal_pointLineQuadrance_iff_on_vertexBisector [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (rootEquation : root ^ 2 = lineNorm first * lineNorm second)
    (point : Point K) :
    pointLineQuadrance point first firstNonNull =
        pointLineQuadrance point second secondNonNull ↔
      (positiveVertexBisector first second root firstNonNull notParallel).Contains point ∨
      (negativeVertexBisector first second root firstNonNull notParallel).Contains point := by
  let firstValue := first.a * point.x + first.b * point.y + first.c
  let secondValue := second.a * point.x + second.b * point.y + second.c
  have firstNormNonzero : lineNorm first ≠ 0 := firstNonNull
  have secondNormNonzero : lineNorm second ≠ 0 := secondNonNull
  have onPositiveIff :
      (positiveVertexBisector first second root firstNonNull notParallel).Contains point ↔
        root * firstValue + lineNorm first * secondValue = 0 := by
    constructor
    · intro contains
      unfold Line.Contains positiveVertexBisector at contains
      calc
        root * firstValue + lineNorm first * secondValue =
          (root * first.a + lineNorm first * second.a) * point.x +
            (root * first.b + lineNorm first * second.b) * point.y +
            (root * first.c + lineNorm first * second.c) := by
              unfold firstValue secondValue
              ring1
        _ = 0 := contains
    · intro factorZero
      unfold Line.Contains positiveVertexBisector
      calc
        (root * first.a + lineNorm first * second.a) * point.x +
            (root * first.b + lineNorm first * second.b) * point.y +
            (root * first.c + lineNorm first * second.c) =
          root * firstValue + lineNorm first * secondValue := by
            unfold firstValue secondValue
            ring1
        _ = 0 := factorZero
  have onNegativeIff :
      (negativeVertexBisector first second root firstNonNull notParallel).Contains point ↔
        root * firstValue - lineNorm first * secondValue = 0 := by
    constructor
    · intro contains
      unfold Line.Contains negativeVertexBisector at contains
      calc
        root * firstValue - lineNorm first * secondValue =
          (root * first.a - lineNorm first * second.a) * point.x +
            (root * first.b - lineNorm first * second.b) * point.y +
            (root * first.c - lineNorm first * second.c) := by
              unfold firstValue secondValue
              ring1
        _ = 0 := contains
    · intro factorZero
      unfold Line.Contains negativeVertexBisector
      calc
        (root * first.a - lineNorm first * second.a) * point.x +
            (root * first.b - lineNorm first * second.b) * point.y +
            (root * first.c - lineNorm first * second.c) =
          root * firstValue - lineNorm first * secondValue := by
            unfold firstValue secondValue
            ring1
        _ = 0 := factorZero
  rw [pointLineQuadrance_formula, pointLineQuadrance_formula]
  constructor
  · intro equalRatios
    have crossProduct := cross_mul_of_ratio_eq
      firstNormNonzero secondNormNonzero equalRatios
    change firstValue ^ 2 * lineNorm second =
      secondValue ^ 2 * lineNorm first at crossProduct
    have factorProduct :
        (root * firstValue - lineNorm first * secondValue) *
          (root * firstValue + lineNorm first * secondValue) = 0 := by
      calc
        (root * firstValue - lineNorm first * secondValue) *
            (root * firstValue + lineNorm first * secondValue) =
          root ^ 2 * firstValue ^ 2 -
            lineNorm first ^ 2 * secondValue ^ 2 := by ring1
        _ =
          lineNorm first *
            (firstValue ^ 2 * lineNorm second -
              secondValue ^ 2 * lineNorm first) := by
          rw [rootEquation]
          ring1
        _ = 0 := by rw [crossProduct]; ring1
    by_cases negativeFactorZero :
        root * firstValue - lineNorm first * secondValue = 0
    · right
      exact onNegativeIff.2 negativeFactorZero
    · left
      have positiveFactorZero :
          root * firstValue + lineNorm first * secondValue = 0 := by
        by_cases positiveZero :
            root * firstValue + lineNorm first * secondValue = 0
        · exact positiveZero
        · exact False.elim
            ((RFAP.ExplicitField.mul_ne_zero negativeFactorZero positiveZero)
              factorProduct)
      exact onPositiveIff.2 positiveFactorZero
  · intro onBisector
    apply ratio_eq_of_cross_mul firstNormNonzero secondNormNonzero
    change firstValue ^ 2 * lineNorm second =
      secondValue ^ 2 * lineNorm first
    have factorProduct :
        (root * firstValue - lineNorm first * secondValue) *
          (root * firstValue + lineNorm first * secondValue) = 0 := by
      rcases onBisector with onPositive | onNegative
      · have positiveFactorZero :
            root * firstValue + lineNorm first * secondValue = 0 := by
          exact onPositiveIff.1 onPositive
        rw [positiveFactorZero]
        ring1
      · have negativeFactorZero :
            root * firstValue - lineNorm first * secondValue = 0 := by
          exact onNegativeIff.1 onNegative
        rw [negativeFactorZero]
        ring1
    have scaledDifference : lineNorm first *
        (firstValue ^ 2 * lineNorm second -
          secondValue ^ 2 * lineNorm first) = 0 := by
      calc
        lineNorm first *
            (firstValue ^ 2 * lineNorm second -
              secondValue ^ 2 * lineNorm first) =
          root ^ 2 * firstValue ^ 2 -
            lineNorm first ^ 2 * secondValue ^ 2 := by
              rw [rootEquation]
              ring1
        _ =
          (root * firstValue - lineNorm first * secondValue) *
            (root * firstValue + lineNorm first * secondValue) := by
              ring1
        _ = 0 := factorProduct
    have differenceZero :=
      eq_zero_of_mul_eq_zero_left firstNormNonzero scaledDifference
    calc
      firstValue ^ 2 * lineNorm second =
          (firstValue ^ 2 * lineNorm second -
            secondValue ^ 2 * lineNorm first) +
            secondValue ^ 2 * lineNorm first := by ring1
      _ = secondValue ^ 2 * lineNorm first := by rw [differenceZero]; ring1

end DivineProportions
