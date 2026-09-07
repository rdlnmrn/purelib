import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Trigonometry.QuadranceToLine

/-!
# Divine Proportions, Chapter 6: spread, cross, and twist

The ratio notions carry explicit non-null/non-perpendicular certificates for
their denominators.  They are otherwise ordinary finite field expressions.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Spread between two displayed non-null lines. -/
def spread (first second : Line K)
    (_firstNonNull : ¬ first.IsNull) (_secondNonNull : ¬ second.IsNull) : K :=
  (first.a * second.b - second.a * first.b) ^ 2 /
    (lineNorm first * lineNorm second)

/-- Cross between two displayed non-null lines. -/
def cross (first second : Line K)
    (_firstNonNull : ¬ first.IsNull) (_secondNonNull : ¬ second.IsNull) : K :=
  (first.a * second.a + first.b * second.b) ^ 2 /
    (lineNorm first * lineNorm second)

/-- Twist between two displayed non-perpendicular lines. -/
def twist (first second : Line K)
    (_notPerpendicular : ¬ first.Perpendicular second) : K :=
  (first.a * second.b - second.a * first.b) ^ 2 /
    (first.a * second.a + first.b * second.b) ^ 2

private theorem normProductNonzero
    (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) :
    lineNorm first * lineNorm second ≠ 0 :=
  RFAP.ExplicitField.mul_ne_zero firstNonNull secondNonNull

private theorem eq_of_mul_eq_mul_left
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = 1 * left := by rw [one_mul]
    _ = (factor * factor⁻¹) * left := by rw [factorCancel]
    _ = factor⁻¹ * (factor * left) := by ring1
    _ = factor⁻¹ * (factor * right) := by rw [productsEqual]
    _ = (factor * factor⁻¹) * right := by ring1
    _ = right := by rw [factorCancel, one_mul]

private theorem div_eq_div_of_cross_mul [DecidableEq K]
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel leftDenominator leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel rightDenominator rightNonzero
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

/-- A displayed line parallel to a non-null line is itself non-null.  The
proof uses the explicit nonzero direction scale rather than selecting a
representative of a line quotient. -/
theorem nonNull_of_parallel [DecidableEq K]
    (source target : Line K) (sourceNonNull : ¬ source.IsNull)
    (parallel : source.Parallel target) : ¬ target.IsNull := by
  rcases direction_scale_of_parallel source target parallel with
    ⟨scale, scaleNonzero, targetA, targetB⟩
  intro targetNull
  have scaleSquaredNonzero : scale * scale ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero scaleNonzero scaleNonzero
  have scaledNormNonzero :
      (scale * scale) * (source.a ^ 2 + source.b ^ 2) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero scaleSquaredNonzero sourceNonNull
  apply scaledNormNonzero
  calc
    (scale * scale) * (source.a ^ 2 + source.b ^ 2) =
        target.a ^ 2 + target.b ^ 2 := by
      rw [targetA, targetB]
      ring1
    _ = 0 := targetNull

/-- Replacing both non-null lines by parallel representatives preserves
spread. -/
theorem spread_eq_of_parallel_pairs [DecidableEq K]
    (first second firstParallel secondParallel : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (firstParallelNonNull : ¬ firstParallel.IsNull)
    (secondParallelNonNull : ¬ secondParallel.IsNull)
    (firstDirectionsParallel : first.Parallel firstParallel)
    (secondDirectionsParallel : second.Parallel secondParallel) :
    spread first second firstNonNull secondNonNull =
      spread firstParallel secondParallel firstParallelNonNull
        secondParallelNonNull := by
  rcases direction_scale_of_parallel first firstParallel
      firstDirectionsParallel with
    ⟨firstScale, firstScaleNonzero, firstA, firstB⟩
  rcases direction_scale_of_parallel second secondParallel
      secondDirectionsParallel with
    ⟨secondScale, secondScaleNonzero, secondA, secondB⟩
  have firstDenominatorNonzero : lineNorm first * lineNorm second ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstNonNull secondNonNull
  have secondDenominatorNonzero :
      lineNorm firstParallel * lineNorm secondParallel ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstParallelNonNull secondParallelNonNull
  unfold spread
  apply div_eq_div_of_cross_mul firstDenominatorNonzero
    secondDenominatorNonzero
  unfold lineNorm
  rw [firstA, firstB, secondA, secondB]
  ring1

/-- Replacing both non-perpendicular lines by parallel representatives
preserves twist.  The proof keeps both denominator certificates explicit and
uses the finite direction scales supplied by the displayed line records. -/
theorem twist_eq_of_parallel_pairs [DecidableEq K]
    (first second firstParallel secondParallel : Line K)
    (firstNotPerpendicular : ¬ first.Perpendicular second)
    (parallelNotPerpendicular :
      ¬ firstParallel.Perpendicular secondParallel)
    (firstDirectionsParallel : first.Parallel firstParallel)
    (secondDirectionsParallel : second.Parallel secondParallel) :
    twist first second firstNotPerpendicular =
      twist firstParallel secondParallel parallelNotPerpendicular := by
  rcases direction_scale_of_parallel first firstParallel
      firstDirectionsParallel with
    ⟨firstScale, _firstScaleNonzero, firstA, firstB⟩
  rcases direction_scale_of_parallel second secondParallel
      secondDirectionsParallel with
    ⟨secondScale, _secondScaleNonzero, secondA, secondB⟩
  have firstDotNonzero :
      first.a * second.a + first.b * second.b ≠ 0 :=
    firstNotPerpendicular
  have parallelDotNonzero :
      firstParallel.a * secondParallel.a +
          firstParallel.b * secondParallel.b ≠ 0 :=
    parallelNotPerpendicular
  have firstDenominatorNonzero :
      (first.a * second.a + first.b * second.b) ^ 2 ≠ 0 := by
    simpa [pow_two] using
      RFAP.ExplicitField.mul_ne_zero firstDotNonzero firstDotNonzero
  have parallelDenominatorNonzero :
      (firstParallel.a * secondParallel.a +
          firstParallel.b * secondParallel.b) ^ 2 ≠ 0 := by
    simpa [pow_two] using
      RFAP.ExplicitField.mul_ne_zero parallelDotNonzero parallelDotNonzero
  unfold twist
  apply div_eq_div_of_cross_mul firstDenominatorNonzero
    parallelDenominatorNonzero
  rw [firstA, firstB, secondA, secondB]
  ring1

/-- Spread is symmetric in its two lines. -/
theorem spread_symm (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) :
    spread first second firstNonNull secondNonNull =
      spread second first secondNonNull firstNonNull := by
  unfold spread
  congr 1 <;> ring1

/-- A spread of two non-null lines vanishes exactly when their direction
determinant vanishes. -/
theorem spread_eq_zero_iff_parallel [DecidableEq K]
    (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) :
    spread first second firstNonNull secondNonNull = 0 ↔
      first.Parallel second := by
  let determinant := first.a * second.b - second.a * first.b
  let denominator := lineNorm first * lineNorm second
  have denominatorNonzero : denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstNonNull secondNonNull
  constructor
  · intro spreadZero
    change determinant ^ 2 / denominator = 0 at spreadZero
    have numeratorZero : determinant ^ 2 = 0 := by
      calc
        determinant ^ 2 =
            (determinant ^ 2 / denominator) * denominator :=
              (RFAP.ExplicitField.div_mul_cancel
                (determinant ^ 2) denominatorNonzero).symm
        _ = 0 := by
          rw [spreadZero]
          ring1
    have determinantZero : determinant = 0 := by
      by_cases zero : determinant = 0
      · exact zero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero zero zero) (by
            simpa [pow_two] using numeratorZero))
    exact determinantZero
  · intro parallel
    change determinant = 0 at parallel
    change determinant ^ 2 / denominator = 0
    rw [parallel]
    rw [show (0 : K) ^ 2 = 0 by ring1]
    exact RFAP.ExplicitField.zero_div denominator

/-- Cross is symmetric in its two lines. -/
theorem cross_symm (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) :
    cross first second firstNonNull secondNonNull =
      cross second first secondNonNull firstNonNull := by
  unfold cross
  congr 1 <;> ring1

/-- Theorem 33 (Spread plus cross), Fibonacci's two-square identity with its
finite denominator cancelled explicitly. -/
theorem spread_add_cross (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) :
    spread first second firstNonNull secondNonNull +
      cross first second firstNonNull secondNonNull = 1 := by
  have denominatorNonzero :=
    normProductNonzero first second firstNonNull secondNonNull
  have denominatorCancel :
      (lineNorm first * lineNorm second) *
        (lineNorm first * lineNorm second)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ denominatorNonzero
  unfold spread cross
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (first.a * second.b - second.a * first.b) ^ 2 *
          (lineNorm first * lineNorm second)⁻¹ +
        (first.a * second.a + first.b * second.b) ^ 2 *
          (lineNorm first * lineNorm second)⁻¹ =
      (lineNorm first * lineNorm second) *
        (lineNorm first * lineNorm second)⁻¹ := by
          unfold lineNorm
          ring1
    _ = 1 := denominatorCancel

/-- Perpendicular non-null lines have unit spread. -/
theorem spread_eq_one_of_perpendicular
    (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (perpendicular : first.Perpendicular second) :
    spread first second firstNonNull secondNonNull = 1 := by
  have crossZero : cross first second firstNonNull secondNonNull = 0 := by
    unfold Line.Perpendicular at perpendicular
    unfold cross
    rw [perpendicular]
    rw [show (0 : K) ^ 2 = 0 by ring1]
    exact RFAP.ExplicitField.zero_div _
  calc
    spread first second firstNonNull secondNonNull =
        spread first second firstNonNull secondNonNull +
          cross first second firstNonNull secondNonNull := by
      rw [crossZero, add_zero]
    _ = 1 := spread_add_cross first second firstNonNull secondNonNull

/-- A spread number carries the square witness in `s(1-s) = r²`. -/
def IsSpreadNumber (value : K) : Prop :=
  ∃ root : K, value * (1 - value) = root ^ 2

/-- Theorem 34, forward clause: every spread is a spread number. -/
theorem spread_isSpreadNumber (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) :
    IsSpreadNumber (spread first second firstNonNull secondNonNull) := by
  let determinant := first.a * second.b - second.a * first.b
  let dot := first.a * second.a + first.b * second.b
  let denominator := lineNorm first * lineNorm second
  have denominatorNonzero : denominator ≠ 0 :=
    normProductNonzero first second firstNonNull secondNonNull
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ denominatorNonzero
  refine ⟨determinant * dot / denominator, ?_⟩
  have fibonacci :
      (first.a * second.b - second.a * first.b) ^ 2 +
        (first.a * second.a + first.b * second.b) ^ 2 =
      lineNorm first * lineNorm second := by
    unfold lineNorm
    ring1
  unfold spread determinant dot denominator
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  rw [show 1 -
      (first.a * second.b - second.a * first.b) ^ 2 *
        (lineNorm first * lineNorm second)⁻¹ =
      (first.a * second.a + first.b * second.b) ^ 2 *
        (lineNorm first * lineNorm second)⁻¹ by
    calc
      1 - (first.a * second.b - second.a * first.b) ^ 2 *
          (lineNorm first * lineNorm second)⁻¹ =
        (lineNorm first * lineNorm second) *
            (lineNorm first * lineNorm second)⁻¹ -
          (first.a * second.b - second.a * first.b) ^ 2 *
            (lineNorm first * lineNorm second)⁻¹ := by
              rw [denominatorCancel]
      _ = (first.a * second.a + first.b * second.b) ^ 2 *
          (lineNorm first * lineNorm second)⁻¹ := by
            rw [← fibonacci]
            ring1]
  ring1

private theorem one_sub_ne_zero {value : K} (notOne : value ≠ 1) :
    1 - value ≠ 0 := by
  intro differenceZero
  apply notOne
  calc
    value = 1 - (1 - value) := by ring1
    _ = 1 := by rw [differenceZero]; ring1

/-- Theorem 34, converse clause: the square witness constructs two concrete
non-null lines whose spread is the requested value. -/
theorem spreadNumber_realized [Nontrivial K] [DecidableEq K]
    (value root : K) (square : value * (1 - value) = root ^ 2) :
    ∃ first second : Line K,
      ∃ firstNonNull : ¬ first.IsNull,
      ∃ secondNonNull : ¬ second.IsNull,
        spread first second firstNonNull secondNonNull = value := by
  let vertical : Line K :=
    { a := 0, b := 1, c := 0,
      direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0) }
  have verticalNonNull : ¬ vertical.IsNull := by
    unfold Line.IsNull vertical
    intro normZero
    exact (one_ne_zero : (1 : K) ≠ 0) (by
      calc
        (1 : K) = 0 ^ 2 + 1 ^ 2 := by ring1
        _ = 0 := normZero)
  by_cases valueIsOne : value = 1
  · let horizontal : Line K :=
      { a := 1, b := 0, c := 0,
        direction_nonzero := Or.inl (one_ne_zero : (1 : K) ≠ 0) }
    have horizontalNonNull : ¬ horizontal.IsNull := by
      unfold Line.IsNull horizontal
      intro normZero
      exact (one_ne_zero : (1 : K) ≠ 0) (by
        calc
          (1 : K) = 1 ^ 2 + 0 ^ 2 := by ring1
          _ = 0 := normZero)
    refine ⟨vertical, horizontal, verticalNonNull, horizontalNonNull, ?_⟩
    have oneInverse : (1 : K)⁻¹ = 1 := by
      calc
        (1 : K)⁻¹ = 1 * (1 : K)⁻¹ := by rw [one_mul]
        _ = 1 := RFAP.ExplicitField.mul_inv_cancel 1 one_ne_zero
    unfold spread
    rw [show
      ((vertical.a * horizontal.b - horizontal.a * vertical.b) ^ 2) =
          (1 : K) by unfold vertical horizontal; ring1]
    rw [show lineNorm vertical * lineNorm horizontal = (1 : K) by
      unfold lineNorm vertical horizontal
      ring1]
    rw [valueIsOne]
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    rw [oneInverse]
    ring1
  · have differenceNonzero : 1 - value ≠ 0 := one_sub_ne_zero valueIsOne
    let target : Line K :=
      { a := root
        b := 1 - value
        c := 0
        direction_nonzero := Or.inr differenceNonzero }
    have targetNorm : lineNorm target = 1 - value := by
      unfold lineNorm target
      calc
        root ^ 2 + (1 - value) ^ 2 =
            value * (1 - value) + (1 - value) ^ 2 := by rw [← square]
        _ = 1 - value := by ring1
    have targetNonNull : ¬ target.IsNull := by
      intro targetNull
      apply differenceNonzero
      calc
        1 - value = lineNorm target := targetNorm.symm
        _ = 0 := targetNull
    refine ⟨vertical, target, verticalNonNull, targetNonNull, ?_⟩
    have differenceCancel :
        (1 - value) * (1 - value)⁻¹ = (1 : K) :=
      RFAP.ExplicitField.mul_inv_cancel _ differenceNonzero
    unfold spread
    rw [show lineNorm vertical = (1 : K) by
      unfold lineNorm vertical
      ring1, targetNorm]
    unfold vertical target
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    rw [one_mul]
    calc
      (0 * (1 - value) - root * 1) ^ 2 * (1 - value)⁻¹ =
          root ^ 2 * (1 - value)⁻¹ := by ring1
      _ = value * (1 - value) * (1 - value)⁻¹ := by rw [square]
      _ = value := by rw [mul_assoc, differenceCancel, mul_one]

/-- The line-through construction has norm equal to endpoint quadrance. -/
theorem lineThrough_norm_eq_quadrance [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) :
    lineNorm (lineThrough first second distinct) = quadrance first second := by
  unfold lineNorm lineThrough quadrance
  ring1

/-- Theorem 43 (Spread from points), in coordinate form. -/
theorem spread_from_points [DecidableEq K]
    (first second vertex : Point K)
    (firstDistinct : first ≠ vertex) (secondDistinct : second ≠ vertex)
    (firstNonNull : ¬ (lineThrough first vertex firstDistinct).IsNull)
    (secondNonNull : ¬ (lineThrough second vertex secondDistinct).IsNull) :
    spread (lineThrough first vertex firstDistinct)
        (lineThrough second vertex secondDistinct) firstNonNull secondNonNull =
      (((first.y - vertex.y) * (vertex.x - second.x) -
        (second.y - vertex.y) * (vertex.x - first.x)) ^ 2) /
        (quadrance first vertex * quadrance second vertex) := by
  unfold spread
  rw [lineThrough_norm_eq_quadrance first vertex firstDistinct,
    lineThrough_norm_eq_quadrance second vertex secondDistinct]
  congr 1

/-- Theorem 44 (Cross from points), in coordinate form. -/
theorem cross_from_points [DecidableEq K]
    (first second vertex : Point K)
    (firstDistinct : first ≠ vertex) (secondDistinct : second ≠ vertex)
    (firstNonNull : ¬ (lineThrough first vertex firstDistinct).IsNull)
    (secondNonNull : ¬ (lineThrough second vertex secondDistinct).IsNull) :
    cross (lineThrough first vertex firstDistinct)
        (lineThrough second vertex secondDistinct) firstNonNull secondNonNull =
      (((first.y - vertex.y) * (second.y - vertex.y) +
        (vertex.x - first.x) * (vertex.x - second.x)) ^ 2) /
        (quadrance first vertex * quadrance second vertex) := by
  unfold cross
  rw [lineThrough_norm_eq_quadrance first vertex firstDistinct,
    lineThrough_norm_eq_quadrance second vertex secondDistinct]
  congr 1

end DivineProportions
