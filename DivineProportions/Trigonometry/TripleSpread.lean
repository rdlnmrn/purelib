import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Trigonometry.Spread

/-!
# Divine Proportions, Chapter 7: the triple spread formula

The proof is performed directly on the six finite line coefficients.  A
single explicit common denominator replaces the book's auxiliary triangle,
and every cancellation is witnessed by the three non-null hypotheses.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The symmetric triple-spread polynomial from §7.1. -/
def tripleSpreadFunction (a b c : K) : K :=
  (a + b + c) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2) - 4 * a * b * c

/-- Three displayed scalars form a spread triple when the triple-spread
polynomial vanishes. -/
def SpreadTriple (a b c : K) : Prop := tripleSpreadFunction a b c = 0

/-- The spread-triple relation is invariant under swapping its outer entries. -/
theorem spreadTriple_swap_first_third {a b c : K}
    (triple : SpreadTriple a b c) : SpreadTriple c b a := by
  unfold SpreadTriple tripleSpreadFunction at triple ⊢
  calc
    (c + b + a) ^ 2 - 2 * (c ^ 2 + b ^ 2 + a ^ 2) - 4 * c * b * a =
        (a + b + c) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2) - 4 * a * b * c := by
      ring1
    _ = 0 := triple

/-- The spread-triple relation is invariant under a cyclic rotation. -/
theorem spreadTriple_rotate {a b c : K}
    (triple : SpreadTriple a b c) : SpreadTriple b c a := by
  unfold SpreadTriple tripleSpreadFunction at triple ⊢
  calc
    (b + c + a) ^ 2 - 2 * (b ^ 2 + c ^ 2 + a ^ 2) - 4 * b * c * a =
        (a + b + c) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2) - 4 * a * b * c := by
      ring1
    _ = 0 := triple

/-- A square comes with the root that displays it. -/
def IsSquare (value : K) : Prop := ∃ root : K, value = root ^ 2

/-- The four-by-four determinant displayed in Exercise 7.1, expanded along
its first row. -/
def tripleSpreadDeterminant (a b c : K) : K :=
  -a * (a * (0 * 2 - 1 * 1) - c * (b * 2 - 1 * 1) +
      1 * (b * 1 - 0 * 1)) +
    b * (a * (c * 2 - 1 * 1) - 0 * (b * 2 - 1 * 1) +
      1 * (b * 1 - c * 1)) -
    (a * (c * 1 - 0 * 1) - 0 * (b * 1 - 0 * 1) +
      c * (b * 1 - c * 1))

/-- Exercise 7.1: the main polynomial, Archimedes, complement, and determinant
forms of the triple-spread function. -/
theorem exercise_7_1 (a b c : K) :
    tripleSpreadFunction a b c =
        archimedesFunction a b c - 4 * a * b * c ∧
      tripleSpreadFunction a b c =
        2 * (a * c + b * c + a * b) -
          (a ^ 2 + b ^ 2 + c ^ 2) - 4 * a * b * c ∧
      tripleSpreadFunction a b c =
        4 * (a * b + b * c + c * a) - (a + b + c) ^ 2 -
          4 * a * b * c ∧
      tripleSpreadFunction a b c =
        4 * (1 - a) * (1 - b) * (1 - c) -
          (a + b + c - 2) ^ 2 ∧
      tripleSpreadFunction a b c = -tripleSpreadDeterminant a b c := by
  unfold tripleSpreadFunction archimedesFunction tripleSpreadDeterminant
  exact ⟨by ring1, by ring1, by ring1, by ring1, by ring1⟩

/-- Exercise 7.2, the form used by the later triangle-spread rules. -/
theorem exercise_7_2 (a b c : K) :
    tripleSpreadFunction a b c =
      ((a + b - c) * c + (c - a + b) * (c - b + a)) * (1 - c) -
        c * (c - (a + b)) * (1 - (a + b)) := by
  unfold tripleSpreadFunction
  ring1

private theorem square_eq_zero_iff [DecidableEq K] (value : K) :
    value ^ 2 = 0 ↔ value = 0 := by
  constructor
  · intro squareZero
    by_cases valueZero : value = 0
    · exact valueZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero valueZero valueZero) (by
          simpa [pow_two] using squareZero))
  · intro valueZero
    rw [valueZero]
    ring1

/-- Exercise 7.3, including the converses implicit in the two displayed
specializations. -/
theorem spreadTriple_zero_iff [DecidableEq K] (a b : K) :
    SpreadTriple a b 0 ↔ a = b := by
  constructor
  · intro triple
    apply sub_eq_zero.mp
    apply (square_eq_zero_iff (a - b)).1
    unfold SpreadTriple at triple
    calc
      (a - b) ^ 2 = -tripleSpreadFunction a b 0 := by
        unfold tripleSpreadFunction
        ring1
      _ = 0 := by rw [triple]; ring1
  · intro equal
    unfold SpreadTriple tripleSpreadFunction
    rw [equal]
    ring1

/-- Exercise 7.3, unit specialization. -/
theorem spreadTriple_one_iff [DecidableEq K] (a b : K) :
    SpreadTriple a b 1 ↔ a + b = 1 := by
  constructor
  · intro triple
    apply sub_eq_zero.mp
    apply (square_eq_zero_iff (a + b - 1)).1
    unfold SpreadTriple at triple
    calc
      (a + b - 1) ^ 2 = -tripleSpreadFunction a b 1 := by
        unfold tripleSpreadFunction
        ring1
      _ = 0 := by rw [triple]; ring1
  · intro sumOne
    unfold SpreadTriple tripleSpreadFunction
    calc
      (a + b + 1) ^ 2 - 2 * (a ^ 2 + b ^ 2 + 1 ^ 2) -
          4 * a * b * 1 = -(a + b - 1) ^ 2 := by ring1
      _ = 0 := by rw [sumOne]; ring1

/-- The complement form extracted in Exercise 7.1. -/
theorem spreadTriple_complement_form {a b c : K}
    (triple : SpreadTriple a b c) :
    (a + b + c - 2) ^ 2 = 4 * (1 - a) * (1 - b) * (1 - c) := by
  have differenceZero :
      4 * (1 - a) * (1 - b) * (1 - c) -
          (a + b + c - 2) ^ 2 = 0 := by
    calc
      4 * (1 - a) * (1 - b) * (1 - c) -
          (a + b + c - 2) ^ 2 = tripleSpreadFunction a b c := by
            exact (exercise_7_1 a b c).2.2.2.1.symm
      _ = 0 := triple
  exact (sub_eq_zero.mp differenceZero).symm

/-- Exercise 7.6: all four useful quadratic forms of the triple-spread
equation. -/
theorem exercise_7_6 {a b c : K} (triple : SpreadTriple a b c) :
    c ^ 2 - 2 * c * (a + b - 2 * a * b) + (a - b) ^ 2 = 0 ∧
      (c - a + b) ^ 2 = 4 * (1 - a) * b * c ∧
      (c - b + a) ^ 2 = 4 * a * (1 - b) * c ∧
      (c - a - b) ^ 2 = 4 * a * b * (1 - c) ∧
      (c - (a + b - 2 * a * b)) ^ 2 =
        4 * a * b * (1 - a) * (1 - b) := by
  unfold SpreadTriple at triple
  constructor
  · calc
      c ^ 2 - 2 * c * (a + b - 2 * a * b) + (a - b) ^ 2 =
          -tripleSpreadFunction a b c := by
            unfold tripleSpreadFunction
            ring1
      _ = 0 := by rw [triple]; ring1
  constructor
  · have differenceZero :
        (c - a + b) ^ 2 - 4 * (1 - a) * b * c = 0 := by
      calc
      (c - a + b) ^ 2 - 4 * (1 - a) * b * c =
          -tripleSpreadFunction a b c := by
            unfold tripleSpreadFunction
            ring1
      _ = 0 := by rw [triple]; ring1
    calc
      (c - a + b) ^ 2 =
          ((c - a + b) ^ 2 - 4 * (1 - a) * b * c) +
            4 * (1 - a) * b * c := by ring1
      _ = 4 * (1 - a) * b * c := by rw [differenceZero]; ring1
  constructor
  · have differenceZero :
        (c - b + a) ^ 2 - 4 * a * (1 - b) * c = 0 := by
      calc
      (c - b + a) ^ 2 - 4 * a * (1 - b) * c =
          -tripleSpreadFunction a b c := by
            unfold tripleSpreadFunction
            ring1
      _ = 0 := by rw [triple]; ring1
    calc
      (c - b + a) ^ 2 =
          ((c - b + a) ^ 2 - 4 * a * (1 - b) * c) +
            4 * a * (1 - b) * c := by ring1
      _ = 4 * a * (1 - b) * c := by rw [differenceZero]; ring1
  constructor
  · have differenceZero :
        (c - a - b) ^ 2 - 4 * a * b * (1 - c) = 0 := by
      calc
      (c - a - b) ^ 2 - 4 * a * b * (1 - c) =
          -tripleSpreadFunction a b c := by
            unfold tripleSpreadFunction
            ring1
      _ = 0 := by rw [triple]; ring1
    calc
      (c - a - b) ^ 2 =
          ((c - a - b) ^ 2 - 4 * a * b * (1 - c)) +
            4 * a * b * (1 - c) := by ring1
      _ = 4 * a * b * (1 - c) := by rw [differenceZero]; ring1
  · have differenceZero :
        (c - (a + b - 2 * a * b)) ^ 2 -
          4 * a * b * (1 - a) * (1 - b) = 0 := by
      calc
      (c - (a + b - 2 * a * b)) ^ 2 -
          4 * a * b * (1 - a) * (1 - b) =
        -tripleSpreadFunction a b c := by
          unfold tripleSpreadFunction
          ring1
      _ = 0 := by rw [triple]; ring1
    calc
      (c - (a + b - 2 * a * b)) ^ 2 =
          ((c - (a + b - 2 * a * b)) ^ 2 -
            4 * a * b * (1 - a) * (1 - b)) +
              4 * a * b * (1 - a) * (1 - b) := by ring1
      _ = 4 * a * b * (1 - a) * (1 - b) := by
        rw [differenceZero]
        ring1

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

private theorem triple_fraction_identity
    (a b c denominator product : K)
    (denominatorNonzero : denominator ≠ 0)
    (productEquation : a * b * c = denominator * product ^ 2)
    (polynomialIdentity :
      (a + b + c) ^ 2 =
        2 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * product ^ 2) :
    (a / denominator + b / denominator + c / denominator) ^ 2 =
      2 * ((a / denominator) ^ 2 +
        (b / denominator) ^ 2 + (c / denominator) ^ 2) +
      4 * (a / denominator) * (b / denominator) * (c / denominator) := by
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have cubicReduction :
      (a * denominator⁻¹) * (b * denominator⁻¹) *
          (c * denominator⁻¹) =
        product ^ 2 * denominator⁻¹ ^ 2 := by
    calc
      (a * denominator⁻¹) * (b * denominator⁻¹) *
          (c * denominator⁻¹) =
        (a * b * c) * denominator⁻¹ ^ 3 := by ring1
      _ = (denominator * product ^ 2) * denominator⁻¹ ^ 3 := by
        rw [productEquation]
      _ = product ^ 2 * (denominator * denominator⁻¹) *
          denominator⁻¹ ^ 2 := by ring1
      _ = product ^ 2 * denominator⁻¹ ^ 2 := by
        rw [denominatorCancel, mul_one]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (a * denominator⁻¹ + b * denominator⁻¹ + c * denominator⁻¹) ^ 2 =
        (a + b + c) ^ 2 * denominator⁻¹ ^ 2 := by ring1
    _ =
        (2 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * product ^ 2) *
          denominator⁻¹ ^ 2 := by rw [polynomialIdentity]
    _ =
        2 * ((a * denominator⁻¹) ^ 2 +
          (b * denominator⁻¹) ^ 2 + (c * denominator⁻¹) ^ 2) +
          4 * (product ^ 2 * denominator⁻¹ ^ 2) := by ring1
    _ =
        2 * ((a * denominator⁻¹) ^ 2 +
          (b * denominator⁻¹) ^ 2 + (c * denominator⁻¹) ^ 2) +
          4 * ((a * denominator⁻¹) * (b * denominator⁻¹) *
            (c * denominator⁻¹)) := by
              rw [cubicReduction]
    _ =
        2 * ((a * denominator⁻¹) ^ 2 +
          (b * denominator⁻¹) ^ 2 + (c * denominator⁻¹) ^ 2) +
          4 * (a * denominator⁻¹) * (b * denominator⁻¹) *
            (c * denominator⁻¹) := by ring1

/-- Exercise 7.5: the displayed two-parameter rational construction always
produces a spread triple.  The hypotheses are exactly the two denominators
which the printed fractions require to be nonzero. -/
theorem exercise_7_5
    (u v : K)
    (uDenominatorNonzero : 1 + u ^ 2 ≠ 0)
    (vDenominatorNonzero : 1 + v ^ 2 ≠ 0) :
    SpreadTriple
      (u ^ 2 / (1 + u ^ 2))
      (v ^ 2 / (1 + v ^ 2))
      ((u - v) ^ 2 / ((1 + u ^ 2) * (1 + v ^ 2))) := by
  let uDenominator := 1 + u ^ 2
  let vDenominator := 1 + v ^ 2
  let denominator := uDenominator * vDenominator
  let firstNumerator := u ^ 2 * vDenominator
  let secondNumerator := v ^ 2 * uDenominator
  let thirdNumerator := (u - v) ^ 2
  let product := u * v * (u - v)
  have denominatorNonzero : denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero uDenominatorNonzero
      vDenominatorNonzero
  have firstValue :
      u ^ 2 / (1 + u ^ 2) = firstNumerator / denominator := by
    apply ratio_eq_of_cross_product uDenominatorNonzero denominatorNonzero
    unfold firstNumerator denominator uDenominator vDenominator
    ring1
  have secondValue :
      v ^ 2 / (1 + v ^ 2) = secondNumerator / denominator := by
    apply ratio_eq_of_cross_product vDenominatorNonzero denominatorNonzero
    unfold secondNumerator denominator uDenominator vDenominator
    ring1
  have thirdValue :
      (u - v) ^ 2 / ((1 + u ^ 2) * (1 + v ^ 2)) =
        thirdNumerator / denominator := by
    unfold thirdNumerator denominator uDenominator vDenominator
    rfl
  have numeratorProduct :
      firstNumerator * secondNumerator * thirdNumerator =
        denominator * product ^ 2 := by
    unfold firstNumerator secondNumerator thirdNumerator denominator product
      uDenominator vDenominator
    ring1
  have numeratorIdentity :
      (firstNumerator + secondNumerator + thirdNumerator) ^ 2 =
        2 * (firstNumerator ^ 2 + secondNumerator ^ 2 +
          thirdNumerator ^ 2) + 4 * product ^ 2 := by
    unfold firstNumerator secondNumerator thirdNumerator product
      uDenominator vDenominator
    ring1
  have fractionIdentity := triple_fraction_identity firstNumerator
    secondNumerator thirdNumerator denominator product denominatorNonzero
    numeratorProduct numeratorIdentity
  unfold SpreadTriple tripleSpreadFunction
  rw [firstValue, secondValue, thirdValue, fractionIdentity]
  ring1

/-- Exercise 7.5's requested counterexample: `{1,0,1}` is a spread triple,
but its first entry cannot have the displayed parametrized form in any
nontrivial constructive explicit field. -/
theorem exercise_7_5_counterexample [Nontrivial K] :
    SpreadTriple (1 : K) 0 1 ∧
      ¬ ∃ u v : K,
        1 + u ^ 2 ≠ 0 ∧
        1 + v ^ 2 ≠ 0 ∧
        u ^ 2 / (1 + u ^ 2) = 1 ∧
        v ^ 2 / (1 + v ^ 2) = 0 ∧
        (u - v) ^ 2 / ((1 + u ^ 2) * (1 + v ^ 2)) = 1 := by
  constructor
  · unfold SpreadTriple tripleSpreadFunction
    ring1
  · rintro ⟨u, v, uDenominatorNonzero, _vDenominatorNonzero,
      firstValue, _secondValue, _thirdValue⟩
    have multiplied := congrArg (fun value : K => value * (1 + u ^ 2))
      firstValue
    rw [RFAP.ExplicitField.div_mul_cancel (u ^ 2) uDenominatorNonzero]
      at multiplied
    have oneEqualsZero : (1 : K) = 0 := by
      calc
        1 = 1 * (1 + u ^ 2) - u ^ 2 := by ring1
        _ = 0 := by rw [← multiplied]; ring1
    exact one_ne_zero oneEqualsZero

/-- Theorem 47 (Triple spread formula). -/
theorem triple_spread_formula
    (first second third : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull) :
    let s₁ := spread second third secondNonNull thirdNonNull
    let s₂ := spread first third firstNonNull thirdNonNull
    let s₃ := spread first second firstNonNull secondNonNull
    (s₁ + s₂ + s₃) ^ 2 =
      2 * (s₁ ^ 2 + s₂ ^ 2 + s₃ ^ 2) + 4 * s₁ * s₂ * s₃ := by
  dsimp only
  let firstNorm := lineNorm first
  let secondNorm := lineNorm second
  let thirdNorm := lineNorm third
  let firstCross := second.a * third.b - third.a * second.b
  let secondCross := first.a * third.b - third.a * first.b
  let thirdCross := first.a * second.b - second.a * first.b
  let denominator := firstNorm * secondNorm * thirdNorm
  let firstNumerator := firstNorm * firstCross ^ 2
  let secondNumerator := secondNorm * secondCross ^ 2
  let thirdNumerator := thirdNorm * thirdCross ^ 2
  let crossProduct := firstCross * secondCross * thirdCross
  have denominatorNonzero : denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero firstNonNull secondNonNull)
      thirdNonNull
  have firstSpread :
      spread second third secondNonNull thirdNonNull =
        firstNumerator / denominator := by
    unfold spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero secondNonNull thirdNonNull)
      denominatorNonzero
    unfold firstNumerator denominator firstNorm secondNorm thirdNorm firstCross lineNorm
    ring1
  have secondSpread :
      spread first third firstNonNull thirdNonNull =
        secondNumerator / denominator := by
    unfold spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero firstNonNull thirdNonNull)
      denominatorNonzero
    unfold secondNumerator denominator firstNorm secondNorm thirdNorm secondCross lineNorm
    ring1
  have thirdSpread :
      spread first second firstNonNull secondNonNull =
        thirdNumerator / denominator := by
    unfold spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero firstNonNull secondNonNull)
      denominatorNonzero
    unfold thirdNumerator denominator firstNorm secondNorm thirdNorm thirdCross lineNorm
    ring1
  have numeratorProduct :
      firstNumerator * secondNumerator * thirdNumerator =
        denominator * crossProduct ^ 2 := by
    unfold firstNumerator secondNumerator thirdNumerator denominator crossProduct
    ring1
  have clearedIdentity :
      (firstNumerator + secondNumerator + thirdNumerator) ^ 2 =
        2 * (firstNumerator ^ 2 + secondNumerator ^ 2 +
          thirdNumerator ^ 2) +
        4 * crossProduct ^ 2 := by
    unfold firstNumerator secondNumerator thirdNumerator crossProduct
    unfold firstNorm secondNorm thirdNorm firstCross secondCross thirdCross lineNorm
    ring1
  rw [firstSpread, secondSpread, thirdSpread]
  exact triple_fraction_identity firstNumerator secondNumerator thirdNumerator
    denominator crossProduct denominatorNonzero numeratorProduct clearedIdentity

/-- Theorem 47 in the book's `SpreadTriple` terminology. -/
theorem three_lines_form_spreadTriple
    (first second third : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull) :
    SpreadTriple
      (spread second third secondNonNull thirdNonNull)
      (spread first third firstNonNull thirdNonNull)
      (spread first second firstNonNull secondNonNull) := by
  unfold SpreadTriple tripleSpreadFunction
  rw [triple_spread_formula first second third firstNonNull secondNonNull
    thirdNonNull]
  ring1

/-- The normal-form calculation at the heart of Theorem 48. -/
theorem spread_from_ratio_normal_form
    (s₁ s₂ s₃ ratio : K)
    (s₂Nonzero : s₂ ≠ 0)
    (triple : SpreadTriple s₁ s₂ s₃)
    (givenRatio : s₁ / s₂ = ratio) :
    (s₃ / s₂ - ratio - 1) ^ 2 = 4 * ratio * (1 - s₃) := by
  have firstEquation : s₁ = ratio * s₂ := by
    calc
      s₁ = (s₁ / s₂) * s₂ :=
        (RFAP.ExplicitField.div_mul_cancel s₁ s₂Nonzero).symm
      _ = ratio * s₂ := by rw [givenRatio]
  have tripleForm := (exercise_7_6 triple).2.2.2.1
  let normalized := s₃ / s₂ - ratio - 1
  have scaledNormalized : normalized * s₂ = s₃ - s₁ - s₂ := by
    unfold normalized
    calc
      (s₃ / s₂ - ratio - 1) * s₂ =
          (s₃ / s₂) * s₂ - ratio * s₂ - s₂ := by ring1
      _ = s₃ - s₁ - s₂ := by
        rw [RFAP.ExplicitField.div_mul_cancel s₃ s₂Nonzero, firstEquation]
  have s₂SquareNonzero : s₂ ^ 2 ≠ 0 := by
    simpa [pow_two] using
      (RFAP.ExplicitField.mul_ne_zero s₂Nonzero s₂Nonzero)
  change normalized ^ 2 = 4 * ratio * (1 - s₃)
  apply eq_of_mul_eq_mul_right s₂SquareNonzero
  calc
    normalized ^ 2 * s₂ ^ 2 = (normalized * s₂) ^ 2 := by ring1
    _ = (s₃ - s₁ - s₂) ^ 2 := by rw [scaledNormalized]
    _ = 4 * s₁ * s₂ * (1 - s₃) := tripleForm
    _ = (4 * ratio * (1 - s₃)) * s₂ ^ 2 := by
      rw [firstEquation]
      ring1

/-- Theorem 48, square clause: the proof computes the root rather than
selecting it. -/
theorem spread_from_ratio_square
    (s₁ s₂ s₃ ratio : K)
    (twoNonzero : (2 : K) ≠ 0)
    (s₂Nonzero : s₂ ≠ 0)
    (triple : SpreadTriple s₁ s₂ s₃)
    (givenRatio : s₁ / s₂ = ratio) :
    IsSquare (ratio * (1 - s₃)) := by
  let normalized := s₃ / s₂ - ratio - 1
  have normalForm : normalized ^ 2 = 4 * ratio * (1 - s₃) :=
    spread_from_ratio_normal_form s₁ s₂ s₃ ratio s₂Nonzero triple givenRatio
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero := RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  refine ⟨normalized / 2, ?_⟩
  apply eq_of_mul_eq_mul_right fourNonzero
  calc
    (ratio * (1 - s₃)) * 4 = normalized ^ 2 := by
      rw [normalForm]
      ring1
    _ = ((normalized / 2) * 2) ^ 2 := by
      rw [RFAP.ExplicitField.div_mul_cancel normalized twoNonzero]
    _ = (normalized / 2) ^ 2 * 4 := by ring1

/-- Theorem 48, explicit `±` clause.  Each branch also records that its
displayed denominator is nonzero. -/
theorem spread_from_ratio_alternatives [DecidableEq K]
    (s₁ s₂ s₃ ratio root : K)
    (s₂Nonzero : s₂ ≠ 0) (s₃Nonzero : s₃ ≠ 0)
    (triple : SpreadTriple s₁ s₂ s₃)
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
    RFAP.ExplicitField.div_ne_zero s₃Nonzero s₂Nonzero
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
    apply eq_of_mul_eq_mul_right denominatorNonzero
    calc
      s₂ * (ratio + 1 + 2 * root) = s₂ * (s₃ / s₂) := by
        rw [denominatorEquation]
      _ = (s₃ / s₂) * s₂ := by ring1
      _ = s₃ := RFAP.ExplicitField.div_mul_cancel s₃ s₂Nonzero
      _ = (s₃ / (ratio + 1 + 2 * root)) *
          (ratio + 1 + 2 * root) :=
        (RFAP.ExplicitField.div_mul_cancel s₃ denominatorNonzero).symm
  · right
    have negativeFactorZero : normalized + 2 * root = 0 := by
      by_cases factorZero : normalized + 2 * root = 0
      · exact factorZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero positiveFactorZero factorZero)
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
    apply eq_of_mul_eq_mul_right denominatorNonzero
    calc
      s₂ * (ratio + 1 - 2 * root) = s₂ * (s₃ / s₂) := by
        rw [denominatorEquation]
      _ = (s₃ / s₂) * s₂ := by ring1
      _ = s₃ := RFAP.ExplicitField.div_mul_cancel s₃ s₂Nonzero
      _ = (s₃ / (ratio + 1 - 2 * root)) *
          (ratio + 1 - 2 * root) :=
        (RFAP.ExplicitField.div_mul_cancel s₃ denominatorNonzero).symm

/-- Theorem 48 (Spread from ratio), packaged exactly as the square conclusion
followed by the formula for any supplied square root. -/
theorem spread_from_ratio [DecidableEq K]
    (s₁ s₂ s₃ ratio : K)
    (twoNonzero : (2 : K) ≠ 0)
    (s₂Nonzero : s₂ ≠ 0) (s₃Nonzero : s₃ ≠ 0)
    (triple : SpreadTriple s₁ s₂ s₃)
    (givenRatio : s₁ / s₂ = ratio) :
    IsSquare (ratio * (1 - s₃)) ∧
      ∀ root : K, ratio * (1 - s₃) = root ^ 2 →
        ((ratio + 1 + 2 * root ≠ 0) ∧
            s₂ = s₃ / (ratio + 1 + 2 * root)) ∨
          ((ratio + 1 - 2 * root ≠ 0) ∧
            s₂ = s₃ / (ratio + 1 - 2 * root)) := by
  exact ⟨spread_from_ratio_square s₁ s₂ s₃ ratio twoNonzero s₂Nonzero
      triple givenRatio,
    fun root rootEquation => spread_from_ratio_alternatives s₁ s₂ s₃ ratio
      root s₂Nonzero s₃Nonzero triple givenRatio rootEquation⟩

/-- Theorem 49 (Triple cross formula), obtained by the finite substitutions
`cᵢ = 1 - sᵢ`. -/
theorem triple_cross_formula
    (first second third : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull) :
    let c₁ := cross second third secondNonNull thirdNonNull
    let c₂ := cross first third firstNonNull thirdNonNull
    let c₃ := cross first second firstNonNull secondNonNull
    (c₁ + c₂ + c₃ - 1) ^ 2 = 4 * c₁ * c₂ * c₃ := by
  dsimp only
  let s₁ := spread second third secondNonNull thirdNonNull
  let s₂ := spread first third firstNonNull thirdNonNull
  let s₃ := spread first second firstNonNull secondNonNull
  have spreadTriple : SpreadTriple s₁ s₂ s₃ :=
    three_lines_form_spreadTriple first second third firstNonNull secondNonNull
      thirdNonNull
  have complement := spreadTriple_complement_form spreadTriple
  have firstCross :
      cross second third secondNonNull thirdNonNull = 1 - s₁ := by
    have sum := spread_add_cross second third secondNonNull thirdNonNull
    unfold s₁
    calc
      cross second third secondNonNull thirdNonNull =
          (spread second third secondNonNull thirdNonNull +
            cross second third secondNonNull thirdNonNull) -
            spread second third secondNonNull thirdNonNull := by ring1
      _ = 1 - spread second third secondNonNull thirdNonNull := by rw [sum]
  have secondCross :
      cross first third firstNonNull thirdNonNull = 1 - s₂ := by
    have sum := spread_add_cross first third firstNonNull thirdNonNull
    unfold s₂
    calc
      cross first third firstNonNull thirdNonNull =
          (spread first third firstNonNull thirdNonNull +
            cross first third firstNonNull thirdNonNull) -
            spread first third firstNonNull thirdNonNull := by ring1
      _ = 1 - spread first third firstNonNull thirdNonNull := by rw [sum]
  have thirdCross :
      cross first second firstNonNull secondNonNull = 1 - s₃ := by
    have sum := spread_add_cross first second firstNonNull secondNonNull
    unfold s₃
    calc
      cross first second firstNonNull secondNonNull =
          (spread first second firstNonNull secondNonNull +
            cross first second firstNonNull secondNonNull) -
            spread first second firstNonNull secondNonNull := by ring1
      _ = 1 - spread first second firstNonNull secondNonNull := by rw [sum]
  rw [firstCross, secondCross, thirdCross]
  calc
    ((1 - s₁) + (1 - s₂) + (1 - s₃) - 1) ^ 2 =
        (s₁ + s₂ + s₃ - 2) ^ 2 := by ring1
    _ = 4 * (1 - s₁) * (1 - s₂) * (1 - s₃) := complement

/-- Exercise 7.7: both normal forms of the Triple cross formula.  The second
clause names the complementary spreads `s₁=1-c₁` and `s₂=1-c₂`
without adding any geometric or infinitary data. -/
theorem exercise_7_7
    (c₁ c₂ c₃ : K)
    (tripleCross : (c₁ + c₂ + c₃ - 1) ^ 2 = 4 * c₁ * c₂ * c₃) :
    (c₃ + c₁ + c₂ - 2 * c₁ * c₂ - 1) ^ 2 =
        4 * c₁ * c₂ * (1 - c₁) * (1 - c₂) ∧
      let s₁ := 1 - c₁
      let s₂ := 1 - c₂
      (c₃ - (c₁ * c₂ + s₁ * s₂)) ^ 2 =
        4 * c₁ * c₂ * s₁ * s₂ := by
  have differenceZero :
      (c₁ + c₂ + c₃ - 1) ^ 2 - 4 * c₁ * c₂ * c₃ = 0 := by
    rw [tripleCross]
    ring1
  constructor
  · apply sub_eq_zero.mp
    calc
      (c₃ + c₁ + c₂ - 2 * c₁ * c₂ - 1) ^ 2 -
          4 * c₁ * c₂ * (1 - c₁) * (1 - c₂) =
        (c₁ + c₂ + c₃ - 1) ^ 2 - 4 * c₁ * c₂ * c₃ := by
          ring1
      _ = 0 := differenceZero
  · dsimp only
    apply sub_eq_zero.mp
    calc
      (c₃ - (c₁ * c₂ + (1 - c₁) * (1 - c₂))) ^ 2 -
          4 * c₁ * c₂ * (1 - c₁) * (1 - c₂) =
        (c₁ + c₂ + c₃ - 1) ^ 2 - 4 * c₁ * c₂ * c₃ := by
          ring1
      _ = 0 := differenceZero

/-- The four-by-four determinant displayed in Exercise 7.8, expanded along
its first row. -/
def tripleCrossDeterminant (c₁ c₂ c₃ : K) : K :=
  (1 * (1 * 2 - 1 * 1) - c₃ * (c₃ * 2 - 1 * 1) +
      1 * (c₃ * 1 - 1 * 1)) -
    c₁ * (c₁ * (1 * 2 - 1 * 1) - c₃ * (c₂ * 2 - 1 * 1) +
      1 * (c₂ * 1 - 1 * 1)) +
    c₂ * (c₁ * (c₃ * 2 - 1 * 1) - 1 * (c₂ * 2 - 1 * 1) +
      1 * (c₂ * 1 - c₃ * 1)) -
    (c₁ * (c₃ * 1 - 1 * 1) - 1 * (c₂ * 1 - 1 * 1) +
      c₃ * (c₂ * 1 - c₃ * 1))

/-- Exercise 7.8: determinant form of the Triple cross polynomial. -/
theorem exercise_7_8 (c₁ c₂ c₃ : K) :
    (c₁ + c₂ + c₃ - 1) ^ 2 - 4 * c₁ * c₂ * c₃ =
      -tripleCrossDeterminant c₁ c₂ c₃ := by
  unfold tripleCrossDeterminant
  ring1

/-- Theorem 51 (Equal spreads).  The third spread is forced into the two
finite alternatives `0` and the logistic value `4s(1-s)`. -/
theorem equal_spreads [DecidableEq K]
    (first second third : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull)
    (equalSpreads :
      spread first second firstNonNull secondNonNull =
        spread second third secondNonNull thirdNonNull) :
    let s := spread first second firstNonNull secondNonNull
    let r := spread first third firstNonNull thirdNonNull
    r = 0 ∨ r = 4 * s * (1 - s) := by
  dsimp only
  let s := spread first second firstNonNull secondNonNull
  let r := spread first third firstNonNull thirdNonNull
  change s = spread second third secondNonNull thirdNonNull at equalSpreads
  have triple := triple_spread_formula first second third firstNonNull
    secondNonNull thirdNonNull
  change
    (spread second third secondNonNull thirdNonNull + r + s) ^ 2 =
      2 * ((spread second third secondNonNull thirdNonNull) ^ 2 +
        r ^ 2 + s ^ 2) +
        4 * spread second third secondNonNull thirdNonNull * r * s at triple
  rw [← equalSpreads] at triple
  have equation :
      (2 * s + r) ^ 2 =
        2 * (2 * s ^ 2 + r ^ 2) + 4 * s ^ 2 * r := by
    calc
      (2 * s + r) ^ 2 = (s + r + s) ^ 2 := by ring1
      _ = 2 * (s ^ 2 + r ^ 2 + s ^ 2) + 4 * s * r * s := triple
      _ = 2 * (2 * s ^ 2 + r ^ 2) + 4 * s ^ 2 * r := by ring1
  have factorZero : r * (r - 4 * s * (1 - s)) = 0 := by
    calc
      r * (r - 4 * s * (1 - s)) =
          -((2 * s + r) ^ 2 -
            (2 * (2 * s ^ 2 + r ^ 2) + 4 * s ^ 2 * r)) := by ring1
      _ = 0 := by rw [equation]; ring1
  by_cases rZero : r = 0
  · exact Or.inl rZero
  · right
    have secondFactorZero : r - 4 * s * (1 - s) = 0 := by
      by_cases factorZeroCase : r - 4 * s * (1 - s) = 0
      · exact factorZeroCase
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero rZero factorZeroCase) factorZero)
    calc
      r = (r - 4 * s * (1 - s)) + 4 * s * (1 - s) := by ring1
      _ = 4 * s * (1 - s) := by rw [secondFactorZero]; ring1

end DivineProportions
