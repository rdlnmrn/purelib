import DivineProportions.Trigonometry.TripleTwist
import DivineProportions.Trigonometry.Quadrea

/-!
# Divine Proportions, Chapter 7 field-fragment examples

The book's two complex examples need only one explicitly supplied element
`i` satisfying `i²=-1`.  Keeping that finite field fragment abstract makes the
same proofs usable in admissible finite fields and in the constructive
Gaussian rationals; no completed complex carrier is introduced.
-/

namespace DivineProportions

namespace ChapterSevenFieldFragments

variable {K : Type*} [RFAP.ExplicitField K]

/-- The finite expression `a+b i`. -/
def complexValue (i real imaginary : K) : K := real + imaginary * i

@[simp] private theorem complexValue_zero_imaginary (i real : K) :
    complexValue i real 0 = real := by
  unfold complexValue
  ring1

@[simp] private theorem complexValue_add
    (i a b c d : K) :
    complexValue i a b + complexValue i c d =
      complexValue i (a + c) (b + d) := by
  unfold complexValue
  ring1

@[simp] private theorem complexValue_sub
    (i a b c d : K) :
    complexValue i a b - complexValue i c d =
      complexValue i (a - c) (b - d) := by
  unfold complexValue
  ring1

@[simp] private theorem complexValue_neg (i a b : K) :
    -complexValue i a b = complexValue i (-a) (-b) := by
  unfold complexValue
  ring1

@[simp] private theorem complexValue_mul
    (i a b c d : K) (iSquare : i ^ 2 = -1) :
    complexValue i a b * complexValue i c d =
      complexValue i (a * c - b * d) (a * d + b * c) := by
  calc
    complexValue i a b * complexValue i c d =
        complexValue i (a * c - b * d) (a * d + b * c) +
          b * d * (i ^ 2 + 1) := by
            unfold complexValue
            ring1
    _ = complexValue i (a * c - b * d) (a * d + b * c) := by
      rw [iSquare]
      ring1

@[simp] private theorem complexValue_square
    (i a b : K) (iSquare : i ^ 2 = -1) :
    complexValue i a b ^ 2 =
      complexValue i (a ^ 2 - b ^ 2) (2 * a * b) := by
  rw [pow_two, complexValue_mul i a b a b iSquare]
  congr 1 <;> ring1

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
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
          rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) * rightDenominator⁻¹ := by
          ring1
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

private theorem i_nonzero [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1) : i ≠ 0 := by
  intro iZero
  have negativeOneZero : (-1 : K) = 0 := by
    calc
      (-1 : K) = i ^ 2 := iSquare.symm
      _ = 0 := by rw [iZero]; ring1
  exact one_ne_zero (by
    calc
      (1 : K) = -(-1) := by ring1
      _ = 0 := by rw [negativeOneZero]; ring1)

private theorem four_nonzero (twoNonzero : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  rw [show (4 : K) = 2 * 2 by ring1]
  exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero

/-- Componentwise division of `a+bi` by one nonzero scalar. -/
private theorem complexValue_div
    (i a b denominator : K) (denominatorNonzero : denominator ≠ 0) :
    complexValue i a b / denominator =
      complexValue i (a / denominator) (b / denominator) := by
  apply eq_of_mul_eq_mul_right denominatorNonzero
  calc
    (complexValue i a b / denominator) * denominator = complexValue i a b :=
      RFAP.ExplicitField.div_mul_cancel _ denominatorNonzero
    _ = complexValue i (a / denominator) (b / denominator) * denominator := by
      symm
      unfold complexValue
      calc
        (a / denominator + b / denominator * i) * denominator =
            (a / denominator) * denominator +
              (b / denominator) * denominator * i := by ring1
        _ = a + b * i := by
          rw [RFAP.ExplicitField.div_mul_cancel a denominatorNonzero,
            RFAP.ExplicitField.div_mul_cancel b denominatorNonzero]

/-- Three displayed fractions reduced to their product denominator. -/
private theorem three_fraction_sum
    (firstNumerator secondNumerator thirdNumerator
      firstDenominator secondDenominator thirdDenominator : K)
    (firstNonzero : firstDenominator ≠ 0)
    (secondNonzero : secondDenominator ≠ 0)
    (thirdNonzero : thirdDenominator ≠ 0) :
    firstNumerator / firstDenominator +
        secondNumerator / secondDenominator +
        thirdNumerator / thirdDenominator =
      (firstNumerator * secondDenominator * thirdDenominator +
          secondNumerator * firstDenominator * thirdDenominator +
          thirdNumerator * firstDenominator * secondDenominator) /
        (firstDenominator * secondDenominator * thirdDenominator) := by
  have denominatorNonzero :
      firstDenominator * secondDenominator * thirdDenominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero firstNonzero secondNonzero) thirdNonzero
  apply eq_of_mul_eq_mul_right denominatorNonzero
  calc
    (firstNumerator / firstDenominator +
          secondNumerator / secondDenominator +
          thirdNumerator / thirdDenominator) *
        (firstDenominator * secondDenominator * thirdDenominator) =
      (firstNumerator / firstDenominator * firstDenominator) *
          secondDenominator * thirdDenominator +
        (secondNumerator / secondDenominator * secondDenominator) *
          firstDenominator * thirdDenominator +
        (thirdNumerator / thirdDenominator * thirdDenominator) *
          firstDenominator * secondDenominator := by ring1
    _ = firstNumerator * secondDenominator * thirdDenominator +
        secondNumerator * firstDenominator * thirdDenominator +
        thirdNumerator * firstDenominator * secondDenominator := by
      rw [RFAP.ExplicitField.div_mul_cancel firstNumerator firstNonzero,
        RFAP.ExplicitField.div_mul_cancel secondNumerator secondNonzero,
        RFAP.ExplicitField.div_mul_cancel thirdNumerator thirdNonzero]
    _ = ((firstNumerator * secondDenominator * thirdDenominator +
          secondNumerator * firstDenominator * thirdDenominator +
          thirdNumerator * firstDenominator * secondDenominator) /
        (firstDenominator * secondDenominator * thirdDenominator)) *
          (firstDenominator * secondDenominator * thirdDenominator) :=
      (RFAP.ExplicitField.div_mul_cancel _ denominatorNonzero).symm

/-- Three fractions compared with an independently reduced target fraction. -/
private theorem three_fraction_sum_eq
    (firstNumerator secondNumerator thirdNumerator targetNumerator
      firstDenominator secondDenominator thirdDenominator targetDenominator : K)
    (firstNonzero : firstDenominator ≠ 0)
    (secondNonzero : secondDenominator ≠ 0)
    (thirdNonzero : thirdDenominator ≠ 0)
    (targetNonzero : targetDenominator ≠ 0)
    (crossProduct :
      (firstNumerator * secondDenominator * thirdDenominator +
          secondNumerator * firstDenominator * thirdDenominator +
          thirdNumerator * firstDenominator * secondDenominator) *
          targetDenominator =
        targetNumerator *
          (firstDenominator * secondDenominator * thirdDenominator)) :
    firstNumerator / firstDenominator +
        secondNumerator / secondDenominator +
        thirdNumerator / thirdDenominator =
      targetNumerator / targetDenominator := by
  calc
    firstNumerator / firstDenominator +
          secondNumerator / secondDenominator +
          thirdNumerator / thirdDenominator =
        (firstNumerator * secondDenominator * thirdDenominator +
            secondNumerator * firstDenominator * thirdDenominator +
            thirdNumerator * firstDenominator * secondDenominator) /
          (firstDenominator * secondDenominator * thirdDenominator) :=
      three_fraction_sum firstNumerator secondNumerator thirdNumerator
        firstDenominator secondDenominator thirdDenominator firstNonzero
        secondNonzero thirdNonzero
    _ = targetNumerator / targetDenominator := by
      apply ratio_eq_of_cross_product
        (RFAP.ExplicitField.mul_ne_zero
          (RFAP.ExplicitField.mul_ne_zero firstNonzero secondNonzero)
          thirdNonzero)
        targetNonzero
      exact crossProduct

/-- The corresponding common-denominator reduction with the cubic product
subtracted, as used by the Triple twist formula. -/
private theorem three_fraction_sum_sub_product_eq
    (firstNumerator secondNumerator thirdNumerator targetNumerator
      firstDenominator secondDenominator thirdDenominator targetDenominator : K)
    (firstNonzero : firstDenominator ≠ 0)
    (secondNonzero : secondDenominator ≠ 0)
    (thirdNonzero : thirdDenominator ≠ 0)
    (targetNonzero : targetDenominator ≠ 0)
    (crossProduct :
      (firstNumerator * secondDenominator * thirdDenominator +
          secondNumerator * firstDenominator * thirdDenominator +
          thirdNumerator * firstDenominator * secondDenominator -
          firstNumerator * secondNumerator * thirdNumerator) *
          targetDenominator =
        targetNumerator *
          (firstDenominator * secondDenominator * thirdDenominator)) :
    firstNumerator / firstDenominator +
        secondNumerator / secondDenominator +
        thirdNumerator / thirdDenominator -
        (firstNumerator / firstDenominator) *
          (secondNumerator / secondDenominator) *
          (thirdNumerator / thirdDenominator) =
      targetNumerator / targetDenominator := by
  have denominatorNonzero :
      firstDenominator * secondDenominator * thirdDenominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero firstNonzero secondNonzero) thirdNonzero
  calc
    firstNumerator / firstDenominator +
          secondNumerator / secondDenominator +
          thirdNumerator / thirdDenominator -
          firstNumerator / firstDenominator *
            (secondNumerator / secondDenominator) *
            (thirdNumerator / thirdDenominator) =
        (firstNumerator * secondDenominator * thirdDenominator +
            secondNumerator * firstDenominator * thirdDenominator +
            thirdNumerator * firstDenominator * secondDenominator -
            firstNumerator * secondNumerator * thirdNumerator) /
          (firstDenominator * secondDenominator * thirdDenominator) := by
      apply eq_of_mul_eq_mul_right denominatorNonzero
      calc
        (firstNumerator / firstDenominator +
              secondNumerator / secondDenominator +
              thirdNumerator / thirdDenominator -
              firstNumerator / firstDenominator *
                (secondNumerator / secondDenominator) *
                (thirdNumerator / thirdDenominator)) *
            (firstDenominator * secondDenominator * thirdDenominator) =
          (firstNumerator / firstDenominator * firstDenominator) *
                secondDenominator * thirdDenominator +
            (secondNumerator / secondDenominator * secondDenominator) *
                firstDenominator * thirdDenominator +
            (thirdNumerator / thirdDenominator * thirdDenominator) *
                firstDenominator * secondDenominator -
            (firstNumerator / firstDenominator * firstDenominator) *
              (secondNumerator / secondDenominator * secondDenominator) *
              (thirdNumerator / thirdDenominator * thirdDenominator) := by ring1
        _ = firstNumerator * secondDenominator * thirdDenominator +
              secondNumerator * firstDenominator * thirdDenominator +
              thirdNumerator * firstDenominator * secondDenominator -
              firstNumerator * secondNumerator * thirdNumerator := by
          rw [RFAP.ExplicitField.div_mul_cancel firstNumerator firstNonzero,
            RFAP.ExplicitField.div_mul_cancel secondNumerator secondNonzero,
            RFAP.ExplicitField.div_mul_cancel thirdNumerator thirdNonzero]
        _ = ((firstNumerator * secondDenominator * thirdDenominator +
              secondNumerator * firstDenominator * thirdDenominator +
              thirdNumerator * firstDenominator * secondDenominator -
              firstNumerator * secondNumerator * thirdNumerator) /
            (firstDenominator * secondDenominator * thirdDenominator)) *
              (firstDenominator * secondDenominator * thirdDenominator) :=
          (RFAP.ExplicitField.div_mul_cancel _ denominatorNonzero).symm
    _ = targetNumerator / targetDenominator := by
      apply ratio_eq_of_cross_product denominatorNonzero targetNonzero
      exact crossProduct

/-- Squaring one displayed fraction and reducing it by a supplied finite
cross-product certificate. -/
private theorem square_fraction_eq
    (numerator denominator targetNumerator targetDenominator : K)
    (denominatorNonzero : denominator ≠ 0)
    (targetNonzero : targetDenominator ≠ 0)
    (crossProduct :
      numerator ^ 2 * targetDenominator =
        targetNumerator * denominator ^ 2) :
    (numerator / denominator) ^ 2 =
      targetNumerator / targetDenominator := by
  have denominatorSquareNonzero : denominator ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero denominatorNonzero denominatorNonzero
  calc
    (numerator / denominator) ^ 2 = numerator ^ 2 / denominator ^ 2 := by
      apply eq_of_mul_eq_mul_right denominatorSquareNonzero
      calc
        (numerator / denominator) ^ 2 * denominator ^ 2 =
            ((numerator / denominator) * denominator) ^ 2 := by ring1
        _ = numerator ^ 2 := by
          rw [RFAP.ExplicitField.div_mul_cancel numerator denominatorNonzero]
        _ = (numerator ^ 2 / denominator ^ 2) * denominator ^ 2 :=
          (RFAP.ExplicitField.div_mul_cancel _ denominatorSquareNonzero).symm
    _ = targetNumerator / targetDenominator :=
      ratio_eq_of_cross_product denominatorSquareNonzero targetNonzero
        crossProduct

/-- Dividing a displayed fraction by one further nonzero scalar merely
multiplies its explicit denominator. -/
private theorem fraction_div
    (numerator denominator divisor : K)
    (denominatorNonzero : denominator ≠ 0) (divisorNonzero : divisor ≠ 0) :
    (numerator / denominator) / divisor =
      numerator / (denominator * divisor) := by
  have productNonzero :=
    RFAP.ExplicitField.mul_ne_zero denominatorNonzero divisorNonzero
  apply eq_of_mul_eq_mul_right productNonzero
  calc
    ((numerator / denominator) / divisor) * (denominator * divisor) =
        (((numerator / denominator) / divisor) * divisor) * denominator := by
      ring1
    _ = (numerator / denominator) * denominator := by
      rw [RFAP.ExplicitField.div_mul_cancel _ divisorNonzero]
    _ = numerator :=
      RFAP.ExplicitField.div_mul_cancel numerator denominatorNonzero
    _ = (numerator / (denominator * divisor)) *
        (denominator * divisor) :=
      (RFAP.ExplicitField.div_mul_cancel numerator productNonzero).symm

namespace ExampleSevenOne

def q₁ : K := complexValue (K := K) 0 1 0
def q₂ : K := complexValue (K := K) 0 (-1) 0

/-- The abstract `i` is supplied separately as the third quadrance. -/
def crossNumerator₁ (i : K) : K := complexValue i 4 3
def crossNumerator₂ (i : K) : K := complexValue i 4 (-3)
def crossNumerator₃ (i : K) : K := complexValue i 1 0

/-- Example 7.1's three Cross-law calculations and printed component forms. -/
theorem cross_values
    [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1) (twoNonzero : (2 : K) ≠ 0) :
    (((-1 : K) + i - 1) ^ 2) / (4 * (-1) * i) =
        complexValue i 1 (3 / 4) ∧
      ((i + 1 - (-1 : K)) ^ 2) / (4 * i * 1) =
        complexValue i 1 (-(3 / 4)) ∧
      (((1 : K) + (-1) - i) ^ 2) / (4 * 1 * (-1)) =
        complexValue i (1 / 4) 0 := by
  have iNonzero := i_nonzero i iSquare
  have fourNonzero := four_nonzero twoNonzero
  have firstDenominatorNonzero : (4 : K) * (-1) * i ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero fourNonzero (neg_ne_zero.mpr one_ne_zero))
      iNonzero
  have secondDenominatorNonzero : (4 : K) * i * 1 ≠ 0 := by
    simpa only [mul_one] using RFAP.ExplicitField.mul_ne_zero fourNonzero iNonzero
  have thirdDenominatorNonzero : (4 : K) * 1 * (-1) ≠ 0 := by
    simpa only [mul_one] using
      RFAP.ExplicitField.mul_ne_zero fourNonzero (neg_ne_zero.mpr one_ne_zero)
  constructor
  · calc
      (((-1 : K) + i - 1) ^ 2) / (4 * (-1) * i) =
          crossNumerator₁ i / 4 := by
        apply ratio_eq_of_cross_product firstDenominatorNonzero fourNonzero
        unfold crossNumerator₁ complexValue
        calc
          (((-1 : K) + i - 1) ^ 2) * 4 =
              (4 + 3 * i) * (4 * (-1) * i) + 16 * (i ^ 2 + 1) := by ring1
          _ = (4 + 3 * i) * (4 * (-1) * i) := by rw [iSquare]; ring1
      _ = complexValue i (4 / 4) (3 / 4) :=
        complexValue_div i 4 3 4 fourNonzero
      _ = complexValue i 1 (3 / 4) := by
        apply congrArg (fun value : K => complexValue i value (3 / 4))
        apply eq_of_mul_eq_mul_right fourNonzero
        rw [RFAP.ExplicitField.div_mul_cancel 4 fourNonzero]
        ring1
  constructor
  · calc
      ((i + 1 - (-1 : K)) ^ 2) / (4 * i * 1) =
          crossNumerator₂ i / 4 := by
        apply ratio_eq_of_cross_product secondDenominatorNonzero fourNonzero
        unfold crossNumerator₂ complexValue
        calc
          ((i + 1 - (-1 : K)) ^ 2) * 4 =
              (4 + (-3) * i) * (4 * i * 1) + 16 * (i ^ 2 + 1) := by ring1
          _ = (4 + (-3) * i) * (4 * i * 1) := by rw [iSquare]; ring1
      _ = complexValue i (4 / 4) ((-3) / 4) :=
        complexValue_div i 4 (-3) 4 fourNonzero
      _ = complexValue i 1 (-(3 / 4)) := by
        unfold complexValue
        have selfDivision : (4 : K) / 4 = 1 := by
          apply eq_of_mul_eq_mul_right fourNonzero
          rw [RFAP.ExplicitField.div_mul_cancel 4 fourNonzero]
          ring1
        rw [selfDivision]
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        ring1
  · calc
      (((1 : K) + (-1) - i) ^ 2) / (4 * 1 * (-1)) =
          crossNumerator₃ i / 4 := by
        apply ratio_eq_of_cross_product thirdDenominatorNonzero fourNonzero
        unfold crossNumerator₃ complexValue
        calc
          (((1 : K) + (-1) - i) ^ 2) * 4 =
              (1 + 0 * i) * (4 * 1 * (-1)) + 4 * (i ^ 2 + 1) := by ring1
          _ = (1 + 0 * i) * (4 * 1 * (-1)) := by rw [iSquare]; ring1
      _ = complexValue i (1 / 4) (0 / 4) :=
        complexValue_div i 1 0 4 fourNonzero
      _ = complexValue i (1 / 4) 0 := by
        rw [RFAP.ExplicitField.zero_div]

/-- Both sides of the Triple cross formula reduce to `25/16`. -/
theorem triple_cross_value
    (i : K) (iSquare : i ^ 2 = -1) (twoNonzero : (2 : K) ≠ 0) :
    let c₁ := complexValue i 1 (3 / 4)
    let c₂ := complexValue i 1 (-(3 / 4))
    let c₃ := complexValue i (1 / 4) 0
    (c₁ + c₂ + c₃ - 1) ^ 2 = 25 / 16 ∧
      4 * c₁ * c₂ * c₃ = 25 / 16 := by
  dsimp only
  have fourNonzero := four_nonzero twoNonzero
  have sixteenNonzero : (16 : K) ≠ 0 := by
    rw [show (16 : K) = 4 * 4 by ring1]
    exact RFAP.ExplicitField.mul_ne_zero fourNonzero fourNonzero
  have fourCancel := RFAP.ExplicitField.mul_inv_cancel (4 : K) fourNonzero
  have sixteenCancel := RFAP.ExplicitField.mul_inv_cancel (16 : K) sixteenNonzero
  have rightScaled : ((25 : K) * 16⁻¹) * 16 = 25 := by
    calc
      ((25 : K) * 16⁻¹) * 16 = 25 * (16 * 16⁻¹) := by ring1
      _ = 25 := by rw [sixteenCancel]; ring1
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  constructor
  · unfold complexValue
    apply eq_of_mul_eq_mul_right sixteenNonzero
    rw [rightScaled]
    calc
      ((1 + 3 * 4⁻¹ * i + (1 + -(3 * 4⁻¹) * i) +
            (1 * 4⁻¹ + 0 * i) - 1) ^ 2) * 16 =
          25 + (4 * 4⁻¹ - 1) * (4 * 4⁻¹ + 9) := by ring1
      _ = 25 := by rw [fourCancel]; ring1
  · unfold complexValue
    apply eq_of_mul_eq_mul_right sixteenNonzero
    rw [rightScaled]
    calc
      (4 * (1 + 3 * 4⁻¹ * i) * (1 + -(3 * 4⁻¹) * i) *
          (1 * 4⁻¹ + 0 * i)) * 16 =
        25 + (4 * 4⁻¹ - 1) *
            (144 * (4⁻¹) ^ 2 + 36 * 4⁻¹ + 25) -
          576 * (4⁻¹) ^ 3 * (i ^ 2 + 1) := by ring1
      _ = 25 := by rw [fourCancel, iSquare]; ring1

end ExampleSevenOne

namespace ExampleSevenFour

/-- Exactly the prime-characteristic exclusions needed by the denominators in
Example 7.4.  They hold in the constructive Gaussian rationals and in every
finite field fragment whose characteristic avoids these six primes. -/
structure AdmissibleCharacteristic (K : Type*) [RFAP.ExplicitField K] : Prop where
  twoNonzero : (2 : K) ≠ 0
  threeNonzero : (3 : K) ≠ 0
  fiveNonzero : (5 : K) ≠ 0
  thirteenNonzero : (13 : K) ≠ 0
  seventeenNonzero : (17 : K) ≠ 0
  fortyOneNonzero : (41 : K) ≠ 0

private theorem mul_three_ne_zero {a b c : K}
    (aNonzero : a ≠ 0) (bNonzero : b ≠ 0) (cNonzero : c ≠ 0) :
    a * b * c ≠ 0 :=
  RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero aNonzero bNonzero) cNonzero

private theorem mul_four_ne_zero {a b c d : K}
    (aNonzero : a ≠ 0) (bNonzero : b ≠ 0) (cNonzero : c ≠ 0)
    (dNonzero : d ≠ 0) : a * b * c * d ≠ 0 :=
  RFAP.ExplicitField.mul_ne_zero
    (mul_three_ne_zero aNonzero bNonzero cNonzero) dNonzero

private theorem eight_nonzero
    (admissible : AdmissibleCharacteristic K) : (8 : K) ≠ 0 := by
  rw [show (8 : K) = 2 * 2 * 2 by ring1]
  exact mul_three_ne_zero admissible.twoNonzero admissible.twoNonzero
    admissible.twoNonzero

private theorem twenty_nonzero
    (admissible : AdmissibleCharacteristic K) : (20 : K) ≠ 0 := by
  rw [show (20 : K) = 2 * 2 * 5 by ring1]
  exact mul_three_ne_zero admissible.twoNonzero admissible.twoNonzero
    admissible.fiveNonzero

private theorem thirtyFour_nonzero
    (admissible : AdmissibleCharacteristic K) : (34 : K) ≠ 0 := by
  rw [show (34 : K) = 2 * 17 by ring1]
  exact RFAP.ExplicitField.mul_ne_zero admissible.twoNonzero
    admissible.seventeenNonzero

private theorem forty_nonzero
    (admissible : AdmissibleCharacteristic K) : (40 : K) ≠ 0 := by
  rw [show (40 : K) = 2 * 2 * 2 * 5 by ring1]
  exact mul_four_ne_zero admissible.twoNonzero admissible.twoNonzero
    admissible.twoNonzero admissible.fiveNonzero

private theorem fiftyTwo_nonzero
    (admissible : AdmissibleCharacteristic K) : (52 : K) ≠ 0 := by
  rw [show (52 : K) = 2 * 2 * 13 by ring1]
  exact mul_three_ne_zero admissible.twoNonzero admissible.twoNonzero
    admissible.thirteenNonzero

private theorem sixtyFive_nonzero
    (admissible : AdmissibleCharacteristic K) : (65 : K) ≠ 0 := by
  rw [show (65 : K) = 5 * 13 by ring1]
  exact RFAP.ExplicitField.mul_ne_zero admissible.fiveNonzero
    admissible.thirteenNonzero

private theorem eightyTwo_nonzero
    (admissible : AdmissibleCharacteristic K) : (82 : K) ≠ 0 := by
  rw [show (82 : K) = 2 * 41 by ring1]
  exact RFAP.ExplicitField.mul_ne_zero admissible.twoNonzero
    admissible.fortyOneNonzero

private theorem oneHundredFour_nonzero
    (admissible : AdmissibleCharacteristic K) : (104 : K) ≠ 0 := by
  rw [show (104 : K) = 2 * 2 * 2 * 13 by ring1]
  exact mul_four_ne_zero admissible.twoNonzero admissible.twoNonzero
    admissible.twoNonzero admissible.thirteenNonzero

private theorem oneHundredThirty_nonzero
    (admissible : AdmissibleCharacteristic K) : (130 : K) ≠ 0 := by
  rw [show (130 : K) = 2 * 5 * 13 by ring1]
  exact mul_three_ne_zero admissible.twoNonzero admissible.fiveNonzero
    admissible.thirteenNonzero

private theorem nine_nonzero
    (admissible : AdmissibleCharacteristic K) : (9 : K) ≠ 0 := by
  rw [show (9 : K) = 3 * 3 by ring1]
  exact RFAP.ExplicitField.mul_ne_zero admissible.threeNonzero
    admissible.threeNonzero

private theorem eighteen_nonzero
    (admissible : AdmissibleCharacteristic K) : (18 : K) ≠ 0 := by
  rw [show (18 : K) = 2 * 3 * 3 by ring1]
  exact mul_three_ne_zero admissible.twoNonzero admissible.threeNonzero
    admissible.threeNonzero

private theorem twoHundredEightyNine_nonzero
    (admissible : AdmissibleCharacteristic K) : (289 : K) ≠ 0 := by
  rw [show (289 : K) = 17 * 17 by ring1]
  exact RFAP.ExplicitField.mul_ne_zero admissible.seventeenNonzero
    admissible.seventeenNonzero

private theorem fiveHundredTwenty_nonzero
    (admissible : AdmissibleCharacteristic K) : (520 : K) ≠ 0 := by
  rw [show (520 : K) = (2 * 2 * 2 * 5) * 13 by ring1]
  exact RFAP.ExplicitField.mul_ne_zero
    (mul_four_ne_zero admissible.twoNonzero admissible.twoNonzero
      admissible.twoNonzero admissible.fiveNonzero)
    admissible.thirteenNonzero

private theorem oneThousandForty_nonzero
    (admissible : AdmissibleCharacteristic K) : (1040 : K) ≠ 0 := by
  rw [show (1040 : K) = 2 * (2 * 2 * 2 * 5) * 13 by ring1]
  exact mul_three_ne_zero admissible.twoNonzero
    (mul_four_ne_zero admissible.twoNonzero admissible.twoNonzero
      admissible.twoNonzero admissible.fiveNonzero)
    admissible.thirteenNonzero

private theorem oneThousandSixHundredEightyOne_nonzero
    (admissible : AdmissibleCharacteristic K) : (1681 : K) ≠ 0 := by
  rw [show (1681 : K) = 41 * 41 by ring1]
  exact RFAP.ExplicitField.mul_ne_zero admissible.fortyOneNonzero
    admissible.fortyOneNonzero

private theorem twoThousandNinetyOne_nonzero
    (admissible : AdmissibleCharacteristic K) : (2091 : K) ≠ 0 := by
  rw [show (2091 : K) = 3 * 17 * 41 by ring1]
  exact mul_three_ne_zero admissible.threeNonzero
    admissible.seventeenNonzero admissible.fortyOneNonzero

private theorem fourThousandTwoHundredTwentyFive_nonzero
    (admissible : AdmissibleCharacteristic K) : (4225 : K) ≠ 0 := by
  rw [show (4225 : K) = (5 * 5) * (13 * 13) by ring1]
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero admissible.fiveNonzero
      admissible.fiveNonzero)
    (RFAP.ExplicitField.mul_ne_zero admissible.thirteenNonzero
      admissible.thirteenNonzero)

private theorem oneHundredThirtyFiveThousandTwoHundred_nonzero
    (admissible : AdmissibleCharacteristic K) : (135200 : K) ≠ 0 := by
  rw [show (135200 : K) =
      (2 * 2 * 2 * 2 * 2) * (5 * 5) * (13 * 13) by ring1]
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero
        (mul_four_ne_zero admissible.twoNonzero admissible.twoNonzero
          admissible.twoNonzero admissible.twoNonzero)
        admissible.twoNonzero)
      (RFAP.ExplicitField.mul_ne_zero admissible.fiveNonzero
        admissible.fiveNonzero))
    (RFAP.ExplicitField.mul_ne_zero admissible.thirteenNonzero
      admissible.thirteenNonzero)

private theorem oneMillionFourHundredFiftySevenThousandFourHundredTwentySeven_nonzero
    (admissible : AdmissibleCharacteristic K) : (1457427 : K) ≠ 0 := by
  rw [show (1457427 : K) = 3 * (17 * 17) * (41 * 41) by ring1]
  exact mul_three_ne_zero admissible.threeNonzero
    (RFAP.ExplicitField.mul_ne_zero admissible.seventeenNonzero
      admissible.seventeenNonzero)
    (RFAP.ExplicitField.mul_ne_zero admissible.fortyOneNonzero
      admissible.fortyOneNonzero)

private theorem fourMillionThreeHundredSeventyTwoThousandTwoHundredEightyOne_nonzero
    (admissible : AdmissibleCharacteristic K) : (4372281 : K) ≠ 0 := by
  rw [show (4372281 : K) = (3 * 3) * (17 * 17) * (41 * 41) by ring1]
  exact mul_three_ne_zero
    (RFAP.ExplicitField.mul_ne_zero admissible.threeNonzero
      admissible.threeNonzero)
    (RFAP.ExplicitField.mul_ne_zero admissible.seventeenNonzero
      admissible.seventeenNonzero)
    (RFAP.ExplicitField.mul_ne_zero admissible.fortyOneNonzero
      admissible.fortyOneNonzero)

/-- The origin vertex `A₁=[0,0]`. -/
def point₁ : Point K := ⟨0, 0⟩

/-- The second vertex `A₂=[3,-i]`. -/
def point₂ (i : K) : Point K := ⟨3, -i⟩

/-- The third vertex `A₃=[1+i,2i]`. -/
def point₃ (i : K) : Point K := ⟨1 + i, 2 * i⟩

/-- The side `A₂A₃`, with the exact coefficient triple
`⟨-3i:-2+i:-1+7i⟩`. -/
def line₁ (i : K) (threeNonzero : (3 : K) ≠ 0) (iNonzero : i ≠ 0) :
    Line K where
  a := -3 * i
  b := -2 + i
  c := complexValue i (-1) 7
  direction_nonzero := Or.inl
    (RFAP.ExplicitField.mul_ne_zero (neg_ne_zero.mpr threeNonzero) iNonzero)

/-- The side `A₁A₃`, represented by `⟨-2i:1+i:0⟩`. -/
def line₂ (i : K) (twoNonzero : (2 : K) ≠ 0) (iNonzero : i ≠ 0) :
    Line K where
  a := -2 * i
  b := 1 + i
  c := 0
  direction_nonzero := Or.inl
    (RFAP.ExplicitField.mul_ne_zero (neg_ne_zero.mpr twoNonzero) iNonzero)

/-- The side `A₁A₂`, represented by `⟨i:3:0⟩`. -/
def line₃ (i : K) (iNonzero : i ≠ 0) : Line K where
  a := i
  b := 3
  c := 0
  direction_nonzero := Or.inl iNonzero

/-- The three quadrances printed in Example 7.4. -/
theorem quadrance_values
    (i : K) (iSquare : i ^ 2 = -1) :
    quadrance (point₂ i) (point₃ i) = complexValue i (-6) (-4) ∧
      quadrance point₁ (point₃ i) = complexValue i (-4) 2 ∧
      quadrance point₁ (point₂ i) = 8 := by
  constructor
  · unfold quadrance point₂ point₃ complexValue
    calc
      ((1 + i - 3) ^ 2 + (2 * i - -i) ^ 2) =
          (-6 + -4 * i) + 10 * (i ^ 2 + 1) := by ring1
      _ = -6 + -4 * i := by rw [iSquare]; ring1
  constructor
  · unfold quadrance point₁ point₃ complexValue
    calc
      ((1 + i - 0) ^ 2 + (2 * i - 0) ^ 2) =
          (-4 + 2 * i) + 5 * (i ^ 2 + 1) := by ring1
      _ = -4 + 2 * i := by rw [iSquare]; ring1
  · unfold quadrance point₁ point₂
    calc
      ((3 : K) - 0) ^ 2 + (-i - 0) ^ 2 = 8 + (i ^ 2 + 1) := by ring1
      _ = 8 := by rw [iSquare]; ring1

/-- The printed quadrea `-192-56i`. -/
theorem quadrea_value (i : K) (iSquare : i ^ 2 = -1) :
    quadrea point₁ (point₂ i) (point₃ i) =
      complexValue i (-192) (-56) := by
  rw [quadrea_coordinate_formula]
  have determinantValue :
      pointDeterminant point₁ (point₂ i) (point₃ i) =
        complexValue i (-1) 7 := by
    unfold pointDeterminant point₁ point₂ point₃ complexValue
    change
      0 * (-i) - 0 * (2 * i) + 3 * (2 * i) - (1 + i) * (-i) +
          (1 + i) * 0 - 3 * 0 = -1 + 7 * i
    calc
      0 * (-i) - 0 * (2 * i) + 3 * (2 * i) - (1 + i) * (-i) +
          (1 + i) * 0 - 3 * 0 =
        i ^ 2 + 7 * i := by ring1
      _ = -1 + 7 * i := by rw [iSquare]
  rw [determinantValue, complexValue_square i (-1) 7 iSquare]
  unfold complexValue
  ring1

/-- Each displayed side contains its two defining vertices. -/
theorem line_incidence [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := i_nonzero i iSquare
    (line₁ i admissible.threeNonzero iNonzero).Contains (point₂ i) ∧
      (line₁ i admissible.threeNonzero iNonzero).Contains (point₃ i) ∧
      (line₂ i admissible.twoNonzero iNonzero).Contains point₁ ∧
      (line₂ i admissible.twoNonzero iNonzero).Contains (point₃ i) ∧
      (line₃ i iNonzero).Contains point₁ ∧
      (line₃ i iNonzero).Contains (point₂ i) := by
  dsimp only
  unfold Line.Contains line₁ line₂ line₃ point₁ point₂ point₃
  unfold complexValue
  constructor
  · calc
      (-3 * i) * 3 + (-2 + i) * -i + (-1 + 7 * i) =
          -(i ^ 2 + 1) := by ring1
      _ = 0 := by rw [iSquare]; ring1
  constructor
  · calc
      (-3 * i) * (1 + i) + (-2 + i) * (2 * i) + (-1 + 7 * i) =
          -(i ^ 2 + 1) := by ring1
      _ = 0 := by rw [iSquare]; ring1
  exact ⟨by ring1, by ring1, by ring1, by ring1⟩

/-- The side norms are the opposite quadrances, as printed. -/
theorem line_norm_values [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := i_nonzero i iSquare
    lineNorm (line₁ i admissible.threeNonzero iNonzero) =
        complexValue i (-6) (-4) ∧
      lineNorm (line₂ i admissible.twoNonzero iNonzero) =
        complexValue i (-4) 2 ∧
      lineNorm (line₃ i iNonzero) = 8 := by
  dsimp only
  unfold lineNorm line₁ line₂ line₃ complexValue
  constructor
  · calc
      (-3 * i) ^ 2 + (-2 + i) ^ 2 =
          (-6 + -4 * i) + 10 * (i ^ 2 + 1) := by ring1
      _ = -6 + -4 * i := by rw [iSquare]; ring1
  constructor
  · calc
      (-2 * i) ^ 2 + (1 + i) ^ 2 =
          (-4 + 2 * i) + 5 * (i ^ 2 + 1) := by ring1
      _ = -4 + 2 * i := by rw [iSquare]; ring1
  · calc
      i ^ 2 + (3 : K) ^ 2 = 8 + (i ^ 2 + 1) := by ring1
      _ = 8 := by rw [iSquare]; ring1

private theorem firstQuadrance_nonzero
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    complexValue i (-6) (-4) ≠ 0 := by
  intro valueZero
  apply fiftyTwo_nonzero admissible
  calc
    (52 : K) = complexValue i (-6) (-4) * complexValue i (-6) 4 := by
      rw [complexValue_mul i (-6) (-4) (-6) 4 iSquare]
      unfold complexValue
      ring1
    _ = 0 := by rw [valueZero]; ring1

private theorem secondQuadrance_nonzero
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    complexValue i (-4) 2 ≠ 0 := by
  intro valueZero
  apply twenty_nonzero admissible
  calc
    (20 : K) = complexValue i (-4) 2 * complexValue i (-4) (-2) := by
      rw [complexValue_mul i (-4) 2 (-4) (-2) iSquare]
      unfold complexValue
      ring1
    _ = 0 := by rw [valueZero]; ring1

/-- The three side lines are non-null, with constructive witnesses obtained
from the small integer norms `52`, `20`, and `8`. -/
theorem side_nonNull [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := i_nonzero i iSquare
    ¬ (line₁ i admissible.threeNonzero iNonzero).IsNull ∧
      ¬ (line₂ i admissible.twoNonzero iNonzero).IsNull ∧
      ¬ (line₃ i iNonzero).IsNull := by
  dsimp only
  have norms := line_norm_values i iSquare admissible
  constructor
  · intro firstNull
    exact firstQuadrance_nonzero i iSquare admissible (norms.1.symm.trans firstNull)
  constructor
  · intro secondNull
    exact secondQuadrance_nonzero i iSquare admissible
      (norms.2.1.symm.trans secondNull)
  · intro thirdNull
    exact eight_nonzero admissible (norms.2.2.symm.trans thirdNull)

theorem line₁_nonNull [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    ¬ (line₁ i admissible.threeNonzero (i_nonzero i iSquare)).IsNull :=
  (side_nonNull i iSquare admissible).1

theorem line₂_nonNull [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    ¬ (line₂ i admissible.twoNonzero (i_nonzero i iSquare)).IsNull :=
  (side_nonNull i iSquare admissible).2.1

theorem line₃_nonNull [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    ¬ (line₃ i (i_nonzero i iSquare)).IsNull :=
  (side_nonNull i iSquare admissible).2.2

/-- All three oriented side-pair determinants equal `1-7i`; their square is
the common spread numerator `-48-14i`. -/
theorem determinant_values [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    second.a * third.b - third.a * second.b = complexValue i 1 (-7) ∧
      first.a * third.b - third.a * first.b = complexValue i 1 (-7) ∧
      first.a * second.b - second.a * first.b = complexValue i 1 (-7) := by
  dsimp only
  unfold line₁ line₂ line₃ complexValue
  constructor
  · calc
      (-2 * i) * 3 - i * (1 + i) =
          (1 + -7 * i) - (i ^ 2 + 1) := by ring1
      _ = 1 + -7 * i := by rw [iSquare]; ring1
  constructor
  · calc
      (-3 * i) * 3 - i * (-2 + i) =
          (1 + -7 * i) - (i ^ 2 + 1) := by ring1
      _ = 1 + -7 * i := by rw [iSquare]; ring1
  · calc
      (-3 * i) * (1 + i) - (-2 * i) * (-2 + i) =
          (1 + -7 * i) - (i ^ 2 + 1) := by ring1
      _ = 1 + -7 * i := by rw [iSquare]; ring1

private theorem determinant_square_value [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    (second.a * third.b - third.a * second.b) ^ 2 =
        complexValue i (-48) (-14) ∧
      (first.a * third.b - third.a * first.b) ^ 2 =
        complexValue i (-48) (-14) ∧
      (first.a * second.b - second.a * first.b) ^ 2 =
        complexValue i (-48) (-14) := by
  dsimp only
  have determinants := determinant_values i iSquare admissible
  rw [determinants.1, determinants.2.1, determinants.2.2,
    complexValue_square i 1 (-7) iSquare]
  unfold complexValue
  exact ⟨by ring1, by ring1, by ring1⟩

/-- The three dot products used by the twists are `5+3i`, `-3+3i`, and
`-9-i`. -/
theorem dot_values [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    second.a * third.a + second.b * third.b = complexValue i 5 3 ∧
      first.a * third.a + first.b * third.b = complexValue i (-3) 3 ∧
      first.a * second.a + first.b * second.b = complexValue i (-9) (-1) := by
  dsimp only
  unfold line₁ line₂ line₃ complexValue
  constructor
  · calc
      (-2 * i) * i + (1 + i) * 3 =
          (5 + 3 * i) - 2 * (i ^ 2 + 1) := by ring1
      _ = 5 + 3 * i := by rw [iSquare]; ring1
  constructor
  · calc
      (-3 * i) * i + (-2 + i) * 3 =
          (-3 + 3 * i) - 3 * (i ^ 2 + 1) := by ring1
      _ = -3 + 3 * i := by rw [iSquare]; ring1
  · calc
      (-3 * i) * (-2 * i) + (-2 + i) * (1 + i) =
          (-9 + -1 * i) + 7 * (i ^ 2 + 1) := by ring1
      _ = -9 + -1 * i := by rw [iSquare]; ring1

/-- The three spreads in a single-denominator component form. -/
theorem spread_common_denominator_values [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    spread second third (line₂_nonNull i iSquare admissible)
        (line₃_nonNull i iSquare admissible) =
          complexValue i 41 38 / 40 ∧
      spread first third (line₁_nonNull i iSquare admissible)
        (line₃_nonNull i iSquare admissible) =
          complexValue i 86 (-27) / 104 ∧
      spread first second (line₁_nonNull i iSquare admissible)
        (line₂_nonNull i iSquare admissible) =
          complexValue i (-199) (-32) / 130 := by
  dsimp only
  have norms := line_norm_values i iSquare admissible
  have determinants := determinant_square_value i iSquare admissible
  constructor
  · unfold spread
    rw [determinants.1, norms.2.1, norms.2.2]
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero
        (secondQuadrance_nonzero i iSquare admissible)
        (eight_nonzero admissible))
      (forty_nonzero admissible)
    have denominatorValue :
        complexValue i (-4) 2 * 8 = complexValue i (-32) 16 := by
      unfold complexValue
      ring1
    rw [denominatorValue,
      complexValue_mul i 41 38 (-32) 16 iSquare]
    unfold complexValue
    ring1
  constructor
  · unfold spread
    rw [determinants.2.1, norms.1, norms.2.2]
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero
        (firstQuadrance_nonzero i iSquare admissible)
        (eight_nonzero admissible))
      (oneHundredFour_nonzero admissible)
    have denominatorValue :
        complexValue i (-6) (-4) * 8 = complexValue i (-48) (-32) := by
      unfold complexValue
      ring1
    rw [denominatorValue,
      complexValue_mul i 86 (-27) (-48) (-32) iSquare]
    unfold complexValue
    ring1
  · unfold spread
    rw [determinants.2.2, norms.1, norms.2.1]
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero
        (firstQuadrance_nonzero i iSquare admissible)
        (secondQuadrance_nonzero i iSquare admissible))
      (oneHundredThirty_nonzero admissible)
    rw [complexValue_mul i (-6) (-4) (-4) 2 iSquare]
    have denominatorValue :
        complexValue i (-6 * -4 - -4 * 2) (-6 * 2 + -4 * -4) =
          complexValue i 32 4 := by
      unfold complexValue
      ring1
    rw [denominatorValue,
      complexValue_mul i (-199) (-32) 32 4 iSquare]
    unfold complexValue
    ring1

/-- Example 7.4's three spreads in precisely the reduced component form
printed in the book. -/
theorem spread_values [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    spread second third (line₂_nonNull i iSquare admissible)
        (line₃_nonNull i iSquare admissible) =
          complexValue i (41 / 40) (19 / 20) ∧
      spread first third (line₁_nonNull i iSquare admissible)
        (line₃_nonNull i iSquare admissible) =
          complexValue i (43 / 52) (-(27 / 104)) ∧
      spread first second (line₁_nonNull i iSquare admissible)
        (line₂_nonNull i iSquare admissible) =
          complexValue i (-(199 / 130)) (-(16 / 65)) := by
  dsimp only
  have common := spread_common_denominator_values i iSquare admissible
  have firstImaginary : (38 : K) / 40 = 19 / 20 := by
    apply ratio_eq_of_cross_product (forty_nonzero admissible)
      (twenty_nonzero admissible)
    ring1
  have secondReal : (86 : K) / 104 = 43 / 52 := by
    apply ratio_eq_of_cross_product (oneHundredFour_nonzero admissible)
      (fiftyTwo_nonzero admissible)
    ring1
  have thirdImaginary : ((-32 : K) / 130) = -(16 / 65) := by
    calc
      ((-32 : K) / 130) = (-16) / 65 := by
        apply ratio_eq_of_cross_product (oneHundredThirty_nonzero admissible)
          (sixtyFive_nonzero admissible)
        ring1
      _ = -(16 / 65) := by
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        ring1
  constructor
  · calc
      spread (line₂ i admissible.twoNonzero (i_nonzero i iSquare))
          (line₃ i (i_nonzero i iSquare))
          (line₂_nonNull i iSquare admissible)
          (line₃_nonNull i iSquare admissible) =
        complexValue i 41 38 / 40 := common.1
      _ = complexValue i (41 / 40) (38 / 40) :=
        complexValue_div i 41 38 40 (forty_nonzero admissible)
      _ = complexValue i (41 / 40) (19 / 20) := by rw [firstImaginary]
  constructor
  · calc
      spread (line₁ i admissible.threeNonzero (i_nonzero i iSquare))
          (line₃ i (i_nonzero i iSquare))
          (line₁_nonNull i iSquare admissible)
          (line₃_nonNull i iSquare admissible) =
        complexValue i 86 (-27) / 104 := common.2.1
      _ = complexValue i (86 / 104) ((-27) / 104) :=
        complexValue_div i 86 (-27) 104 (oneHundredFour_nonzero admissible)
      _ = complexValue i (43 / 52) (-(27 / 104)) := by
        rw [secondReal]
        unfold complexValue
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        ring1
  · calc
      spread (line₁ i admissible.threeNonzero (i_nonzero i iSquare))
          (line₂ i admissible.twoNonzero (i_nonzero i iSquare))
          (line₁_nonNull i iSquare admissible)
          (line₂_nonNull i iSquare admissible) =
        complexValue i (-199) (-32) / 130 := common.2.2
      _ = complexValue i ((-199) / 130) ((-32) / 130) :=
        complexValue_div i (-199) (-32) 130
          (oneHundredThirty_nonzero admissible)
      _ = complexValue i (-(199 / 130)) (-(16 / 65)) := by
        rw [thirdImaginary]
        unfold complexValue
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        ring1

/-- The three quotients in the Spread law have the common single-denominator
value `(-199-32i)/1040`. -/
theorem spread_law_common_value [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    let s₁ := spread second third (line₂_nonNull i iSquare admissible)
      (line₃_nonNull i iSquare admissible)
    let s₂ := spread first third (line₁_nonNull i iSquare admissible)
      (line₃_nonNull i iSquare admissible)
    let s₃ := spread first second (line₁_nonNull i iSquare admissible)
      (line₂_nonNull i iSquare admissible)
    s₁ / complexValue i (-6) (-4) = complexValue i (-199) (-32) / 1040 ∧
      s₂ / complexValue i (-4) 2 = complexValue i (-199) (-32) / 1040 ∧
      s₃ / 8 = complexValue i (-199) (-32) / 1040 := by
  dsimp only
  have spreads := spread_common_denominator_values i iSquare admissible
  constructor
  · rw [spreads.1]
    calc
      (complexValue i 41 38 / 40) / complexValue i (-6) (-4) =
          complexValue i 41 38 /
            (40 * complexValue i (-6) (-4)) :=
        fraction_div _ _ _ (forty_nonzero admissible)
          (firstQuadrance_nonzero i iSquare admissible)
      _ = complexValue i (-199) (-32) / 1040 := by
        apply ratio_eq_of_cross_product
          (RFAP.ExplicitField.mul_ne_zero (forty_nonzero admissible)
            (firstQuadrance_nonzero i iSquare admissible))
          (oneThousandForty_nonzero admissible)
        have scaledQuadrance :
            (40 : K) * complexValue i (-6) (-4) =
              complexValue i (-240) (-160) := by
          unfold complexValue
          ring1
        rw [scaledQuadrance,
          complexValue_mul i (-199) (-32) (-240) (-160) iSquare]
        unfold complexValue
        ring1
  constructor
  · rw [spreads.2.1]
    calc
      (complexValue i 86 (-27) / 104) / complexValue i (-4) 2 =
          complexValue i 86 (-27) /
            (104 * complexValue i (-4) 2) :=
        fraction_div _ _ _ (oneHundredFour_nonzero admissible)
          (secondQuadrance_nonzero i iSquare admissible)
      _ = complexValue i (-199) (-32) / 1040 := by
        apply ratio_eq_of_cross_product
          (RFAP.ExplicitField.mul_ne_zero
            (oneHundredFour_nonzero admissible)
            (secondQuadrance_nonzero i iSquare admissible))
          (oneThousandForty_nonzero admissible)
        have scaledQuadrance :
            (104 : K) * complexValue i (-4) 2 =
              complexValue i (-416) 208 := by
          unfold complexValue
          ring1
        rw [scaledQuadrance,
          complexValue_mul i (-199) (-32) (-416) 208 iSquare]
        unfold complexValue
        ring1
  · rw [spreads.2.2]
    calc
      (complexValue i (-199) (-32) / 130) / 8 =
          complexValue i (-199) (-32) / (130 * 8) :=
        fraction_div _ _ _ (oneHundredThirty_nonzero admissible)
          (eight_nonzero admissible)
      _ = complexValue i (-199) (-32) / 1040 := by
        congr 1
        ring1

/-- The common Spread-law value in the two reduced components printed by the
book. -/
theorem spread_law_value
    (i : K) (admissible : AdmissibleCharacteristic K) :
    complexValue i (-199) (-32) / 1040 =
      complexValue i (-(199 / 1040)) (-(2 / 65)) := by
  have imaginaryReduction : ((-32 : K) / 1040) = -(2 / 65) := by
    calc
      ((-32 : K) / 1040) = (-2) / 65 := by
        apply ratio_eq_of_cross_product (oneThousandForty_nonzero admissible)
          (sixtyFive_nonzero admissible)
        ring1
      _ = -(2 / 65) := by
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        ring1
  calc
    complexValue i (-199) (-32) / 1040 =
        complexValue i ((-199) / 1040) ((-32) / 1040) :=
      complexValue_div i (-199) (-32) 1040
        (oneThousandForty_nonzero admissible)
    _ = complexValue i (-(199 / 1040)) (-(2 / 65)) := by
      rw [imaginaryReduction]
      unfold complexValue
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      ring1

/-- The sum of the three spreads, before squaring, is `(167+231i)/520`. -/
private theorem spread_sum_value [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    spread second third (line₂_nonNull i iSquare admissible)
          (line₃_nonNull i iSquare admissible) +
        spread first third (line₁_nonNull i iSquare admissible)
          (line₃_nonNull i iSquare admissible) +
        spread first second (line₁_nonNull i iSquare admissible)
          (line₂_nonNull i iSquare admissible) =
      complexValue i 167 231 / 520 := by
  dsimp only
  rw [(spread_common_denominator_values i iSquare admissible).1,
    (spread_common_denominator_values i iSquare admissible).2.1,
    (spread_common_denominator_values i iSquare admissible).2.2]
  apply three_fraction_sum_eq
    (complexValue i 41 38) (complexValue i 86 (-27))
    (complexValue i (-199) (-32)) (complexValue i 167 231)
    40 104 130 520 (forty_nonzero admissible)
    (oneHundredFour_nonzero admissible) (oneHundredThirty_nonzero admissible)
    (fiveHundredTwenty_nonzero admissible)
  unfold complexValue
  ring1

/-- The square common to both sides of the Triple spread formula, using one
component denominator. -/
private theorem triple_spread_common_value [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    (spread second third (line₂_nonNull i iSquare admissible)
          (line₃_nonNull i iSquare admissible) +
        spread first third (line₁_nonNull i iSquare admissible)
          (line₃_nonNull i iSquare admissible) +
        spread first second (line₁_nonNull i iSquare admissible)
          (line₂_nonNull i iSquare admissible)) ^ 2 =
      complexValue i (-12736) 38577 / 135200 := by
  dsimp only
  rw [spread_sum_value i iSquare admissible]
  apply square_fraction_eq
    (complexValue i 167 231) 520 (complexValue i (-12736) 38577) 135200
    (fiveHundredTwenty_nonzero admissible)
    (oneHundredThirtyFiveThousandTwoHundred_nonzero admissible)
  rw [complexValue_square i 167 231 iSquare]
  unfold complexValue
  ring1

/-- Both sides of the Triple spread formula have the exact value printed in
Example 7.4. -/
theorem triple_spread_value [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    let s₁ := spread second third (line₂_nonNull i iSquare admissible)
      (line₃_nonNull i iSquare admissible)
    let s₂ := spread first third (line₁_nonNull i iSquare admissible)
      (line₃_nonNull i iSquare admissible)
    let s₃ := spread first second (line₁_nonNull i iSquare admissible)
      (line₂_nonNull i iSquare admissible)
    (s₁ + s₂ + s₃) ^ 2 =
        complexValue i (-(398 / 4225)) (38577 / 135200) ∧
      2 * (s₁ ^ 2 + s₂ ^ 2 + s₃ ^ 2) + 4 * s₁ * s₂ * s₃ =
        complexValue i (-(398 / 4225)) (38577 / 135200) := by
  dsimp only
  have common := triple_spread_common_value i iSquare admissible
  have realReduction : ((-12736 : K) / 135200) = -(398 / 4225) := by
    calc
      ((-12736 : K) / 135200) = (-398) / 4225 := by
        apply ratio_eq_of_cross_product
          (oneHundredThirtyFiveThousandTwoHundred_nonzero admissible)
          (fourThousandTwoHundredTwentyFive_nonzero admissible)
        ring1
      _ = -(398 / 4225) := by
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        ring1
  have printedValue :
      complexValue i (-12736) 38577 / 135200 =
        complexValue i (-(398 / 4225)) (38577 / 135200) := by
    calc
      complexValue i (-12736) 38577 / 135200 =
          complexValue i ((-12736) / 135200) (38577 / 135200) :=
        complexValue_div i (-12736) 38577 135200
          (oneHundredThirtyFiveThousandTwoHundred_nonzero admissible)
      _ = complexValue i (-(398 / 4225)) (38577 / 135200) := by
        rw [realReduction]
  constructor
  · exact common.trans printedValue
  · calc
      2 *
            (spread (line₂ i admissible.twoNonzero (i_nonzero i iSquare))
                  (line₃ i (i_nonzero i iSquare))
                  (line₂_nonNull i iSquare admissible)
                  (line₃_nonNull i iSquare admissible) ^ 2 +
              spread (line₁ i admissible.threeNonzero (i_nonzero i iSquare))
                  (line₃ i (i_nonzero i iSquare))
                  (line₁_nonNull i iSquare admissible)
                  (line₃_nonNull i iSquare admissible) ^ 2 +
              spread (line₁ i admissible.threeNonzero (i_nonzero i iSquare))
                  (line₂ i admissible.twoNonzero (i_nonzero i iSquare))
                  (line₁_nonNull i iSquare admissible)
                  (line₂_nonNull i iSquare admissible) ^ 2) +
          4 *
            spread (line₂ i admissible.twoNonzero (i_nonzero i iSquare))
              (line₃ i (i_nonzero i iSquare))
              (line₂_nonNull i iSquare admissible)
              (line₃_nonNull i iSquare admissible) *
            spread (line₁ i admissible.threeNonzero (i_nonzero i iSquare))
              (line₃ i (i_nonzero i iSquare))
              (line₁_nonNull i iSquare admissible)
              (line₃_nonNull i iSquare admissible) *
            spread (line₁ i admissible.threeNonzero (i_nonzero i iSquare))
              (line₂ i admissible.twoNonzero (i_nonzero i iSquare))
              (line₁_nonNull i iSquare admissible)
              (line₂_nonNull i iSquare admissible) =
          (spread (line₂ i admissible.twoNonzero (i_nonzero i iSquare))
                (line₃ i (i_nonzero i iSquare))
                (line₂_nonNull i iSquare admissible)
                (line₃_nonNull i iSquare admissible) +
            spread (line₁ i admissible.threeNonzero (i_nonzero i iSquare))
                (line₃ i (i_nonzero i iSquare))
                (line₁_nonNull i iSquare admissible)
                (line₃_nonNull i iSquare admissible) +
            spread (line₁ i admissible.threeNonzero (i_nonzero i iSquare))
                (line₂ i admissible.twoNonzero (i_nonzero i iSquare))
                (line₁_nonNull i iSquare admissible)
                (line₂_nonNull i iSquare admissible)) ^ 2 :=
        (triple_spread_formula
          (line₁ i admissible.threeNonzero (i_nonzero i iSquare))
          (line₂ i admissible.twoNonzero (i_nonzero i iSquare))
          (line₃ i (i_nonzero i iSquare))
          (line₁_nonNull i iSquare admissible)
          (line₂_nonNull i iSquare admissible)
          (line₃_nonNull i iSquare admissible)).symm
      _ = complexValue i (-(398 / 4225)) (38577 / 135200) :=
        common.trans printedValue

private theorem firstDot_nonzero
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    complexValue i 5 3 ≠ 0 := by
  intro valueZero
  apply thirtyFour_nonzero admissible
  calc
    (34 : K) = complexValue i 5 3 * complexValue i 5 (-3) := by
      rw [complexValue_mul i 5 3 5 (-3) iSquare]
      unfold complexValue
      ring1
    _ = 0 := by rw [valueZero]; ring1

private theorem secondDot_nonzero
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    complexValue i (-3) 3 ≠ 0 := by
  intro valueZero
  apply eighteen_nonzero admissible
  calc
    (18 : K) = complexValue i (-3) 3 * complexValue i (-3) (-3) := by
      rw [complexValue_mul i (-3) 3 (-3) (-3) iSquare]
      unfold complexValue
      ring1
    _ = 0 := by rw [valueZero]; ring1

private theorem thirdDot_nonzero
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    complexValue i (-9) (-1) ≠ 0 := by
  intro valueZero
  apply eightyTwo_nonzero admissible
  calc
    (82 : K) = complexValue i (-9) (-1) * complexValue i (-9) 1 := by
      rw [complexValue_mul i (-9) (-1) (-9) 1 iSquare]
      unfold complexValue
      ring1
    _ = 0 := by rw [valueZero]; ring1

theorem line₂_line₃_notPerpendicular [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    ¬ (line₂ i admissible.twoNonzero (i_nonzero i iSquare)).Perpendicular
      (line₃ i (i_nonzero i iSquare)) := by
  intro perpendicular
  apply firstDot_nonzero i iSquare admissible
  calc
    complexValue i 5 3 =
        (line₂ i admissible.twoNonzero (i_nonzero i iSquare)).a *
            (line₃ i (i_nonzero i iSquare)).a +
          (line₂ i admissible.twoNonzero (i_nonzero i iSquare)).b *
            (line₃ i (i_nonzero i iSquare)).b :=
      (dot_values i iSquare admissible).1.symm
    _ = 0 := perpendicular

theorem line₁_line₃_notPerpendicular [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    ¬ (line₁ i admissible.threeNonzero (i_nonzero i iSquare)).Perpendicular
      (line₃ i (i_nonzero i iSquare)) := by
  intro perpendicular
  apply secondDot_nonzero i iSquare admissible
  calc
    complexValue i (-3) 3 =
        (line₁ i admissible.threeNonzero (i_nonzero i iSquare)).a *
            (line₃ i (i_nonzero i iSquare)).a +
          (line₁ i admissible.threeNonzero (i_nonzero i iSquare)).b *
            (line₃ i (i_nonzero i iSquare)).b :=
      (dot_values i iSquare admissible).2.1.symm
    _ = 0 := perpendicular

theorem line₁_line₂_notPerpendicular [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    ¬ (line₁ i admissible.threeNonzero (i_nonzero i iSquare)).Perpendicular
      (line₂ i admissible.twoNonzero (i_nonzero i iSquare)) := by
  intro perpendicular
  apply thirdDot_nonzero i iSquare admissible
  calc
    complexValue i (-9) (-1) =
        (line₁ i admissible.threeNonzero (i_nonzero i iSquare)).a *
            (line₂ i admissible.twoNonzero (i_nonzero i iSquare)).a +
          (line₁ i admissible.threeNonzero (i_nonzero i iSquare)).b *
            (line₂ i admissible.twoNonzero (i_nonzero i iSquare)).b :=
      (dot_values i iSquare admissible).2.2.symm
    _ = 0 := perpendicular

/-- The three twists in the single-denominator component forms used to check
the final formula. -/
theorem twist_values [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    twist second third (line₂_line₃_notPerpendicular i iSquare admissible) =
        complexValue i (-297) 304 / 289 ∧
      twist first third (line₁_line₃_notPerpendicular i iSquare admissible) =
        complexValue i 7 (-24) / 9 ∧
      twist first second (line₁_line₂_notPerpendicular i iSquare admissible) =
        complexValue i (-1023) (-64) / 1681 := by
  dsimp only
  have determinants := determinant_square_value i iSquare admissible
  have dots := dot_values i iSquare admissible
  have firstDotSquare :
      complexValue i 5 3 ^ 2 = complexValue i 16 30 := by
    rw [complexValue_square i 5 3 iSquare]
    unfold complexValue
    ring1
  have secondDotSquare :
      complexValue i (-3) 3 ^ 2 = complexValue i 0 (-18) := by
    rw [complexValue_square i (-3) 3 iSquare]
    unfold complexValue
    ring1
  have thirdDotSquare :
      complexValue i (-9) (-1) ^ 2 = complexValue i 80 18 := by
    rw [complexValue_square i (-9) (-1) iSquare]
    unfold complexValue
    ring1
  constructor
  · unfold twist
    rw [determinants.1, dots.1, firstDotSquare]
    apply ratio_eq_of_cross_product
      (by
        rw [← firstDotSquare]
        simpa only [pow_two] using
          RFAP.ExplicitField.mul_ne_zero
            (firstDot_nonzero i iSquare admissible)
            (firstDot_nonzero i iSquare admissible))
      (twoHundredEightyNine_nonzero admissible)
    rw [complexValue_mul i (-297) 304 16 30 iSquare]
    unfold complexValue
    ring1
  constructor
  · unfold twist
    rw [determinants.2.1, dots.2.1, secondDotSquare]
    apply ratio_eq_of_cross_product
      (by
        rw [← secondDotSquare]
        simpa only [pow_two] using
          RFAP.ExplicitField.mul_ne_zero
            (secondDot_nonzero i iSquare admissible)
            (secondDot_nonzero i iSquare admissible))
      (nine_nonzero admissible)
    rw [complexValue_mul i 7 (-24) 0 (-18) iSquare]
    unfold complexValue
    ring1
  · unfold twist
    rw [determinants.2.2, dots.2.2, thirdDotSquare]
    apply ratio_eq_of_cross_product
      (by
        rw [← thirdDotSquare]
        simpa only [pow_two] using
          RFAP.ExplicitField.mul_ne_zero
            (thirdDot_nonzero i iSquare admissible)
            (thirdDot_nonzero i iSquare admissible))
      (oneThousandSixHundredEightyOne_nonzero admissible)
    rw [complexValue_mul i (-1023) (-64) 80 18 iSquare]
    unfold complexValue
    ring1

/-- Before squaring, the Triple-twist expression is `(474+1232i)/2091`. -/
private theorem twist_expression_value [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    let t₁ := twist second third
      (line₂_line₃_notPerpendicular i iSquare admissible)
    let t₂ := twist first third
      (line₁_line₃_notPerpendicular i iSquare admissible)
    let t₃ := twist first second
      (line₁_line₂_notPerpendicular i iSquare admissible)
    t₁ + t₂ + t₃ - t₁ * t₂ * t₃ =
      complexValue i 474 1232 / 2091 := by
  dsimp only
  rw [(twist_values i iSquare admissible).1,
    (twist_values i iSquare admissible).2.1,
    (twist_values i iSquare admissible).2.2]
  apply three_fraction_sum_sub_product_eq
    (complexValue i (-297) 304) (complexValue i 7 (-24))
    (complexValue i (-1023) (-64)) (complexValue i 474 1232)
    289 9 1681 2091 (twoHundredEightyNine_nonzero admissible)
    (nine_nonzero admissible) (oneThousandSixHundredEightyOne_nonzero admissible)
    (twoThousandNinetyOne_nonzero admissible)
  have firstProduct :
      complexValue i (-297) 304 * complexValue i 7 (-24) =
        complexValue i 5217 9256 := by
    rw [complexValue_mul i (-297) 304 7 (-24) iSquare]
    unfold complexValue
    ring1
  have productValue :
      complexValue i (-297) 304 * complexValue i 7 (-24) *
          complexValue i (-1023) (-64) =
        complexValue i (-4744607) (-9802776) := by
    rw [firstProduct,
      complexValue_mul i 5217 9256 (-1023) (-64) iSquare]
    unfold complexValue
    ring1
  rw [productValue]
  unfold complexValue
  ring1

private theorem triple_twist_common_value [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    let t₁ := twist second third
      (line₂_line₃_notPerpendicular i iSquare admissible)
    let t₂ := twist first third
      (line₁_line₃_notPerpendicular i iSquare admissible)
    let t₃ := twist first second
      (line₁_line₂_notPerpendicular i iSquare admissible)
    (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 =
      complexValue i (-1293148) 1167936 / 4372281 := by
  dsimp only
  rw [twist_expression_value i iSquare admissible]
  apply square_fraction_eq
    (complexValue i 474 1232) 2091
    (complexValue i (-1293148) 1167936) 4372281
    (twoThousandNinetyOne_nonzero admissible)
    (fourMillionThreeHundredSeventyTwoThousandTwoHundredEightyOne_nonzero
      admissible)
  rw [complexValue_square i 474 1232 iSquare]
  unfold complexValue
  ring1

/-- Both sides of the Triple twist formula have the exact value printed in
Example 7.4. -/
theorem triple_twist_value [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    let t₁ := twist second third
      (line₂_line₃_notPerpendicular i iSquare admissible)
    let t₂ := twist first third
      (line₁_line₃_notPerpendicular i iSquare admissible)
    let t₃ := twist first second
      (line₁_line₂_notPerpendicular i iSquare admissible)
    (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 =
        complexValue i (-(1293148 / 4372281)) (389312 / 1457427) ∧
      4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ +
          2 * t₁ * t₂ * t₃) =
        complexValue i (-(1293148 / 4372281)) (389312 / 1457427) := by
  dsimp only
  have common := triple_twist_common_value i iSquare admissible
  have imaginaryReduction :
      (1167936 : K) / 4372281 = 389312 / 1457427 := by
    apply ratio_eq_of_cross_product
      (fourMillionThreeHundredSeventyTwoThousandTwoHundredEightyOne_nonzero
        admissible)
      (oneMillionFourHundredFiftySevenThousandFourHundredTwentySeven_nonzero
        admissible)
    ring1
  have printedValue :
      complexValue i (-1293148) 1167936 / 4372281 =
        complexValue i (-(1293148 / 4372281)) (389312 / 1457427) := by
    calc
      complexValue i (-1293148) 1167936 / 4372281 =
          complexValue i ((-1293148) / 4372281) (1167936 / 4372281) :=
        complexValue_div i (-1293148) 1167936 4372281
          (fourMillionThreeHundredSeventyTwoThousandTwoHundredEightyOne_nonzero
            admissible)
      _ = complexValue i (-(1293148 / 4372281)) (389312 / 1457427) := by
        rw [imaginaryReduction]
        unfold complexValue
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        ring1
  have formula := triple_twist_formula
    (line₁ i admissible.threeNonzero (i_nonzero i iSquare))
    (line₂ i admissible.twoNonzero (i_nonzero i iSquare))
    (line₃ i (i_nonzero i iSquare))
    (line₁_line₂_notPerpendicular i iSquare admissible)
    (line₁_line₃_notPerpendicular i iSquare admissible)
    (line₂_line₃_notPerpendicular i iSquare admissible)
  exact ⟨common.trans printedValue,
    formula.symm.trans (common.trans printedValue)⟩

end ExampleSevenFour

end ChapterSevenFieldFragments

end DivineProportions
