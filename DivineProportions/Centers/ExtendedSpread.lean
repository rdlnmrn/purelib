import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Centers.Circumcenter

/-!
# Divine Proportions, §12.1: the Extended spread law

The book proves the result by introducing the three side midpoints and then
solving an auxiliary triangle.  Here the same finite content is exposed by a
stronger polynomial lemma: a triangle with a displayed common-quadrance center
satisfies `quadrea * circumquadrance = Q₁ * Q₂ * Q₃`.  Combining that identity
with Quadrea spread gives the final reciprocal, while the ordinary Spread law
gives the other two equalities.

No generic-position choice among the midpoints is needed, and all divisions
are guarded by explicit nonzero certificates.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The finite polynomial identity behind the Extended spread law.  It only
asks for a displayed point having the same quadrance `circumquadranceValue`
from all three vertices. -/
theorem circumquadrea_identity
    (first second third center : Point K) (circumquadranceValue : K)
    (firstRadius : quadrance center first = circumquadranceValue)
    (secondRadius : quadrance center second = circumquadranceValue)
    (thirdRadius : quadrance center third = circumquadranceValue) :
    quadrea first second third * circumquadranceValue =
      quadrance second third * quadrance first third *
        quadrance first second := by
  let ax := first.x - center.x
  let ay := first.y - center.y
  let bx := second.x - center.x
  let bY := second.y - center.y
  let cx := third.x - center.x
  let cy := third.y - center.y
  let firstSecondDot := ax * bx + ay * bY
  let firstThirdDot := ax * cx + ay * cy
  let secondThirdDot := bx * cx + bY * cy
  have firstNorm : ax ^ 2 + ay ^ 2 = circumquadranceValue := by
    simpa only [quadrance, ax, ay] using firstRadius
  have secondNorm : bx ^ 2 + bY ^ 2 = circumquadranceValue := by
    simpa only [quadrance, bx, bY] using secondRadius
  have thirdNorm : cx ^ 2 + cy ^ 2 = circumquadranceValue := by
    simpa only [quadrance, cx, cy] using thirdRadius
  have gramIdentity :
      circumquadranceValue ^ 3 +
          2 * firstSecondDot * firstThirdDot * secondThirdDot -
          circumquadranceValue *
            (firstSecondDot ^ 2 + firstThirdDot ^ 2 +
              secondThirdDot ^ 2) = 0 := by
    calc
      circumquadranceValue ^ 3 +
            2 * firstSecondDot * firstThirdDot * secondThirdDot -
            circumquadranceValue *
              (firstSecondDot ^ 2 + firstThirdDot ^ 2 +
                secondThirdDot ^ 2) =
          (ax ^ 2 + ay ^ 2) * (bx ^ 2 + bY ^ 2) *
              (cx ^ 2 + cy ^ 2) +
            2 * firstSecondDot * firstThirdDot * secondThirdDot -
            (ax ^ 2 + ay ^ 2) * secondThirdDot ^ 2 -
            (bx ^ 2 + bY ^ 2) * firstThirdDot ^ 2 -
            (cx ^ 2 + cy ^ 2) * firstSecondDot ^ 2 := by
              rw [firstNorm, secondNorm, thirdNorm]
              ring1
      _ = 0 := by
        unfold firstSecondDot firstThirdDot secondThirdDot
        ring1
  have firstQuadrance :
      quadrance second third =
        2 * (circumquadranceValue - secondThirdDot) := by
    calc
      quadrance second third =
          (bx ^ 2 + bY ^ 2) + (cx ^ 2 + cy ^ 2) -
            2 * secondThirdDot := by
              unfold quadrance bx bY cx cy secondThirdDot
              ring1
      _ = 2 * (circumquadranceValue - secondThirdDot) := by
        rw [secondNorm, thirdNorm]
        ring1
  have secondQuadrance :
      quadrance first third =
        2 * (circumquadranceValue - firstThirdDot) := by
    calc
      quadrance first third =
          (ax ^ 2 + ay ^ 2) + (cx ^ 2 + cy ^ 2) -
            2 * firstThirdDot := by
              unfold quadrance ax ay cx cy firstThirdDot
              ring1
      _ = 2 * (circumquadranceValue - firstThirdDot) := by
        rw [firstNorm, thirdNorm]
        ring1
  have thirdQuadrance :
      quadrance first second =
        2 * (circumquadranceValue - firstSecondDot) := by
    calc
      quadrance first second =
          (ax ^ 2 + ay ^ 2) + (bx ^ 2 + bY ^ 2) -
            2 * firstSecondDot := by
              unfold quadrance ax ay bx bY firstSecondDot
              ring1
      _ = 2 * (circumquadranceValue - firstSecondDot) := by
        rw [firstNorm, secondNorm]
        ring1
  unfold quadrea
  rw [firstQuadrance, secondQuadrance, thirdQuadrance]
  calc
    archimedesFunction
          (2 * (circumquadranceValue - secondThirdDot))
          (2 * (circumquadranceValue - firstThirdDot))
          (2 * (circumquadranceValue - firstSecondDot)) *
        circumquadranceValue =
      2 * (circumquadranceValue - secondThirdDot) *
          (2 * (circumquadranceValue - firstThirdDot)) *
          (2 * (circumquadranceValue - firstSecondDot)) +
        4 *
          (circumquadranceValue ^ 3 +
            2 * firstSecondDot * firstThirdDot * secondThirdDot -
            circumquadranceValue *
              (firstSecondDot ^ 2 + firstThirdDot ^ 2 +
                secondThirdDot ^ 2)) := by
          unfold archimedesFunction
          ring1
    _ = 2 * (circumquadranceValue - secondThirdDot) *
          (2 * (circumquadranceValue - firstThirdDot)) *
          (2 * (circumquadranceValue - firstSecondDot)) := by
      rw [gramIdentity]
      ring1

private theorem cancel_left_nonzero
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

private theorem explicit_div_one [Nontrivial K] (value : K) :
    value / 1 = value := by
  have oneInverse : (1 : K)⁻¹ = 1 := by
    simpa only [one_mul] using
      RFAP.ExplicitField.mul_inv_cancel (1 : K)
        (one_ne_zero : (1 : K) ≠ 0)
  rw [RFAP.ExplicitField.div_eq_mul_inv, oneInverse, mul_one]

private theorem side_quadrance_nonzero [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (nonNull : ¬ (lineThrough first second distinct).IsNull) :
    quadrance first second ≠ 0 := by
  intro quadranceZero
  exact nonNull
    ((null_line_iff_quadrance_zero first second distinct).2 quadranceZero)

private theorem spread_reverse_both [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (firstSecondNonNull :
      ¬ (lineThrough first second firstSecondDistinct).IsNull)
    (firstThirdNonNull :
      ¬ (lineThrough first third firstThirdDistinct).IsNull) :
    spread (lineThrough first second firstSecondDistinct)
        (lineThrough first third firstThirdDistinct)
        firstSecondNonNull firstThirdNonNull =
      spread (lineThrough second first firstSecondDistinct.symm)
        (lineThrough third first firstThirdDistinct.symm)
        (by
          rwa [null_line_iff_quadrance_zero,
            quadrance_symm second first,
            ← null_line_iff_quadrance_zero first second firstSecondDistinct])
        (by
          rwa [null_line_iff_quadrance_zero,
            quadrance_symm third first,
            ← null_line_iff_quadrance_zero first third firstThirdDistinct]) := by
  unfold spread lineNorm lineThrough
  congr 1 <;> ring1

/-- Theorem 82 (Extended spread law).  The three spreads are taken at
`first`, `second`, and `third`; their corresponding quadrances are the
opposite sides.  `center` is a displayed circumcenter and its quadrance to
`first` is the book's `K`. -/
theorem extended_spread_law
    [Nontrivial K] [DecidableEq K]
    (first second third center : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (firstSecondNonNull :
      ¬ (lineThrough first second firstSecondDistinct).IsNull)
    (firstThirdNonNull :
      ¬ (lineThrough first third firstThirdDistinct).IsNull)
    (secondThirdNonNull :
      ¬ (lineThrough second third secondThirdDistinct).IsNull)
    (twoNonzero : (2 : K) ≠ 0)
    (equalFirstSecond :
      quadrance center first = quadrance center second)
    (equalSecondThird :
      quadrance center second = quadrance center third) :
    let firstSecondReversedNonNull :
        ¬ (lineThrough second first firstSecondDistinct.symm).IsNull := by
      rwa [null_line_iff_quadrance_zero,
        quadrance_symm second first,
        ← null_line_iff_quadrance_zero first second firstSecondDistinct]
    let firstThirdReversedNonNull :
        ¬ (lineThrough third first firstThirdDistinct.symm).IsNull := by
      rwa [null_line_iff_quadrance_zero,
        quadrance_symm third first,
        ← null_line_iff_quadrance_zero first third firstThirdDistinct]
    let secondThirdReversedNonNull :
        ¬ (lineThrough third second secondThirdDistinct.symm).IsNull := by
      rwa [null_line_iff_quadrance_zero,
        quadrance_symm third second,
        ← null_line_iff_quadrance_zero second third secondThirdDistinct]
    let s₁ := spread (lineThrough first second firstSecondDistinct)
      (lineThrough first third firstThirdDistinct)
      firstSecondNonNull firstThirdNonNull
    let s₂ := spread (lineThrough second first firstSecondDistinct.symm)
      (lineThrough second third secondThirdDistinct)
      firstSecondReversedNonNull secondThirdNonNull
    let s₃ := spread (lineThrough third first firstThirdDistinct.symm)
      (lineThrough third second secondThirdDistinct.symm)
      firstThirdReversedNonNull secondThirdReversedNonNull
    let q₁ := quadrance second third
    let q₂ := quadrance first third
    let q₃ := quadrance first second
    let circumquadranceValue := quadrance center first
    s₁ / q₁ = s₂ / q₂ ∧
      s₂ / q₂ = s₃ / q₃ ∧
      s₃ / q₃ = 1 / (4 * circumquadranceValue) := by
  dsimp only
  let firstSecondReversedNonNull :
      ¬ (lineThrough second first firstSecondDistinct.symm).IsNull := by
    rwa [null_line_iff_quadrance_zero,
      quadrance_symm second first,
      ← null_line_iff_quadrance_zero first second firstSecondDistinct]
  let firstThirdReversedNonNull :
      ¬ (lineThrough third first firstThirdDistinct.symm).IsNull := by
    rwa [null_line_iff_quadrance_zero,
      quadrance_symm third first,
      ← null_line_iff_quadrance_zero first third firstThirdDistinct]
  let secondThirdReversedNonNull :
      ¬ (lineThrough third second secondThirdDistinct.symm).IsNull := by
    rwa [null_line_iff_quadrance_zero,
      quadrance_symm third second,
      ← null_line_iff_quadrance_zero second third secondThirdDistinct]
  let s₁ := spread (lineThrough first second firstSecondDistinct)
    (lineThrough first third firstThirdDistinct)
    firstSecondNonNull firstThirdNonNull
  let s₂ := spread (lineThrough second first firstSecondDistinct.symm)
    (lineThrough second third secondThirdDistinct)
    firstSecondReversedNonNull secondThirdNonNull
  let s₃ := spread (lineThrough third first firstThirdDistinct.symm)
    (lineThrough third second secondThirdDistinct.symm)
    firstThirdReversedNonNull secondThirdReversedNonNull
  let q₁ := quadrance second third
  let q₂ := quadrance first third
  let q₃ := quadrance first second
  let circumquadranceValue := quadrance center first
  have q₁Nonzero : q₁ ≠ 0 :=
    side_quadrance_nonzero second third secondThirdDistinct
      secondThirdNonNull
  have q₂Nonzero : q₂ ≠ 0 :=
    side_quadrance_nonzero first third firstThirdDistinct
      firstThirdNonNull
  have q₃Nonzero : q₃ ≠ 0 :=
    side_quadrance_nonzero first second firstSecondDistinct
      firstSecondNonNull
  have productNonzero : q₁ * q₂ * q₃ ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero q₁Nonzero q₂Nonzero) q₃Nonzero
  have circumIdentity :
      quadrea first second third * circumquadranceValue = q₁ * q₂ * q₃ := by
    apply circumquadrea_identity first second third center
      circumquadranceValue
    · exact rfl
    · exact equalFirstSecond.symm
    · exact (equalFirstSecond.trans equalSecondThird).symm
  have circumquadranceNonzero : circumquadranceValue ≠ 0 := by
    intro circumquadranceZero
    apply productNonzero
    calc
      q₁ * q₂ * q₃ =
          quadrea first second third * circumquadranceValue :=
            circumIdentity.symm
      _ = 0 := by rw [circumquadranceZero]; ring1
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [fourAsProduct]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have fourCircumquadranceNonzero :
      4 * circumquadranceValue ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero fourNonzero circumquadranceNonzero
  have spreadRatios := spread_law first second third
    firstSecondDistinct firstThirdDistinct secondThirdDistinct
    firstSecondNonNull firstThirdNonNull secondThirdNonNull twoNonzero
  change s₁ / q₁ = s₂ / q₂ ∧ s₂ / q₂ = s₃ / q₃ at spreadRatios
  have reverseSpreadAtThird := spread_reverse_both
    third first second firstThirdDistinct.symm secondThirdDistinct.symm
    firstThirdReversedNonNull secondThirdReversedNonNull
  have areaAtThird := quadrea_spread first second third
    firstThirdDistinct secondThirdDistinct
    firstThirdNonNull secondThirdNonNull
  rw [← reverseSpreadAtThird] at areaAtThird
  change quadrea first second third = 4 * q₁ * q₂ * s₃ at areaAtThird
  have reciprocalCross : s₃ * (4 * circumquadranceValue) = 1 * q₃ := by
    have factorNonzero : q₁ * q₂ ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero q₁Nonzero q₂Nonzero
    apply cancel_left_nonzero factorNonzero
    calc
      (q₁ * q₂) * (s₃ * (4 * circumquadranceValue)) =
          (4 * q₁ * q₂ * s₃) * circumquadranceValue := by ring1
      _ = quadrea first second third * circumquadranceValue := by
        rw [← areaAtThird]
      _ = q₁ * q₂ * q₃ := circumIdentity
      _ = (q₁ * q₂) * (1 * q₃) := by ring1
  change s₁ / q₁ = s₂ / q₂ ∧
    s₂ / q₂ = s₃ / q₃ ∧ s₃ / q₃ = 1 / (4 * circumquadranceValue)
  refine ⟨spreadRatios.1, spreadRatios.2, ?_⟩
  exact ratio_eq_of_cross_product q₃Nonzero
    fourCircumquadranceNonzero reciprocalCross

/-- The quotient chain of Theorem 82 can always be cleared back to the three
finite identities `sᵢ(4K) = Qᵢ`.  This is the form used by the following
reader exercises. -/
theorem extended_spread_law_cross_products
    [Nontrivial K] [DecidableEq K]
    (q₁ q₂ q₃ s₁ s₂ s₃ circumquadranceValue : K)
    (q₁Nonzero : q₁ ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (q₃Nonzero : q₃ ≠ 0)
    (fourCircumquadranceNonzero : 4 * circumquadranceValue ≠ 0)
    (extendedRatios :
      s₁ / q₁ = s₂ / q₂ ∧
        s₂ / q₂ = s₃ / q₃ ∧
        s₃ / q₃ = 1 / (4 * circumquadranceValue)) :
    s₁ * (4 * circumquadranceValue) = q₁ ∧
      s₂ * (4 * circumquadranceValue) = q₂ ∧
      s₃ * (4 * circumquadranceValue) = q₃ := by
  have firstRatio : s₁ / q₁ = 1 / (4 * circumquadranceValue) :=
    extendedRatios.1.trans
      (extendedRatios.2.1.trans extendedRatios.2.2)
  have secondRatio : s₂ / q₂ = 1 / (4 * circumquadranceValue) :=
    extendedRatios.2.1.trans extendedRatios.2.2
  have firstCross := cross_product_of_ratio_eq q₁Nonzero
    fourCircumquadranceNonzero firstRatio
  have secondCross := cross_product_of_ratio_eq q₂Nonzero
    fourCircumquadranceNonzero secondRatio
  have thirdCross := cross_product_of_ratio_eq q₃Nonzero
    fourCircumquadranceNonzero extendedRatios.2.2
  simpa only [one_mul] using And.intro firstCross
    (And.intro secondCross thirdCross)

/-- Exercise 12.2 before division: both expressions become equal after
multiplication by the displayed circumquadrance. -/
theorem exercise_12_2_cleared
    (q₁ q₂ q₃ s₁ s₂ s₃ area circumquadranceValue : K)
    (circumquadrea :
      area * circumquadranceValue = q₁ * q₂ * q₃)
    (firstExtended : s₁ * (4 * circumquadranceValue) = q₁)
    (secondExtended : s₂ * (4 * circumquadranceValue) = q₂)
    (thirdExtended : s₃ * (4 * circumquadranceValue) = q₃) :
    area * circumquadranceValue = q₁ * q₂ * q₃ ∧
      area * circumquadranceValue =
        64 * circumquadranceValue ^ 3 * s₁ * s₂ * s₃ := by
  constructor
  · exact circumquadrea
  · calc
      area * circumquadranceValue = q₁ * q₂ * q₃ := circumquadrea
      _ = (s₁ * (4 * circumquadranceValue)) *
          (s₂ * (4 * circumquadranceValue)) *
          (s₃ * (4 * circumquadranceValue)) := by
            rw [firstExtended, secondExtended, thirdExtended]
      _ = 64 * circumquadranceValue ^ 3 * s₁ * s₂ * s₃ := by ring1

/-- Exercise 12.2 in the book's exact quotient form:
`A = Q₁Q₂Q₃/K = 64K²s₁s₂s₃`. -/
theorem exercise_12_2
    [Nontrivial K] [DecidableEq K]
    (q₁ q₂ q₃ s₁ s₂ s₃ area circumquadranceValue : K)
    (circumquadranceNonzero : circumquadranceValue ≠ 0)
    (circumquadrea :
      area * circumquadranceValue = q₁ * q₂ * q₃)
    (firstExtended : s₁ * (4 * circumquadranceValue) = q₁)
    (secondExtended : s₂ * (4 * circumquadranceValue) = q₂)
    (thirdExtended : s₃ * (4 * circumquadranceValue) = q₃) :
    area = (q₁ * q₂ * q₃) / circumquadranceValue ∧
      area = 64 * circumquadranceValue ^ 2 * s₁ * s₂ * s₃ := by
  have cleared := exercise_12_2_cleared q₁ q₂ q₃ s₁ s₂ s₃ area
    circumquadranceValue circumquadrea firstExtended secondExtended
    thirdExtended
  constructor
  · have ratio := ratio_eq_of_cross_product
      (one_ne_zero : (1 : K) ≠ 0) circumquadranceNonzero
      (by simpa only [mul_one] using circumquadrea)
    simpa only [explicit_div_one] using ratio
  · apply cancel_left_nonzero circumquadranceNonzero
    calc
      circumquadranceValue * area =
          area * circumquadranceValue := by ring1
      _ = 64 * circumquadranceValue ^ 3 * s₁ * s₂ * s₃ := cleared.2
      _ = circumquadranceValue *
          (64 * circumquadranceValue ^ 2 * s₁ * s₂ * s₃) := by ring1

/-- Exercise 12.3 without division. -/
theorem exercise_12_3_cleared
    (q₁ q₂ q₃ s₁ s₂ s₃ circumquadranceValue : K)
    (firstExtended : s₁ * (4 * circumquadranceValue) = q₁)
    (secondExtended : s₂ * (4 * circumquadranceValue) = q₂)
    (thirdExtended : s₃ * (4 * circumquadranceValue) = q₃) :
    (s₁ + s₂) * (4 * circumquadranceValue) = q₁ + q₂ ∧
      (s₁ + s₂ + s₃) * (4 * circumquadranceValue) =
        q₁ + q₂ + q₃ := by
  constructor
  · calc
      (s₁ + s₂) * (4 * circumquadranceValue) =
          s₁ * (4 * circumquadranceValue) +
            s₂ * (4 * circumquadranceValue) := by ring1
      _ = q₁ + q₂ := by rw [firstExtended, secondExtended]
  · calc
      (s₁ + s₂ + s₃) * (4 * circumquadranceValue) =
          s₁ * (4 * circumquadranceValue) +
            s₂ * (4 * circumquadranceValue) +
            s₃ * (4 * circumquadranceValue) := by ring1
      _ = q₁ + q₂ + q₃ := by
        rw [firstExtended, secondExtended, thirdExtended]

/-- Exercise 12.3 in the two quotient forms printed in the book. -/
theorem exercise_12_3
    [Nontrivial K] [DecidableEq K]
    (q₁ q₂ q₃ s₁ s₂ s₃ circumquadranceValue : K)
    (fourCircumquadranceNonzero : 4 * circumquadranceValue ≠ 0)
    (firstExtended : s₁ * (4 * circumquadranceValue) = q₁)
    (secondExtended : s₂ * (4 * circumquadranceValue) = q₂)
    (thirdExtended : s₃ * (4 * circumquadranceValue) = q₃) :
    s₁ + s₂ = (q₁ + q₂) / (4 * circumquadranceValue) ∧
      s₁ + s₂ + s₃ =
        (q₁ + q₂ + q₃) / (4 * circumquadranceValue) := by
  have cleared := exercise_12_3_cleared q₁ q₂ q₃ s₁ s₂ s₃
    circumquadranceValue firstExtended secondExtended thirdExtended
  constructor
  · have ratio := ratio_eq_of_cross_product
      (one_ne_zero : (1 : K) ≠ 0) fourCircumquadranceNonzero
      (by simpa only [mul_one] using cleared.1)
    simpa only [explicit_div_one] using ratio
  · have ratio := ratio_eq_of_cross_product
      (one_ne_zero : (1 : K) ≠ 0) fourCircumquadranceNonzero
      (by simpa only [mul_one] using cleared.2)
    simpa only [explicit_div_one] using ratio

end DivineProportions
