import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Trigonometry.SpreadReflection
import DivineProportions.Algebra.QuadraticCompatibility

/-!
# Divine Proportions, §7.7: quadruple spread and cross formulas

The scalar elimination is kept separate from the geometric specialization.
Two displayed spread triples give two explicit quadratic equations with a
common root; the finite quadratic-compatibility calculation then yields the
four-variable polynomial.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The inner symmetric polynomial in the quadruple spread function. -/
def quadrupleSpreadCore (a b c d : K) : K :=
  (a + b + c + d) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) -
    4 * (a * b * c + a * b * d + a * c * d + b * c * d) +
    8 * a * b * c * d

/-- The quadruple spread function `R` from the book. -/
def quadrupleSpreadFunction (a b c d : K) : K :=
  quadrupleSpreadCore a b c d ^ 2 -
    64 * a * b * c * d * (1 - a) * (1 - b) * (1 - c) * (1 - d)

private theorem sub_ne_zero_of_ne {left right : K}
    (different : left ≠ right) : left - right ≠ 0 := by
  intro differenceZero
  apply different
  calc
    left = (left - right) + right := by ring1
    _ = right := by rw [differenceZero]; ring1

/-- The symmetric compatibility clause of Theorem 53. -/
theorem two_spread_triples_compatibility
    (a b c d x : K)
    (firstTriple : SpreadTriple a b x)
    (secondTriple : SpreadTriple c d x) :
    quadrupleSpreadFunction a b c d = 0 := by
  let firstCenter := a + b - 2 * a * b
  let firstSquare := 4 * a * b * (1 - a) * (1 - b)
  let secondCenter := c + d - 2 * c * d
  let secondSquare := 4 * c * d * (1 - c) * (1 - d)
  have firstNormal := (exercise_7_6 firstTriple).2.2.2.2
  have secondNormal := (exercise_7_6 secondTriple).2.2.2.2
  change (x - firstCenter) ^ 2 = firstSquare at firstNormal
  change (x - secondCenter) ^ 2 = secondSquare at secondNormal
  have compatible : QuadraticsCompatible firstCenter firstSquare
      secondCenter secondSquare :=
    ⟨x, firstNormal, secondNormal⟩
  have identity := quadraticCompatibilityIdentity_of_compatible compatible
  unfold quadraticCompatibilityIdentity at identity
  unfold quadrupleSpreadFunction
  have coreIdentity :
      quadrupleSpreadCore a b c d ^ 2 =
        64 * a * b * c * d * (1 - a) * (1 - b) *
          (1 - c) * (1 - d) := by
    calc
      quadrupleSpreadCore a b c d ^ 2 =
          ((firstCenter - secondCenter) ^ 2 -
            (firstSquare + secondSquare)) ^ 2 := by
              unfold quadrupleSpreadCore firstCenter firstSquare
                secondCenter secondSquare
              ring1
      _ = 4 * firstSquare * secondSquare := identity
      _ = 64 * a * b * c * d * (1 - a) * (1 - b) *
          (1 - c) * (1 - d) := by
            unfold firstSquare secondSquare
            ring1
  rw [coreIdentity]
  ring1

/-- The common spread in Theorem 53, when the two quadratic centers differ. -/
theorem two_spread_triples_common_value
    (a b c d x : K)
    (twoNonzero : (2 : K) ≠ 0)
    (firstTriple : SpreadTriple a b x)
    (secondTriple : SpreadTriple c d x)
    (centersDistinct :
      a + b - 2 * a * b ≠ c + d - 2 * c * d) :
    let denominator := 2 * (a + b - c - d - 2 * a * b + 2 * c * d)
    denominator ≠ 0 ∧
      x = ((a - b) ^ 2 - (c - d) ^ 2) / denominator := by
  dsimp only
  let firstCenter := a + b - 2 * a * b
  let firstSquare := 4 * a * b * (1 - a) * (1 - b)
  let secondCenter := c + d - 2 * c * d
  let secondSquare := 4 * c * d * (1 - c) * (1 - d)
  let denominator := 2 * (firstCenter - secondCenter)
  let numerator := (a - b) ^ 2 - (c - d) ^ 2
  have firstNormal := (exercise_7_6 firstTriple).2.2.2.2
  have secondNormal := (exercise_7_6 secondTriple).2.2.2.2
  change (x - firstCenter) ^ 2 = firstSquare at firstNormal
  change (x - secondCenter) ^ 2 = secondSquare at secondNormal
  have centerDifferenceNonzero : firstCenter - secondCenter ≠ 0 :=
    sub_ne_zero_of_ne centersDistinct
  have denominatorNonzero : denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero centerDifferenceNonzero
  have clearedEquation : denominator * x = numerator := by
    calc
      denominator * x =
          firstCenter ^ 2 - secondCenter ^ 2 -
            (x - firstCenter) ^ 2 + (x - secondCenter) ^ 2 := by
              unfold denominator
              ring1
      _ = firstCenter ^ 2 - secondCenter ^ 2 -
          firstSquare + secondSquare := by rw [firstNormal, secondNormal]
      _ = numerator := by
        unfold firstCenter secondCenter firstSquare secondSquare numerator
        ring1
  have valueEquation : x = numerator / denominator := by
    have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
      RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      x = x * 1 := by rw [mul_one]
      _ = x * (denominator * denominator⁻¹) := by rw [denominatorCancel]
      _ = (denominator * x) * denominator⁻¹ := by ring1
      _ = numerator * denominator⁻¹ := by rw [clearedEquation]
  have denominatorEquation :
      denominator =
        2 * (a + b - c - d - 2 * a * b + 2 * c * d) := by
    unfold denominator firstCenter secondCenter
    ring1
  have numeratorEquation :
      numerator = (a - b) ^ 2 - (c - d) ^ 2 := by
    rfl
  rw [← denominatorEquation, ← numeratorEquation]
  exact ⟨denominatorNonzero, valueEquation⟩

/-- Theorem 53 (Two spread triples), both clauses. -/
theorem two_spread_triples
    (a b c d x : K)
    (twoNonzero : (2 : K) ≠ 0)
    (firstTriple : SpreadTriple a b x)
    (secondTriple : SpreadTriple c d x) :
    quadrupleSpreadFunction a b c d = 0 ∧
      (a + b - 2 * a * b ≠ c + d - 2 * c * d →
        let denominator :=
          2 * (a + b - c - d - 2 * a * b + 2 * c * d)
        denominator ≠ 0 ∧
          x = ((a - b) ^ 2 - (c - d) ^ 2) / denominator) := by
  exact ⟨two_spread_triples_compatibility a b c d x firstTriple secondTriple,
    fun centersDistinct => two_spread_triples_common_value a b c d x
      twoNonzero firstTriple secondTriple centersDistinct⟩

/-- Exercise 7.13: two adjacent spread triples determine their common entry
by one explicit quotient.  The characteristic-two exclusion is exposed as
the executable witness `(2:K) ≠ 0`. -/
theorem exercise_7_13
    [DecidableEq K] (a b c x : K)
    (twoNonzero : (2 : K) ≠ 0)
    (firstTriple : SpreadTriple a b x)
    (secondTriple : SpreadTriple b c x)
    (outerDistinct : a ≠ c)
    (middleNotHalf : b ≠ (1 : K) / 2) :
    let denominator := 2 * (1 - 2 * b)
    denominator ≠ 0 ∧ x = (a + c - 2 * b) / denominator := by
  dsimp only
  have oneMinusTwiceMiddleNonzero : 1 - 2 * b ≠ 0 := by
    intro differenceZero
    apply middleNotHalf
    have twiceMiddle : 2 * b = 1 := (sub_eq_zero.mp differenceZero).symm
    have twoCancel : (2 : K) * 2⁻¹ = 1 :=
      RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      b = b * 1 := by rw [mul_one]
      _ = b * (2 * 2⁻¹) := by rw [twoCancel]
      _ = (2 * b) * 2⁻¹ := by ring1
      _ = 1 * 2⁻¹ := by rw [twiceMiddle]
  have denominatorNonzero : 2 * (1 - 2 * b) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero oneMinusTwiceMiddleNonzero
  have productZero :
      (a - c) *
        (2 * (1 - 2 * b) * x - (a + c - 2 * b)) = 0 := by
    calc
      (a - c) *
          (2 * (1 - 2 * b) * x - (a + c - 2 * b)) =
        tripleSpreadFunction a b x - tripleSpreadFunction b c x := by
          unfold tripleSpreadFunction
          ring1
      _ = 0 := by
        unfold SpreadTriple at firstTriple secondTriple
        rw [firstTriple, secondTriple]
        ring1
  have outerDifferenceNonzero : a - c ≠ 0 := sub_ne_zero_of_ne outerDistinct
  have clearedEquation : 2 * (1 - 2 * b) * x = a + c - 2 * b := by
    apply sub_eq_zero.mp
    by_cases remainingZero :
        2 * (1 - 2 * b) * x - (a + c - 2 * b) = 0
    · exact remainingZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero outerDifferenceNonzero remainingZero)
          productZero)
  have denominatorCancel :
      (2 * (1 - 2 * b)) * (2 * (1 - 2 * b))⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ denominatorNonzero
  refine ⟨denominatorNonzero, ?_⟩
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    x = x * 1 := by rw [mul_one]
    _ = x * ((2 * (1 - 2 * b)) * (2 * (1 - 2 * b))⁻¹) := by
      rw [denominatorCancel]
    _ = (2 * (1 - 2 * b) * x) * (2 * (1 - 2 * b))⁻¹ := by ring1
    _ = (a + c - 2 * b) * (2 * (1 - 2 * b))⁻¹ := by
      rw [clearedEquation]

private theorem spreadTriple_reorder {a b c : K}
    (triple : SpreadTriple a b c) : SpreadTriple c a b := by
  unfold SpreadTriple tripleSpreadFunction at triple ⊢
  calc
    (c + a + b) ^ 2 - 2 * (c ^ 2 + a ^ 2 + b ^ 2) - 4 * c * a * b =
        (a + b + c) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2) - 4 * a * b * c := by
          ring1
    _ = 0 := triple

private theorem spreadTriple_swap_last {a b c : K}
    (triple : SpreadTriple a b c) : SpreadTriple a c b := by
  unfold SpreadTriple tripleSpreadFunction at triple ⊢
  calc
    (a + c + b) ^ 2 - 2 * (a ^ 2 + c ^ 2 + b ^ 2) - 4 * a * c * b =
        (a + b + c) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2) - 4 * a * b * c := by
          ring1
    _ = 0 := triple

/-- The polynomial clause of Theorem 54, without the characteristic
assumption needed only by its two quotient formulas. -/
theorem quadruple_spread_relation
    (first second third fourth : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull) (fourthNonNull : ¬ fourth.IsNull) :
    let s₁₂ := spread first second firstNonNull secondNonNull
    let s₂₃ := spread second third secondNonNull thirdNonNull
    let s₃₄ := spread third fourth thirdNonNull fourthNonNull
    let s₁₄ := spread first fourth firstNonNull fourthNonNull
    quadrupleSpreadFunction s₁₂ s₂₃ s₃₄ s₁₄ = 0 := by
  dsimp only
  let s₁₂ := spread first second firstNonNull secondNonNull
  let s₂₃ := spread second third secondNonNull thirdNonNull
  let s₃₄ := spread third fourth thirdNonNull fourthNonNull
  let s₁₄ := spread first fourth firstNonNull fourthNonNull
  let s₁₃ := spread first third firstNonNull thirdNonNull
  have firstRaw := three_lines_form_spreadTriple first second third firstNonNull
    secondNonNull thirdNonNull
  have firstTriple : SpreadTriple s₁₂ s₂₃ s₁₃ := by
    exact spreadTriple_reorder firstRaw
  have secondTriple : SpreadTriple s₃₄ s₁₄ s₁₃ :=
    three_lines_form_spreadTriple first third fourth firstNonNull thirdNonNull
      fourthNonNull
  exact two_spread_triples_compatibility s₁₂ s₂₃ s₃₄ s₁₄ s₁₃
    firstTriple secondTriple

/-- Theorem 54 (Quadruple spread formula), including both diagonal-spread
formulas under their exact nondegeneracy hypotheses. -/
theorem quadruple_spread_formula
    (first second third fourth : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull) (fourthNonNull : ¬ fourth.IsNull)
    (twoNonzero : (2 : K) ≠ 0) :
    let s₁₂ := spread first second firstNonNull secondNonNull
    let s₂₃ := spread second third secondNonNull thirdNonNull
    let s₃₄ := spread third fourth thirdNonNull fourthNonNull
    let s₁₄ := spread first fourth firstNonNull fourthNonNull
    let s₁₃ := spread first third firstNonNull thirdNonNull
    let s₂₄ := spread second fourth secondNonNull fourthNonNull
    quadrupleSpreadFunction s₁₂ s₂₃ s₃₄ s₁₄ = 0 ∧
      (s₁₂ + s₂₃ - 2 * s₁₂ * s₂₃ ≠
          s₃₄ + s₁₄ - 2 * s₃₄ * s₁₄ →
        let denominator :=
          2 * (s₁₂ + s₂₃ - s₃₄ - s₁₄ -
            2 * s₁₂ * s₂₃ + 2 * s₃₄ * s₁₄)
        denominator ≠ 0 ∧
          s₁₃ = ((s₁₂ - s₂₃) ^ 2 - (s₃₄ - s₁₄) ^ 2) /
            denominator) ∧
      (s₂₃ + s₃₄ - 2 * s₂₃ * s₃₄ ≠
          s₁₂ + s₁₄ - 2 * s₁₂ * s₁₄ →
        let denominator :=
          2 * (s₂₃ + s₃₄ - s₁₂ - s₁₄ -
            2 * s₂₃ * s₃₄ + 2 * s₁₂ * s₁₄)
        denominator ≠ 0 ∧
          s₂₄ = ((s₂₃ - s₃₄) ^ 2 - (s₁₂ - s₁₄) ^ 2) /
            denominator) := by
  dsimp only
  let s₁₂ := spread first second firstNonNull secondNonNull
  let s₂₃ := spread second third secondNonNull thirdNonNull
  let s₃₄ := spread third fourth thirdNonNull fourthNonNull
  let s₁₄ := spread first fourth firstNonNull fourthNonNull
  let s₁₃ := spread first third firstNonNull thirdNonNull
  let s₂₄ := spread second fourth secondNonNull fourthNonNull
  have firstRaw := three_lines_form_spreadTriple first second third firstNonNull
    secondNonNull thirdNonNull
  have firstTriple : SpreadTriple s₁₂ s₂₃ s₁₃ := by
    exact spreadTriple_reorder firstRaw
  have secondTriple : SpreadTriple s₃₄ s₁₄ s₁₃ :=
    three_lines_form_spreadTriple first third fourth firstNonNull thirdNonNull
      fourthNonNull
  have thirdRaw := three_lines_form_spreadTriple second third fourth
    secondNonNull thirdNonNull fourthNonNull
  have thirdTriple : SpreadTriple s₂₃ s₃₄ s₂₄ := by
    exact spreadTriple_reorder thirdRaw
  have fourthRaw := three_lines_form_spreadTriple first second fourth
    firstNonNull secondNonNull fourthNonNull
  have fourthTriple : SpreadTriple s₁₂ s₁₄ s₂₄ := by
    exact spreadTriple_swap_last (spreadTriple_reorder fourthRaw)
  have firstResult := two_spread_triples s₁₂ s₂₃ s₃₄ s₁₄ s₁₃
    twoNonzero firstTriple secondTriple
  have secondResult := two_spread_triples s₂₃ s₃₄ s₁₂ s₁₄ s₂₄
    twoNonzero thirdTriple fourthTriple
  exact ⟨firstResult.1, firstResult.2, secondResult.2⟩

/-- Complementing all four arguments leaves the quadruple function fixed. -/
theorem quadrupleSpreadFunction_complement (a b c d : K) :
    quadrupleSpreadFunction (1 - a) (1 - b) (1 - c) (1 - d) =
      quadrupleSpreadFunction a b c d := by
  unfold quadrupleSpreadFunction quadrupleSpreadCore
  ring1

/-- Theorem 55 (Quadruple cross formula). -/
theorem quadruple_cross_formula
    (first second third fourth : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull) (fourthNonNull : ¬ fourth.IsNull) :
    quadrupleSpreadFunction
      (cross first second firstNonNull secondNonNull)
      (cross second third secondNonNull thirdNonNull)
      (cross third fourth thirdNonNull fourthNonNull)
      (cross first fourth firstNonNull fourthNonNull) = 0 := by
  let s₁₂ := spread first second firstNonNull secondNonNull
  let s₂₃ := spread second third secondNonNull thirdNonNull
  let s₃₄ := spread third fourth thirdNonNull fourthNonNull
  let s₁₄ := spread first fourth firstNonNull fourthNonNull
  have spreadRelation := quadruple_spread_relation first second third fourth
    firstNonNull secondNonNull thirdNonNull fourthNonNull
  have firstComplement :
      cross first second firstNonNull secondNonNull = 1 - s₁₂ := by
    have sum := spread_add_cross first second firstNonNull secondNonNull
    unfold s₁₂
    calc
      cross first second firstNonNull secondNonNull =
          (spread first second firstNonNull secondNonNull +
            cross first second firstNonNull secondNonNull) -
            spread first second firstNonNull secondNonNull := by ring1
      _ = 1 - spread first second firstNonNull secondNonNull := by rw [sum]
  have secondComplement :
      cross second third secondNonNull thirdNonNull = 1 - s₂₃ := by
    have sum := spread_add_cross second third secondNonNull thirdNonNull
    unfold s₂₃
    calc
      cross second third secondNonNull thirdNonNull =
          (spread second third secondNonNull thirdNonNull +
            cross second third secondNonNull thirdNonNull) -
            spread second third secondNonNull thirdNonNull := by ring1
      _ = 1 - spread second third secondNonNull thirdNonNull := by rw [sum]
  have thirdComplement :
      cross third fourth thirdNonNull fourthNonNull = 1 - s₃₄ := by
    have sum := spread_add_cross third fourth thirdNonNull fourthNonNull
    unfold s₃₄
    calc
      cross third fourth thirdNonNull fourthNonNull =
          (spread third fourth thirdNonNull fourthNonNull +
            cross third fourth thirdNonNull fourthNonNull) -
            spread third fourth thirdNonNull fourthNonNull := by ring1
      _ = 1 - spread third fourth thirdNonNull fourthNonNull := by rw [sum]
  have fourthComplement :
      cross first fourth firstNonNull fourthNonNull = 1 - s₁₄ := by
    have sum := spread_add_cross first fourth firstNonNull fourthNonNull
    unfold s₁₄
    calc
      cross first fourth firstNonNull fourthNonNull =
          (spread first fourth firstNonNull fourthNonNull +
            cross first fourth firstNonNull fourthNonNull) -
            spread first fourth firstNonNull fourthNonNull := by ring1
      _ = 1 - spread first fourth firstNonNull fourthNonNull := by rw [sum]
  rw [firstComplement, secondComplement, thirdComplement, fourthComplement,
    quadrupleSpreadFunction_complement]
  exact spreadRelation

/-- The Spread-plus-cross theorem solved for the spread. -/
theorem spread_eq_one_sub_cross
    (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) :
    spread first second firstNonNull secondNonNull =
      1 - cross first second firstNonNull secondNonNull := by
  have sum := spread_add_cross first second firstNonNull secondNonNull
  calc
    spread first second firstNonNull secondNonNull =
        (spread first second firstNonNull secondNonNull +
          cross first second firstNonNull secondNonNull) -
          cross first second firstNonNull secondNonNull := by ring1
    _ = 1 - cross first second firstNonNull secondNonNull := by rw [sum]

/-- The constructive diagonal-cross calculation.  Unlike the diagonal-spread
formula, complementation leaves an outer `1-`; Exercise 7.14 omits it. -/
theorem two_cross_triples_common_value
    (a b c d x : K)
    (twoNonzero : (2 : K) ≠ 0)
    (firstTriple : SpreadTriple (1 - a) (1 - b) (1 - x))
    (secondTriple : SpreadTriple (1 - c) (1 - d) (1 - x))
    (centersDistinct :
      a + b - 2 * a * b ≠ c + d - 2 * c * d) :
    let denominator := 2 * (a + b - c - d - 2 * a * b + 2 * c * d)
    denominator ≠ 0 ∧
      x = 1 - ((a - b) ^ 2 - (c - d) ^ 2) / denominator := by
  dsimp only
  have complementedCentersDistinct :
      (1 - a) + (1 - b) - 2 * (1 - a) * (1 - b) ≠
        (1 - c) + (1 - d) - 2 * (1 - c) * (1 - d) := by
    intro centersEqual
    apply centersDistinct
    calc
      a + b - 2 * a * b =
          (1 - a) + (1 - b) - 2 * (1 - a) * (1 - b) := by ring1
      _ = (1 - c) + (1 - d) - 2 * (1 - c) * (1 - d) := centersEqual
      _ = c + d - 2 * c * d := by ring1
  have result := two_spread_triples_common_value
    (1 - a) (1 - b) (1 - c) (1 - d) (1 - x)
    twoNonzero firstTriple secondTriple complementedCentersDistinct
  dsimp only at result
  have denominatorEquality :
      2 * ((1 - a) + (1 - b) - (1 - c) - (1 - d) -
          2 * (1 - a) * (1 - b) + 2 * (1 - c) * (1 - d)) =
        2 * (a + b - c - d - 2 * a * b + 2 * c * d) := by ring1
  have numeratorEquality :
      ((1 - a) - (1 - b)) ^ 2 - ((1 - c) - (1 - d)) ^ 2 =
        (a - b) ^ 2 - (c - d) ^ 2 := by ring1
  constructor
  · rw [← denominatorEquality]
    exact result.1
  · calc
      x = 1 - (1 - x) := by ring1
      _ = 1 -
          (((1 - a) - (1 - b)) ^ 2 - ((1 - c) - (1 - d)) ^ 2) /
            (2 * ((1 - a) + (1 - b) - (1 - c) - (1 - d) -
              2 * (1 - a) * (1 - b) +
              2 * (1 - c) * (1 - d))) := by rw [result.2]
      _ = 1 - ((a - b) ^ 2 - (c - d) ^ 2) /
          (2 * (a + b - c - d - 2 * a * b + 2 * c * d)) := by
        rw [numeratorEquality, denominatorEquality]

/-- Corrected Exercise 7.14.  Both printed right-hand sides determine the
complements of the requested diagonal crosses. -/
theorem exercise_7_14_corrected
    (first second third fourth : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull) (fourthNonNull : ¬ fourth.IsNull)
    (twoNonzero : (2 : K) ≠ 0) :
    let c₁₂ := cross first second firstNonNull secondNonNull
    let c₂₃ := cross second third secondNonNull thirdNonNull
    let c₃₄ := cross third fourth thirdNonNull fourthNonNull
    let c₁₄ := cross first fourth firstNonNull fourthNonNull
    let c₁₃ := cross first third firstNonNull thirdNonNull
    let c₂₄ := cross second fourth secondNonNull fourthNonNull
    (c₁₂ + c₂₃ - 2 * c₁₂ * c₂₃ ≠
        c₃₄ + c₁₄ - 2 * c₃₄ * c₁₄ →
      let denominator :=
        2 * (c₁₂ + c₂₃ - c₃₄ - c₁₄ -
          2 * c₁₂ * c₂₃ + 2 * c₃₄ * c₁₄)
      denominator ≠ 0 ∧
        c₁₃ = 1 -
          ((c₁₂ - c₂₃) ^ 2 - (c₃₄ - c₁₄) ^ 2) /
            denominator) ∧
    (c₂₃ + c₃₄ - 2 * c₂₃ * c₃₄ ≠
        c₁₂ + c₁₄ - 2 * c₁₂ * c₁₄ →
      let denominator :=
        2 * (c₂₃ + c₃₄ - c₁₂ - c₁₄ -
          2 * c₂₃ * c₃₄ + 2 * c₁₂ * c₁₄)
      denominator ≠ 0 ∧
        c₂₄ = 1 -
          ((c₂₃ - c₃₄) ^ 2 - (c₁₂ - c₁₄) ^ 2) /
            denominator) := by
  dsimp only
  let c₁₂ := cross first second firstNonNull secondNonNull
  let c₂₃ := cross second third secondNonNull thirdNonNull
  let c₃₄ := cross third fourth thirdNonNull fourthNonNull
  let c₁₄ := cross first fourth firstNonNull fourthNonNull
  let c₁₃ := cross first third firstNonNull thirdNonNull
  let c₂₄ := cross second fourth secondNonNull fourthNonNull
  have firstRaw := three_lines_form_spreadTriple first second third firstNonNull
    secondNonNull thirdNonNull
  have firstSpreadTriple : SpreadTriple
      (spread first second firstNonNull secondNonNull)
      (spread second third secondNonNull thirdNonNull)
      (spread first third firstNonNull thirdNonNull) :=
    spreadTriple_reorder firstRaw
  have firstCrossTriple : SpreadTriple (1 - c₁₂) (1 - c₂₃) (1 - c₁₃) := by
    unfold c₁₂ c₂₃ c₁₃
    rw [← spread_eq_one_sub_cross first second firstNonNull secondNonNull,
      ← spread_eq_one_sub_cross second third secondNonNull thirdNonNull,
      ← spread_eq_one_sub_cross first third firstNonNull thirdNonNull]
    exact firstSpreadTriple
  have secondSpreadTriple : SpreadTriple
      (spread third fourth thirdNonNull fourthNonNull)
      (spread first fourth firstNonNull fourthNonNull)
      (spread first third firstNonNull thirdNonNull) :=
    three_lines_form_spreadTriple first third fourth firstNonNull thirdNonNull
      fourthNonNull
  have secondCrossTriple : SpreadTriple (1 - c₃₄) (1 - c₁₄) (1 - c₁₃) := by
    unfold c₃₄ c₁₄ c₁₃
    rw [← spread_eq_one_sub_cross third fourth thirdNonNull fourthNonNull,
      ← spread_eq_one_sub_cross first fourth firstNonNull fourthNonNull,
      ← spread_eq_one_sub_cross first third firstNonNull thirdNonNull]
    exact secondSpreadTriple
  have thirdRaw := three_lines_form_spreadTriple second third fourth
    secondNonNull thirdNonNull fourthNonNull
  have thirdSpreadTriple : SpreadTriple
      (spread second third secondNonNull thirdNonNull)
      (spread third fourth thirdNonNull fourthNonNull)
      (spread second fourth secondNonNull fourthNonNull) :=
    spreadTriple_reorder thirdRaw
  have thirdCrossTriple : SpreadTriple (1 - c₂₃) (1 - c₃₄) (1 - c₂₄) := by
    unfold c₂₃ c₃₄ c₂₄
    rw [← spread_eq_one_sub_cross second third secondNonNull thirdNonNull,
      ← spread_eq_one_sub_cross third fourth thirdNonNull fourthNonNull,
      ← spread_eq_one_sub_cross second fourth secondNonNull fourthNonNull]
    exact thirdSpreadTriple
  have fourthRaw := three_lines_form_spreadTriple first second fourth
    firstNonNull secondNonNull fourthNonNull
  have fourthSpreadTriple : SpreadTriple
      (spread first second firstNonNull secondNonNull)
      (spread first fourth firstNonNull fourthNonNull)
      (spread second fourth secondNonNull fourthNonNull) :=
    spreadTriple_swap_last (spreadTriple_reorder fourthRaw)
  have fourthCrossTriple : SpreadTriple (1 - c₁₂) (1 - c₁₄) (1 - c₂₄) := by
    unfold c₁₂ c₁₄ c₂₄
    rw [← spread_eq_one_sub_cross first second firstNonNull secondNonNull,
      ← spread_eq_one_sub_cross first fourth firstNonNull fourthNonNull,
      ← spread_eq_one_sub_cross second fourth secondNonNull fourthNonNull]
    exact fourthSpreadTriple
  constructor
  · intro centersDistinct
    exact two_cross_triples_common_value c₁₂ c₂₃ c₃₄ c₁₄ c₁₃
      twoNonzero firstCrossTriple secondCrossTriple centersDistinct
  · intro centersDistinct
    exact two_cross_triples_common_value c₂₃ c₃₄ c₁₂ c₁₄ c₂₄
      twoNonzero thirdCrossTriple fourthCrossTriple centersDistinct

namespace ExerciseSevenFourteenCounterexample

abbrev F₁₁ := FieldEleven.Element

def line₁ : Line F₁₁ := ⟨1, 0, 0, Or.inl (by decide)⟩
def line₂ : Line F₁₁ := ⟨1, 1, 0, Or.inl (by decide)⟩
def line₃ : Line F₁₁ := ⟨0, 1, 0, Or.inr (by decide)⟩
def line₄ : Line F₁₁ := ⟨1, 2, 0, Or.inl (by decide)⟩

theorem line₁_nonNull : ¬ line₁.IsNull := by
  unfold Line.IsNull line₁
  decide

theorem line₂_nonNull : ¬ line₂.IsNull := by
  unfold Line.IsNull line₂
  decide

theorem line₃_nonNull : ¬ line₃.IsNull := by
  unfold Line.IsNull line₃
  decide

theorem line₄_nonNull : ¬ line₄.IsNull := by
  unfold Line.IsNull line₄
  decide

/-- The adjacent crosses are `6,6,3,9` in `F₁₁`, while the first
diagonal cross is zero. -/
theorem cross_values :
    cross line₁ line₂ line₁_nonNull line₂_nonNull = 6 ∧
      cross line₂ line₃ line₂_nonNull line₃_nonNull = 6 ∧
      cross line₃ line₄ line₃_nonNull line₄_nonNull = 3 ∧
      cross line₁ line₄ line₁_nonNull line₄_nonNull = 9 ∧
      cross line₁ line₃ line₁_nonNull line₃_nonNull = 0 := by
  decide

/-- Exercise 7.14's first printed right-hand side is one, not the actual
diagonal cross zero. -/
theorem printed_first_formula_fails :
    let c₁₂ := cross line₁ line₂ line₁_nonNull line₂_nonNull
    let c₂₃ := cross line₂ line₃ line₂_nonNull line₃_nonNull
    let c₃₄ := cross line₃ line₄ line₃_nonNull line₄_nonNull
    let c₁₄ := cross line₁ line₄ line₁_nonNull line₄_nonNull
    let c₁₃ := cross line₁ line₃ line₁_nonNull line₃_nonNull
    let denominator :=
      2 * (c₁₂ + c₂₃ - c₃₄ - c₁₄ -
        2 * c₁₂ * c₂₃ + 2 * c₃₄ * c₁₄)
    denominator ≠ 0 ∧
      c₁₃ ≠ ((c₁₂ - c₂₃) ^ 2 - (c₃₄ - c₁₄) ^ 2) /
        denominator := by
  decide

end ExerciseSevenFourteenCounterexample

/-- The pairwise spread table of a requested finite family of non-null lines. -/
def finiteSpread {n : Nat}
    (lines : Fin n → Line K) (nonNull : ∀ index, ¬ (lines index).IsNull)
    (first second : Fin n) : K :=
  spread (lines first) (lines second) (nonNull first) (nonNull second)

/-- Every three entries of a finite spread table satisfy the Triple-spread
relation. -/
theorem finite_spread_triples {n : Nat}
    (lines : Fin n → Line K) (nonNull : ∀ index, ¬ (lines index).IsNull)
    (first second third : Fin n) :
    SpreadTriple
      (finiteSpread lines nonNull second third)
      (finiteSpread lines nonNull first third)
      (finiteSpread lines nonNull first second) :=
  three_lines_form_spreadTriple (lines first) (lines second) (lines third)
    (nonNull first) (nonNull second) (nonNull third)

/-- Every four entries of the same finite table satisfy the Quadruple-spread
relation. -/
theorem finite_quadruple_spread_relations {n : Nat}
    (lines : Fin n → Line K) (nonNull : ∀ index, ¬ (lines index).IsNull)
    (first second third fourth : Fin n) :
    quadrupleSpreadFunction
      (finiteSpread lines nonNull first second)
      (finiteSpread lines nonNull second third)
      (finiteSpread lines nonNull third fourth)
      (finiteSpread lines nonNull first fourth) = 0 :=
  quadruple_spread_relation (lines first) (lines second) (lines third)
    (lines fourth) (nonNull first) (nonNull second) (nonNull third)
    (nonNull fourth)

/-- Exercise 7.15: a quintuple, and more generally every requested finite
line family, has a bounded compatibility system consisting of all of its
Triple- and Quadruple-spread relations.  This avoids pretending that the open
question supplied a particular giant eliminated polynomial. -/
theorem exercise_7_15
    (lines : Fin 5 → Line K) (nonNull : ∀ index, ¬ (lines index).IsNull) :
    (∀ first second third,
      SpreadTriple
        (finiteSpread lines nonNull second third)
        (finiteSpread lines nonNull first third)
        (finiteSpread lines nonNull first second)) ∧
      (∀ first second third fourth,
        quadrupleSpreadFunction
          (finiteSpread lines nonNull first second)
          (finiteSpread lines nonNull second third)
          (finiteSpread lines nonNull third fourth)
          (finiteSpread lines nonNull first fourth) = 0) := by
  exact ⟨finite_spread_triples lines nonNull,
    finite_quadruple_spread_relations lines nonNull⟩

end DivineProportions
