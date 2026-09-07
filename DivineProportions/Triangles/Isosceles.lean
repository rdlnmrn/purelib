import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Trigonometry.TriangleRatios
import DivineProportions.Trigonometry.TripleSpread

/-!
# Divine Proportions, Chapter 10: isosceles triangles

The scalar forms isolate the finite cancellations used by the geometric
statements.  They apply uniformly to ratios obtained from rational triangles
or from triangles over explicit finite fields.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

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

private theorem eq_of_mul_eq_mul_left
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  apply eq_of_mul_eq_mul_right factorNonzero
  calc
    left * factor = factor * left := by ring1
    _ = factor * right := productsEqual
    _ = right * factor := by ring1

private theorem div_eq_div_of_cross_mul
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

/-- Theorem 64 (Null isosceles), for the displayed equal pair `Q₁ = Q₂`.
The two alternatives say respectively that exactly those two sides are null,
or that no side is null. -/
theorem null_isosceles [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (equalQuadrances :
      quadrance second third = quadrance first third) :
    (quadrance second third = 0 ∧
        quadrance first third = 0 ∧ quadrance first second ≠ 0) ∨
      (quadrance second third ≠ 0 ∧
        quadrance first third ≠ 0 ∧ quadrance first second ≠ 0) := by
  have quadreaNonzero : quadrea first second third ≠ 0 :=
    (quadrea_ne_zero_iff_not_collinear first second third twoNonzero).2
      notCollinear
  have thirdQuadranceNonzero : quadrance first second ≠ 0 := by
    intro thirdZero
    apply quadreaNonzero
    unfold quadrea
    rw [equalQuadrances, thirdZero]
    unfold archimedesFunction
    ring1
  by_cases firstEqualQuadranceZero : quadrance second third = 0
  · left
    exact ⟨firstEqualQuadranceZero,
      equalQuadrances.symm.trans firstEqualQuadranceZero,
      thirdQuadranceNonzero⟩
  · right
    have secondEqualQuadranceNonzero : quadrance first third ≠ 0 := by
      intro secondZero
      exact firstEqualQuadranceZero (equalQuadrances.trans secondZero)
    exact ⟨firstEqualQuadranceZero, secondEqualQuadranceNonzero,
      thirdQuadranceNonzero⟩

/-- Theorem 65 (Pons Asinorum), in the exact scalar form supplied by the
Spread law.  Non-nullity of the triangle supplies the four nonzero premises. -/
theorem pons_asinorum
    (q₁ q₂ s₁ s₂ : K)
    (q₁Nonzero : q₁ ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (s₁Nonzero : s₁ ≠ 0)
    (spreadLaw : s₁ / q₁ = s₂ / q₂) :
    q₁ = q₂ ↔ s₁ = s₂ := by
  have crossProduct : s₁ * q₂ = s₂ * q₁ := by
    calc
      s₁ * q₂ = ((s₁ / q₁) * q₁) * q₂ := by
        rw [RFAP.ExplicitField.div_mul_cancel s₁ q₁Nonzero]
      _ = (s₁ / q₁) * (q₁ * q₂) := by ring1
      _ = (s₂ / q₂) * (q₁ * q₂) := by rw [spreadLaw]
      _ = ((s₂ / q₂) * q₂) * q₁ := by ring1
      _ = s₂ * q₁ := by
        rw [RFAP.ExplicitField.div_mul_cancel s₂ q₂Nonzero]
  constructor
  · intro quadrancesEqual
    apply eq_of_mul_eq_mul_right q₂Nonzero
    calc
      s₁ * q₂ = s₂ * q₁ := crossProduct
      _ = s₂ * q₂ := by rw [quadrancesEqual]
  · intro spreadsEqual
    apply eq_of_mul_eq_mul_left s₁Nonzero
    calc
      s₁ * q₁ = s₂ * q₁ := by rw [spreadsEqual]
      _ = s₁ * q₂ := crossProduct.symm

/-- Theorem 66 (Isosceles triangle), retaining the two formulas printed in
the source.  `spreadLaw` and `equalSpreads` are precisely the earlier named
theorems after substituting `Q₁ = Q₂` and `s₁ = s₂`. -/
theorem isosceles_triangle
    (q q₃ s s₃ : K)
    (qNonzero : q ≠ 0) (q₃Nonzero : q₃ ≠ 0)
    (sNonzero : s ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (spreadLaw : s / q = s₃ / q₃)
    (equalSpreads : s₃ = 4 * s * (1 - s)) :
    q₃ = 4 * q * (1 - s) ∧
      s₃ = (q₃ / q) * (1 - q₃ / (4 * q)) := by
  have crossProduct : s * q₃ = s₃ * q := by
    calc
      s * q₃ = ((s / q) * q) * q₃ := by
        rw [RFAP.ExplicitField.div_mul_cancel s qNonzero]
      _ = (s / q) * (q * q₃) := by ring1
      _ = (s₃ / q₃) * (q * q₃) := by rw [spreadLaw]
      _ = ((s₃ / q₃) * q₃) * q := by ring1
      _ = s₃ * q := by
        rw [RFAP.ExplicitField.div_mul_cancel s₃ q₃Nonzero]
  have thirdQuadrance : q₃ = 4 * q * (1 - s) := by
    apply eq_of_mul_eq_mul_left sNonzero
    calc
      s * q₃ = s₃ * q := crossProduct
      _ = (4 * s * (1 - s)) * q := by rw [equalSpreads]
      _ = s * (4 * q * (1 - s)) := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero := RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  have fourQNonzero : (4 : K) * q ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero fourNonzero qNonzero
  have firstRatio : q₃ / q = 4 * (1 - s) := by
    apply eq_of_mul_eq_mul_right qNonzero
    calc
      (q₃ / q) * q = q₃ :=
        RFAP.ExplicitField.div_mul_cancel q₃ qNonzero
      _ = 4 * q * (1 - s) := thirdQuadrance
      _ = (4 * (1 - s)) * q := by ring1
  have secondRatio : q₃ / (4 * q) = 1 - s := by
    apply eq_of_mul_eq_mul_right fourQNonzero
    calc
      (q₃ / (4 * q)) * (4 * q) = q₃ :=
        RFAP.ExplicitField.div_mul_cancel q₃ fourQNonzero
      _ = 4 * q * (1 - s) := thirdQuadrance
      _ = (1 - s) * (4 * q) := by ring1
  constructor
  · exact thirdQuadrance
  · rw [firstRatio, secondRatio, equalSpreads]
    ring1

/-- Theorem 68 (Isosceles reflection).  The two premises are the Spread-ratio
value in the right half-triangle and the midpoint quadrance from Theorem 20. -/
theorem isosceles_reflection
    (q q₃ r midpointQuadrance : K)
    (qNonzero : q ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (spreadRatio : r = midpointQuadrance / q)
    (midpointValue : midpointQuadrance = q₃ / 4) :
    q₃ = 4 * r * q := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero := RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  have ratioCleared : r * q = midpointQuadrance := by
    rw [spreadRatio]
    exact RFAP.ExplicitField.div_mul_cancel midpointQuadrance qNonzero
  have midpointCleared : midpointQuadrance * 4 = q₃ := by
    rw [midpointValue]
    exact RFAP.ExplicitField.div_mul_cancel q₃ fourNonzero
  calc
    q₃ = midpointQuadrance * 4 := midpointCleared.symm
    _ = (r * q) * 4 := by rw [ratioCleared]
    _ = 4 * r * q := by ring1

/-- Theorem 69 (Equilateral triangle), in terms of the common spread and
quadrance.  The common cross is represented by its complement `1 - s`. -/
theorem equilateral_triangle [DecidableEq K]
    (q s : K) (sNonzero : s ≠ 0) (fourNonzero : (4 : K) ≠ 0)
    (spreadTriple : SpreadTriple s s s) :
    s = 3 / 4 ∧
      1 - s = 1 / 4 ∧
      archimedesFunction q q q = 3 * q ^ 2 := by
  have squareNonzero : s ^ 2 ≠ 0 := by
    simpa [pow_two] using RFAP.ExplicitField.mul_ne_zero sNonzero sNonzero
  have factorZero : s ^ 2 * (3 - 4 * s) = 0 := by
    unfold SpreadTriple tripleSpreadFunction at spreadTriple
    calc
      s ^ 2 * (3 - 4 * s) =
          (s + s + s) ^ 2 - 2 * (s ^ 2 + s ^ 2 + s ^ 2) -
            4 * s * s * s := by ring1
      _ = 0 := spreadTriple
  have linearZero : 3 - 4 * s = 0 := by
    by_cases zero : 3 - 4 * s = 0
    · exact zero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero squareNonzero zero) factorZero)
  have spreadValue : s = 3 / 4 := by
    apply eq_of_mul_eq_mul_right fourNonzero
    calc
      s * 4 = 3 := by
        calc
          s * 4 = 3 - (3 - 4 * s) := by ring1
          _ = 3 := by rw [linearZero]; ring1
      _ = (3 / 4) * 4 :=
        (RFAP.ExplicitField.div_mul_cancel 3 fourNonzero).symm
  have crossValue : 1 - s = 1 / 4 := by
    apply eq_of_mul_eq_mul_right fourNonzero
    calc
      (1 - s) * 4 = (1 - 3 / 4) * 4 := by rw [spreadValue]
      _ = 4 - (3 / 4) * 4 := by ring1
      _ = 1 := by
        rw [RFAP.ExplicitField.div_mul_cancel 3 fourNonzero]
        ring1
      _ = (1 / 4) * 4 :=
        (RFAP.ExplicitField.div_mul_cancel 1 fourNonzero).symm
  exact ⟨spreadValue, crossValue, by
    unfold archimedesFunction
    ring1⟩

/-- Exercise 10.1.  The first premise is the complemented Equal-spreads
formula, while the last two premises are the spread/cross definitions of the
two twists.  Nonzero crosses are precisely the finite denominators required
for those twists to be defined. -/
theorem exercise_10_1
    (c c₃ t t₃ : K) (cNonzero : c ≠ 0) (c₃Nonzero : c₃ ≠ 0)
    (thirdCross : c₃ = 1 - 4 * (1 - c) * c)
    (twistValue : t = (1 - c) / c)
    (thirdTwistValue : t₃ = (1 - c₃) / c₃) :
    c₃ = (2 * c - 1) ^ 2 ∧
      t₃ = 4 * t / (1 - t) ^ 2 := by
  have thirdCrossFormula : c₃ = (2 * c - 1) ^ 2 := by
    rw [thirdCross]
    ring1
  have inverseCancel : c * c⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel c cNonzero
  have oneMinusTwist : 1 - t = (2 * c - 1) * c⁻¹ := by
    rw [twistValue]
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      1 - (1 - c) * c⁻¹ =
          (2 * c - 1) * c⁻¹ + (1 - c * c⁻¹) := by ring1
      _ = (2 * c - 1) * c⁻¹ := by rw [inverseCancel]; ring1
  have crossFactorNonzero : 2 * c - 1 ≠ 0 := by
    intro factorZero
    apply c₃Nonzero
    rw [thirdCrossFormula, factorZero]
    ring1
  have oneMinusTwistNonzero : 1 - t ≠ 0 := by
    rw [oneMinusTwist]
    exact RFAP.ExplicitField.mul_ne_zero crossFactorNonzero
      (RFAP.ExplicitField.inv_ne_zero cNonzero)
  have oneMinusTwistSquareNonzero : (1 - t) ^ 2 ≠ 0 := by
    simpa [pow_two] using RFAP.ExplicitField.mul_ne_zero
      oneMinusTwistNonzero oneMinusTwistNonzero
  have oneMinusThirdCross : 1 - c₃ = 4 * c * (1 - c) := by
    rw [thirdCrossFormula]
    ring1
  constructor
  · exact thirdCrossFormula
  · rw [thirdTwistValue]
    apply div_eq_div_of_cross_mul c₃Nonzero
      oneMinusTwistSquareNonzero
    rw [oneMinusThirdCross, oneMinusTwist, twistValue,
      thirdCrossFormula]
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      4 * c * (1 - c) * (((2 * c - 1) * c⁻¹) ^ 2) =
          4 * (1 - c) * (2 * c - 1) ^ 2 *
            (c * c⁻¹) * c⁻¹ := by ring1
      _ = 4 * ((1 - c) * c⁻¹) * (2 * c - 1) ^ 2 := by
        rw [inverseCancel]
        ring1

/-- Exercise 10.2's two factorizations of the isosceles quadrea agree once
the Isosceles triangle theorem has supplied `Q₃ = 4Q(1-s)`. -/
theorem exercise_10_2
    (q q₃ s : K) (thirdQuadrance : q₃ = 4 * q * (1 - s)) :
    16 * q ^ 2 * s * (1 - s) = q₃ * (4 * q - q₃) := by
  rw [thirdQuadrance]
  ring1

/-- Exercise 10.3's finite content.  If the equal pair of an isosceles
triangle is null, the remaining side is necessarily non-null and the quadrea
is the negative square of its quadrance.  In particular the spread-based
conclusions of the preceding theorems are not defined on the two null sides. -/
theorem exercise_10_3 [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (equalQuadrances :
      quadrance second third = quadrance first third)
    (firstNull : quadrance second third = 0) :
    quadrance second third = 0 ∧
      quadrance first third = 0 ∧
      quadrance first second ≠ 0 ∧
      quadrea first second third = -(quadrance first second) ^ 2 := by
  have secondNull : quadrance first third = 0 :=
    equalQuadrances.symm.trans firstNull
  have alternatives := null_isosceles first second third notCollinear
    twoNonzero equalQuadrances
  have thirdNonNull : quadrance first second ≠ 0 := by
    rcases alternatives with nullPair | nonNullTriple
    · exact nullPair.2.2
    · exact False.elim (nonNullTriple.1 firstNull)
  refine ⟨firstNull, secondNull, thirdNonNull, ?_⟩
  unfold quadrea archimedesFunction
  rw [firstNull, secondNull]
  ring1

end DivineProportions
