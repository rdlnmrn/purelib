import DivineProportions.Proportions.TwoStruts
import DivineProportions.Proportions.Stewart
import DivineProportions.Proportions.MenelausCeva
import DivineProportions.Trigonometry.TripleSpread
import DivineProportions.Triangles.Right

/-!
# Divine Proportions, Chapter 11 exercises

This module begins the reader problems following the Two-struts theorem.  All
normalizations are retained as finite polynomial equalities.  In particular,
Example 11.1 is checked by scaling the two quad triples by the displayed
factor `256`; no quadratic formula or selected root is used.
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

/-- Denominator-free core of Exercise 11.1.  The Triangle-proportions
cross-product and `s₁+s₂=1` leave exactly one finite common denominator. -/
theorem exercise_11_1_cleared [DecidableEq K]
    (r₁ r₂ s₁ s₂ R₁ R₂ : K)
    (rightTriangle : SpreadTriple s₁ s₂ 1)
    (triangleProportion :
      r₁ * (s₂ * R₂) = (s₁ * R₁) * r₂) :
    s₁ * (r₁ * R₂ + r₂ * R₁) = r₁ * R₂ := by
  have spreadSum : s₁ + s₂ = 1 :=
    (spreadTriple_one_iff s₁ s₂).1 rightTriangle
  calc
    s₁ * (r₁ * R₂ + r₂ * R₁) =
        s₁ * (r₁ * R₂) + (s₁ * R₁) * r₂ := by ring1
    _ = s₁ * (r₁ * R₂) + r₁ * (s₂ * R₂) := by
      rw [triangleProportion]
    _ = (s₁ + s₂) * (r₁ * R₂) := by ring1
    _ = r₁ * R₂ := by rw [spreadSum, one_mul]

/-- Exercise 11.1 in the printed reciprocal form. -/
theorem exercise_11_1 [DecidableEq K]
    (r₁ r₂ s₁ s₂ R₁ R₂ : K)
    (r₁Nonzero : r₁ ≠ 0) (R₂Nonzero : R₂ ≠ 0)
    (rightTriangle : SpreadTriple s₁ s₂ 1)
    (triangleProportion :
      r₁ * (s₂ * R₂) = (s₁ * R₁) * r₂) :
    s₁ = (1 + (r₂ * R₁) / (r₁ * R₂))⁻¹ := by
  let denominator := r₁ * R₂
  let expression := 1 + (r₂ * R₁) / denominator
  have denominatorNonzero : denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero r₁Nonzero R₂Nonzero
  have cleared := exercise_11_1_cleared r₁ r₂ s₁ s₂ R₁ R₂
    rightTriangle triangleProportion
  have expressionProduct : s₁ * expression = 1 := by
    apply eq_of_mul_eq_mul_right denominatorNonzero
    calc
      (s₁ * expression) * denominator =
          s₁ * (denominator + ((r₂ * R₁) / denominator) *
            denominator) := by
        unfold expression
        ring1
      _ = s₁ * (denominator + r₂ * R₁) := by
        rw [RFAP.ExplicitField.div_mul_cancel _ denominatorNonzero]
      _ = denominator := by
        simpa only [denominator] using cleared
      _ = 1 * denominator := by ring1
  have oneNonzero : (1 : K) ≠ 0 := by
    intro oneZero
    apply denominatorNonzero
    calc
      denominator = denominator * 1 := by rw [mul_one]
      _ = denominator * 0 := by rw [oneZero]
      _ = 0 := by rw [mul_zero]
  have expressionNonzero : expression ≠ 0 := by
    intro expressionZero
    apply oneNonzero
    calc
      1 = s₁ * expression := expressionProduct.symm
      _ = 0 := by rw [expressionZero, mul_zero]
  apply eq_of_mul_eq_mul_right expressionNonzero
  calc
    s₁ * expression = 1 := expressionProduct
    _ = expression⁻¹ * expression := by
      rw [show expression⁻¹ * expression = expression * expression⁻¹ by
        ring1, RFAP.ExplicitField.mul_inv_cancel expression
          expressionNonzero]


/-- The first factorization in Example 11.1.  The hypotheses `4p=1` and
`64r=9` are the denominator-free forms of `p=1/4` and `r=9/64`. -/
private theorem example_11_1_first_factorization
    (p r m : K) (pValue : 4 * p = 1) (rValue : 64 * r = 9)
    (triple : QuadTriple r (r * p) (m * p)) :
    (64 * m - 9) * (64 * m - 81) = 0 := by
  have scaled := quadTriple_scale r (r * p) (m * p) 256 triple
  have firstValue : 256 * r = (36 : K) := by
    calc
      256 * r = 4 * (64 * r) := by ring1
      _ = 4 * 9 := by rw [rValue]
      _ = 36 := by ring1
  have secondValue : 256 * (r * p) = (9 : K) := by
    calc
      256 * (r * p) = (64 * r) * (4 * p) := by ring1
      _ = 9 * 1 := by rw [rValue, pValue]
      _ = 9 := by ring1
  have thirdValue : 256 * (m * p) = 64 * m := by
    calc
      256 * (m * p) = (64 * m) * (4 * p) := by ring1
      _ = 64 * m := by rw [pValue, mul_one]
  rw [firstValue, secondValue, thirdValue] at scaled
  unfold QuadTriple archimedesFunction at scaled
  calc
    (64 * m - 9) * (64 * m - 81) =
        -((36 + 9 + 64 * m) ^ 2 -
          2 * (36 ^ 2 + 9 ^ 2 + (64 * m) ^ 2)) := by ring1
    _ = 0 := by rw [scaled]; exact neg_zero

/-- The second factorization in Example 11.1. -/
private theorem example_11_1_second_factorization
    (p r n : K) (pValue : 4 * p = 1) (rValue : 64 * r = 9)
    (triple : QuadTriple p (r * p) (n * r)) :
    (36 * n - 25) * (36 * n - 121) = 0 := by
  have scaled := quadTriple_scale p (r * p) (n * r) 256 triple
  have firstValue : 256 * p = (64 : K) := by
    calc
      256 * p = 64 * (4 * p) := by ring1
      _ = 64 := by rw [pValue, mul_one]
  have secondValue : 256 * (r * p) = (9 : K) := by
    calc
      256 * (r * p) = (64 * r) * (4 * p) := by ring1
      _ = 9 * 1 := by rw [rValue, pValue]
      _ = 9 := by ring1
  have thirdValue : 256 * (n * r) = 36 * n := by
    calc
      256 * (n * r) = 4 * (64 * r) * n := by ring1
      _ = 4 * 9 * n := by rw [rValue]
      _ = 36 * n := by ring1
  rw [firstValue, secondValue, thirdValue] at scaled
  unfold QuadTriple archimedesFunction at scaled
  calc
    (36 * n - 25) * (36 * n - 121) =
        -((64 + 9 + 36 * n) ^ 2 -
          2 * (64 ^ 2 + 9 ^ 2 + (36 * n) ^ 2)) := by ring1
    _ = 0 := by rw [scaled]; exact neg_zero

/-- Example 11.1.  The two quad triples supplied by Two struts at
`p=1/4`, `r=9/64` give exactly the two printed factored equations. -/
theorem example_11_1
    (p r m n : K) (pValue : 4 * p = 1) (rValue : 64 * r = 9)
    (strutTriples :
      QuadTriple r (r * p) (m * p) ∧
        QuadTriple p (r * p) (n * r)) :
    (64 * m - 9) * (64 * m - 81) = 0 ∧
      (36 * n - 25) * (36 * n - 121) = 0 :=
  ⟨example_11_1_first_factorization p r m pValue rValue
      strutTriples.1,
    example_11_1_second_factorization p r n pValue rValue
      strutTriples.2⟩

private theorem equal_parameter_equation [DecidableEq K]
    (r x : K) (rNonzero : r ≠ 0)
    (triple : QuadTriple r (r * r) (x * r)) :
    (x - r - 1) ^ 2 = 4 * r := by
  have rSquareNonzero : r ^ 2 ≠ 0 := by
    rw [pow_two]
    exact RFAP.ExplicitField.mul_ne_zero rNonzero rNonzero
  have scaledDifference :
      r ^ 2 * ((x - r - 1) ^ 2 - 4 * r) = 0 := by
    calc
      r ^ 2 * ((x - r - 1) ^ 2 - 4 * r) =
          -archimedesFunction r (r * r) (x * r) := by
        unfold archimedesFunction
        ring1
      _ = 0 := by
        unfold QuadTriple at triple
        rw [triple]
        exact neg_zero
  have differenceZero : (x - r - 1) ^ 2 - 4 * r = 0 := by
    by_cases zero : (x - r - 1) ^ 2 - 4 * r = 0
    · exact zero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero rSquareNonzero zero)
          scaledDifference)
  exact sub_eq_zero.mp differenceZero

/-- Exercise 11.2.  If the two input ratios in Two struts agree, both output
parameters satisfy the same printed quadratic equation. -/
theorem exercise_11_2
    [DecidableEq K]
    (p r m n : K) (rNonzero : r ≠ 0) (equalRatios : p = r)
    (strutTriples :
      QuadTriple r (r * p) (m * p) ∧
        QuadTriple p (r * p) (n * r)) :
    (m - r - 1) ^ 2 = 4 * r ∧
      (n - r - 1) ^ 2 = 4 * r := by
  subst p
  exact ⟨equal_parameter_equation r m rNonzero strutTriples.1,
    equal_parameter_equation r n rNonzero strutTriples.2⟩

/-- Denominator-free core of Exercise 11.3.  The conclusion `4p=1` remains
meaningful even in characteristics where the printed quotient `1/4` does
not. -/
theorem exercise_11_3_cleared
    [DecidableEq K]
    (p r : K) (rNonzero : r ≠ 0)
    (triple : QuadTriple r (r * p) (r * p)) : 4 * p = 1 := by
  have rSquareNonzero : r ^ 2 ≠ 0 := by
    rw [pow_two]
    exact RFAP.ExplicitField.mul_ne_zero rNonzero rNonzero
  have scaledDifference : r ^ 2 * (4 * p - 1) = 0 := by
    calc
      r ^ 2 * (4 * p - 1) =
          archimedesFunction r (r * p) (r * p) := by
        unfold archimedesFunction
        ring1
      _ = 0 := triple
  have differenceZero : 4 * p - 1 = 0 := by
    by_cases zero : 4 * p - 1 = 0
    · exact zero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero rSquareNonzero zero)
          scaledDifference)
  exact sub_eq_zero.mp differenceZero

/-- Exercise 11.3 in the source's quotient notation. -/
theorem exercise_11_3
    [DecidableEq K]
    (p r : K) (rNonzero : r ≠ 0) (fourNonzero : (4 : K) ≠ 0)
    (triple : QuadTriple r (r * p) (r * p)) : p = 1 / 4 := by
  apply eq_of_mul_eq_mul_right fourNonzero
  calc
    p * 4 = 4 * p := by ring1
    _ = 1 := exercise_11_3_cleared p r rNonzero triple
    _ = (1 / 4) * 4 :=
      (RFAP.ExplicitField.div_mul_cancel 1 fourNonzero).symm

private theorem mul_div_cancel_right (value divisor : K)
    (divisorNonzero : divisor ≠ 0) :
    (value * divisor) / divisor = value := by
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    value * divisor * divisor⁻¹ =
        value * (divisor * divisor⁻¹) := by ring1
    _ = value := by
      rw [RFAP.ExplicitField.mul_inv_cancel divisor divisorNonzero, mul_one]

private theorem first_bisector_quadTriple
    (p r m s₁ s₂ s₃ : K) (s₃Nonzero : s₃ ≠ 0)
    (firstBisectorRatio : r * s₂ = s₃)
    (secondBisectorRatio : p * s₁ = s₃)
    (triple : QuadTriple r (r * p) (m * p)) :
    QuadTriple s₁ s₃ (m * s₂) := by
  have scaled := quadTriple_scale r (r * p) (m * p) (s₁ * s₂) triple
  have firstValue : (s₁ * s₂) * r = s₁ * s₃ := by
    calc
      (s₁ * s₂) * r = s₁ * (r * s₂) := by ring1
      _ = s₁ * s₃ := by rw [firstBisectorRatio]
  have secondValue : (s₁ * s₂) * (r * p) = s₃ * s₃ := by
    calc
      (s₁ * s₂) * (r * p) = (r * s₂) * (p * s₁) := by ring1
      _ = s₃ * s₃ := by rw [firstBisectorRatio, secondBisectorRatio]
  have thirdValue : (s₁ * s₂) * (m * p) = (m * s₂) * s₃ := by
    calc
      (s₁ * s₂) * (m * p) = (m * s₂) * (p * s₁) := by ring1
      _ = (m * s₂) * s₃ := by rw [secondBisectorRatio]
  rw [firstValue, secondValue, thirdValue] at scaled
  have normalized := quadTriple_normalize (s₁ * s₃) (s₃ * s₃)
    ((m * s₂) * s₃) s₃ scaled
  rw [mul_div_cancel_right s₁ s₃ s₃Nonzero,
    mul_div_cancel_right s₃ s₃ s₃Nonzero,
    mul_div_cancel_right (m * s₂) s₃ s₃Nonzero] at normalized
  exact normalized

private theorem second_bisector_quadTriple
    (p r n s₁ s₂ s₃ : K) (s₃Nonzero : s₃ ≠ 0)
    (firstBisectorRatio : r * s₂ = s₃)
    (secondBisectorRatio : p * s₁ = s₃)
    (triple : QuadTriple p (r * p) (n * r)) :
    QuadTriple s₂ s₃ (n * s₁) := by
  have scaled := quadTriple_scale p (r * p) (n * r) (s₁ * s₂) triple
  have firstValue : (s₁ * s₂) * p = s₂ * s₃ := by
    calc
      (s₁ * s₂) * p = s₂ * (p * s₁) := by ring1
      _ = s₂ * s₃ := by rw [secondBisectorRatio]
  have secondValue : (s₁ * s₂) * (r * p) = s₃ * s₃ := by
    calc
      (s₁ * s₂) * (r * p) = (r * s₂) * (p * s₁) := by ring1
      _ = s₃ * s₃ := by rw [firstBisectorRatio, secondBisectorRatio]
  have thirdValue : (s₁ * s₂) * (n * r) = (n * s₁) * s₃ := by
    calc
      (s₁ * s₂) * (n * r) = (n * s₁) * (r * s₂) := by ring1
      _ = (n * s₁) * s₃ := by rw [firstBisectorRatio]
  rw [firstValue, secondValue, thirdValue] at scaled
  have normalized := quadTriple_normalize (s₂ * s₃) (s₃ * s₃)
    ((n * s₁) * s₃) s₃ scaled
  rw [mul_div_cancel_right s₂ s₃ s₃Nonzero,
    mul_div_cancel_right s₃ s₃ s₃Nonzero,
    mul_div_cancel_right (n * s₁) s₃ s₃Nonzero] at normalized
  exact normalized

/-- Corrected Exercise 11.4, with both omitted square terms restored.  These
are the source equations after multiplication by `s₂²` and `s₁²`; the PDF
incorrectly omits `(m s₂)²` and `(n s₁)²` on the right. -/
theorem exercise_11_4_corrected
    (p r m n s₁ s₂ s₃ : K) (s₃Nonzero : s₃ ≠ 0)
    (firstBisectorRatio : r * s₂ = s₃)
    (secondBisectorRatio : p * s₁ = s₃)
    (strutTriples :
      QuadTriple r (r * p) (m * p) ∧
        QuadTriple p (r * p) (n * r)) :
    (m * s₂ + s₁ + s₃) ^ 2 =
        2 * ((m * s₂) ^ 2 + s₁ ^ 2 + s₃ ^ 2) ∧
      (n * s₁ + s₂ + s₃) ^ 2 =
        2 * ((n * s₁) ^ 2 + s₂ ^ 2 + s₃ ^ 2) := by
  have firstTriple := first_bisector_quadTriple p r m s₁ s₂ s₃
    s₃Nonzero firstBisectorRatio secondBisectorRatio strutTriples.1
  have secondTriple := second_bisector_quadTriple p r n s₁ s₂ s₃
    s₃Nonzero firstBisectorRatio secondBisectorRatio strutTriples.2
  constructor
  · unfold QuadTriple archimedesFunction at firstTriple
    exact sub_eq_zero.mp (by
      calc
        (m * s₂ + s₁ + s₃) ^ 2 -
            2 * ((m * s₂) ^ 2 + s₁ ^ 2 + s₃ ^ 2) =
          archimedesFunction s₁ s₃ (m * s₂) := by
            unfold archimedesFunction
            ring1
        _ = 0 := firstTriple)
  · unfold QuadTriple archimedesFunction at secondTriple
    exact sub_eq_zero.mp (by
      calc
        (n * s₁ + s₂ + s₃) ^ 2 -
            2 * ((n * s₁) ^ 2 + s₂ ^ 2 + s₃ ^ 2) =
          archimedesFunction s₂ s₃ (n * s₁) := by
            unfold archimedesFunction
            ring1
        _ = 0 := secondTriple)

/-- Exercise 11.5, strengthened to the exact geometric hypotheses used by the
proof.  A point on the non-null base of an isosceles triangle satisfies the
printed product identity. -/
theorem exercise_11_5 [DecidableEq K]
    (first second vertex point : Point K)
    (firstSecondDistinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0)
    (baseNonNull :
      ¬ (lineThrough first second firstSecondDistinct).IsNull)
    (pointOnBase :
      (lineThrough first second firstSecondDistinct).Contains point)
    (equalLegs :
      quadrance first vertex = quadrance second vertex) :
    (quadrance first vertex - quadrance vertex point) ^ 2 =
      quadrance first point * quadrance second point := by
  let firstPart := quadrance first point
  let secondPart := quadrance second point
  let vertexPart := quadrance vertex point
  let commonLeg := quadrance first vertex
  have stewartIdentity := stewart first second vertex point
    firstSecondDistinct pointOnBase
  rw [← equalLegs] at stewartIdentity
  have stewartFactored :
      (firstPart - secondPart) *
        (firstPart * secondPart - (commonLeg - vertexPart) ^ 2) = 0 := by
    calc
      (firstPart - secondPart) *
          (firstPart * secondPart - (commonLeg - vertexPart) ^ 2) =
        secondPart * (vertexPart + firstPart - commonLeg) ^ 2 -
          firstPart * (vertexPart + secondPart - commonLeg) ^ 2 := by
        unfold firstPart secondPart vertexPart commonLeg
        ring1
      _ = 0 := by
        rw [stewartIdentity]
        ring1
  by_cases unequalParts : firstPart = secondPart
  · have equalEndpointQuadrances :
        quadrance point first = quadrance point second := by
      calc
        quadrance point first = firstPart :=
          quadrance_symm point first
        _ = secondPart := unequalParts
        _ = quadrance point second :=
          (quadrance_symm point second).symm
    have pointIsMidpoint : point = midpoint first second :=
      midpoint_unique_of_equal_quadrance first second point
        firstSecondDistinct twoNonzero baseNonNull pointOnBase
        equalEndpointQuadrances
    have fourNonzero : (4 : K) ≠ 0 := by
      rw [show (4 : K) = 2 * 2 by ring1]
      exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    have endpointCleared : firstPart * 4 = quadrance first second := by
      calc
        firstPart * 4 =
            quadrance (midpoint first second) first * 4 := by
          unfold firstPart
          rw [pointIsMidpoint, quadrance_symm first (midpoint first second)]
        _ = (quadrance first second / 4) * 4 := by
          rw [midpoint_quadrance first second twoNonzero]
        _ = quadrance first second :=
          RFAP.ExplicitField.div_mul_cancel _ fourNonzero
    have vertexCleared :
        vertexPart * 4 =
          2 * commonLeg + 2 * commonLeg - quadrance first second := by
      calc
        vertexPart * 4 =
            quadrance (midpoint first second) vertex * 4 := by
          unfold vertexPart
          rw [pointIsMidpoint,
            quadrance_symm vertex (midpoint first second)]
        _ = 2 * quadrance first vertex +
            2 * quadrance second vertex - quadrance first second :=
          median_quadrance_cleared first second vertex twoNonzero
        _ = 2 * commonLeg + 2 * commonLeg - quadrance first second := by
          unfold commonLeg
          rw [← equalLegs]
    have legDifference : commonLeg - vertexPart = firstPart := by
      apply eq_of_mul_eq_mul_right fourNonzero
      calc
        (commonLeg - vertexPart) * 4 =
            4 * commonLeg - vertexPart * 4 := by ring1
        _ = quadrance first second := by
          rw [vertexCleared]
          ring1
        _ = firstPart * 4 := endpointCleared.symm
    change (commonLeg - vertexPart) ^ 2 = firstPart * secondPart
    rw [legDifference, ← unequalParts, pow_two]
  · have secondFactorZero :
        firstPart * secondPart - (commonLeg - vertexPart) ^ 2 = 0 := by
      by_cases zero :
          firstPart * secondPart - (commonLeg - vertexPart) ^ 2 = 0
      · exact zero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero
              (sub_ne_zero.mpr unequalParts) zero)
            stewartFactored)
    change (commonLeg - vertexPart) ^ 2 = firstPart * secondPart
    exact (sub_eq_zero.mp secondFactorZero).symm

/-- Denominator-free factorization behind Exercise 11.6. -/
theorem exercise_11_6_cleared
    (Q R₁ R₂ R₃ : K)
    (baseTriple : QuadTriple R₂ R₁ Q)
    (isoscelesProduct : (Q - R₃) ^ 2 = R₁ * R₂) :
    (Q - (2 * R₃ - R₁ - R₂)) *
      (3 * Q - (2 * R₃ + R₁ + R₂)) = 0 := by
  change archimedesFunction R₂ R₁ Q = 0 at baseTriple
  calc
    (Q - (2 * R₃ - R₁ - R₂)) *
        (3 * Q - (2 * R₃ + R₁ + R₂)) =
      archimedesFunction R₂ R₁ Q -
        4 * (R₁ * R₂ - (Q - R₃) ^ 2) := by
      unfold archimedesFunction
      ring1
    _ = 0 := by rw [baseTriple, isoscelesProduct]; ring1

/-- Exercise 11.6 in its two printed alternatives. -/
theorem exercise_11_6 [DecidableEq K]
    (Q R₁ R₂ R₃ : K) (threeNonzero : (3 : K) ≠ 0)
    (baseTriple : QuadTriple R₂ R₁ Q)
    (isoscelesProduct : (Q - R₃) ^ 2 = R₁ * R₂) :
    Q = 2 * R₃ - R₁ - R₂ ∨
      Q = (2 * R₃ + R₁ + R₂) / 3 := by
  have factored := exercise_11_6_cleared Q R₁ R₂ R₃ baseTriple
    isoscelesProduct
  by_cases firstFactorZero : Q - (2 * R₃ - R₁ - R₂) = 0
  · exact Or.inl (sub_eq_zero.mp firstFactorZero)
  · have secondFactorZero :
        3 * Q - (2 * R₃ + R₁ + R₂) = 0 := by
      by_cases zero : 3 * Q - (2 * R₃ + R₁ + R₂) = 0
      · exact zero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero firstFactorZero zero) factored)
    apply Or.inr
    apply eq_of_mul_eq_mul_right threeNonzero
    calc
      Q * 3 = 3 * Q := by ring1
      _ = 2 * R₃ + R₁ + R₂ := sub_eq_zero.mp secondFactorZero
      _ = ((2 * R₃ + R₁ + R₂) / 3) * 3 :=
        (RFAP.ExplicitField.div_mul_cancel _ threeNonzero).symm

/-- The geometric interface to Exercise 11.6: an equilateral triangle and a
displayed point on its non-null base supply both scalar premises above. -/
theorem exercise_11_6_geometric [Nontrivial K] [DecidableEq K]
    (first second vertex point : Point K)
    (firstSecondDistinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) (threeNonzero : (3 : K) ≠ 0)
    (baseNonNull :
      ¬ (lineThrough first second firstSecondDistinct).IsNull)
    (pointOnBase :
      (lineThrough first second firstSecondDistinct).Contains point)
    (firstLegEqualsBase :
      quadrance first vertex = quadrance first second)
    (equalLegs :
      quadrance first vertex = quadrance second vertex) :
    quadrance first second =
        2 * quadrance vertex point - quadrance first point -
          quadrance second point ∨
      quadrance first second =
        (2 * quadrance vertex point + quadrance first point +
          quadrance second point) / 3 := by
  have collinear : Collinear first second point :=
    ⟨lineThrough first second firstSecondDistinct,
      lineThrough_contains_first first second firstSecondDistinct,
      lineThrough_contains_second first second firstSecondDistinct,
      pointOnBase⟩
  have baseTriple :
      QuadTriple (quadrance second point) (quadrance first point)
        (quadrance first second) :=
    (triple_quad_formula first second point twoNonzero).2 collinear
  have isoscelesProduct := exercise_11_5 first second vertex point
    firstSecondDistinct twoNonzero baseNonNull pointOnBase equalLegs
  rw [firstLegEqualsBase] at isoscelesProduct
  exact exercise_11_6 (quadrance first second) (quadrance first point)
    (quadrance second point) (quadrance vertex point) threeNonzero
    baseTriple isoscelesProduct

/-! The `n`-gon extension in Exercise 11.9 is a theorem about displayed
finite lists.  `nextQuadrances` is the caller-supplied one-place cyclic
rotation of `quadrances`; keeping that rotation explicit avoids any hidden
enumeration or modular-index convention. -/

/-- Product of a displayed finite scalar list. -/
def finiteScalarProduct : List K → K
  | [] => 1
  | value :: remaining => value * finiteScalarProduct remaining

/-- Entrywise multiplication of two displayed finite lists. -/
def pointwiseScalarProduct : List K → List K → List K
  | left :: leftRemaining, right :: rightRemaining =>
      left * right :: pointwiseScalarProduct leftRemaining rightRemaining
  | _, _ => []

private theorem finiteScalarProduct_pointwise
    (left right : List K) (sameLength : left.length = right.length) :
    finiteScalarProduct (pointwiseScalarProduct left right) =
      finiteScalarProduct left * finiteScalarProduct right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil =>
          simp only [pointwiseScalarProduct, finiteScalarProduct]
          ring1
      | cons right rightRemaining =>
          simp only [List.length_nil, List.length_cons] at sameLength
          exact Nat.noConfusion sameLength
  | cons left leftRemaining inductionHypothesis =>
      cases right with
      | nil =>
          simp only [List.length_cons, List.length_nil] at sameLength
          exact Nat.noConfusion sameLength
      | cons right rightRemaining =>
          have remainingLength :
              leftRemaining.length = rightRemaining.length :=
            Nat.succ.inj sameLength
          simp only [pointwiseScalarProduct, finiteScalarProduct,
            inductionHypothesis rightRemaining remainingLength]
          ring1

/-- Exercise 11.9 for a general displayed finite polygon.  The list equality
is the finite family of cleared Spread-law equations
`rᵢNᵢ=Nᵢ₊₁pᵢ₊₁`; the second equality certifies that the supplied next-list is
a cyclic rearrangement at product level. -/
theorem exercise_11_9_polygon
    (rSpreads pSpreads quadrances nextQuadrances : List K)
    (rLength : rSpreads.length = quadrances.length)
    (pLength : nextQuadrances.length = pSpreads.length)
    (spreadLaws :
      pointwiseScalarProduct rSpreads quadrances =
        pointwiseScalarProduct nextQuadrances pSpreads)
    (cyclicQuadrances :
      finiteScalarProduct nextQuadrances =
        finiteScalarProduct quadrances)
    (quadranceProductNonzero : finiteScalarProduct quadrances ≠ 0) :
    finiteScalarProduct rSpreads = finiteScalarProduct pSpreads := by
  apply eq_of_mul_eq_mul_right quadranceProductNonzero
  calc
    finiteScalarProduct rSpreads * finiteScalarProduct quadrances =
        finiteScalarProduct
          (pointwiseScalarProduct rSpreads quadrances) :=
      (finiteScalarProduct_pointwise rSpreads quadrances rLength).symm
    _ = finiteScalarProduct
        (pointwiseScalarProduct nextQuadrances pSpreads) := by
      rw [spreadLaws]
    _ = finiteScalarProduct nextQuadrances *
        finiteScalarProduct pSpreads :=
      finiteScalarProduct_pointwise nextQuadrances pSpreads pLength
    _ = finiteScalarProduct pSpreads *
        finiteScalarProduct quadrances := by
      rw [cyclicQuadrances]
      ring1

/-- The quadrilateral displayed in Exercise 11.9. -/
theorem exercise_11_9_quadrilateral
    (r₁ r₂ r₃ r₄ p₁ p₂ p₃ p₄ N₁ N₂ N₃ N₄ : K)
    (N₁Nonzero : N₁ ≠ 0) (N₂Nonzero : N₂ ≠ 0)
    (N₃Nonzero : N₃ ≠ 0) (N₄Nonzero : N₄ ≠ 0)
    (firstRatio : r₁ * N₁ = N₂ * p₂)
    (secondRatio : r₂ * N₂ = N₃ * p₃)
    (thirdRatio : r₃ * N₃ = N₄ * p₄)
    (fourthRatio : r₄ * N₄ = N₁ * p₁) :
    r₁ * r₂ * r₃ * r₄ = p₁ * p₂ * p₃ * p₄ := by
  have quadranceProductNonzero :
      finiteScalarProduct [N₁, N₂, N₃, N₄] ≠ 0 := by
    simp only [finiteScalarProduct]
    exact RFAP.ExplicitField.mul_ne_zero N₁Nonzero
      (RFAP.ExplicitField.mul_ne_zero N₂Nonzero
        (RFAP.ExplicitField.mul_ne_zero N₃Nonzero
          (by simpa only [mul_one] using N₄Nonzero)))
  have finiteResult := exercise_11_9_polygon
    [r₁, r₂, r₃, r₄] [p₂, p₃, p₄, p₁]
    [N₁, N₂, N₃, N₄] [N₂, N₃, N₄, N₁]
    rfl rfl (by
      simp only [pointwiseScalarProduct]
      rw [firstRatio, secondRatio, thirdRatio, fourthRatio])
    (by simp only [finiteScalarProduct]; ring1)
    quadranceProductNonzero
  calc
    r₁ * r₂ * r₃ * r₄ =
        finiteScalarProduct [r₁, r₂, r₃, r₄] := by
      simp only [finiteScalarProduct]
      ring1
    _ = finiteScalarProduct [p₂, p₃, p₄, p₁] := finiteResult
    _ = p₁ * p₂ * p₃ * p₄ := by
      simp only [finiteScalarProduct]
      ring1

/-- Exercise 11.11, Menelaus part.  With null spreads allowed, the proof
retains their product instead of cancelling it. -/
theorem exercise_11_11_menelaus_relaxed
    (r₁ r₂ r₃ R₁ R₂ R₃ P₁ P₂ P₃ : K)
    (firstRatio : r₁ * P₁ = R₂ * r₂)
    (secondRatio : r₂ * P₂ = R₃ * r₃)
    (thirdRatio : r₃ * P₃ = R₁ * r₁) :
    (R₁ * R₂ * R₃ - P₁ * P₂ * P₃) * (r₁ * r₂ * r₃) = 0 := by
  have retained := menelaus_cleared r₁ r₂ r₃ R₁ R₂ R₃ P₁ P₂ P₃
    firstRatio secondRatio thirdRatio
  calc
    (R₁ * R₂ * R₃ - P₁ * P₂ * P₃) * (r₁ * r₂ * r₃) =
        (R₁ * R₂ * R₃) * (r₁ * r₂ * r₃) -
          (P₁ * P₂ * P₃) * (r₁ * r₂ * r₃) := by ring1
    _ = 0 := by rw [retained]; ring1

/-- Exercise 11.11, Ceva part.  Null side or cevian spreads leave the exact
common factor shown here; the ordinary concurrency product follows only when
that displayed factor is nonzero. -/
theorem exercise_11_11_ceva_relaxed
    (r₁ r₂ r₃ p₁ p₂ p₃ s₁ s₂ s₃ R₁ R₂ R₃ P₁ P₂ P₃ : K)
    (firstRatio : r₁ * (s₃ * P₁) = (s₂ * R₁) * p₁)
    (secondRatio : r₂ * (s₁ * P₂) = (s₃ * R₂) * p₂)
    (thirdRatio : r₃ * (s₂ * P₃) = (s₁ * R₃) * p₃)
    (alternateSpreads : r₁ * r₂ * r₃ = p₁ * p₂ * p₃) :
    (R₁ * R₂ * R₃ - P₁ * P₂ * P₃) *
      ((s₁ * s₂ * s₃) * (p₁ * p₂ * p₃)) = 0 := by
  have retained := ceva_cleared r₁ r₂ r₃ p₁ p₂ p₃ s₁ s₂ s₃
    R₁ R₂ R₃ P₁ P₂ P₃ firstRatio secondRatio thirdRatio
      alternateSpreads
  calc
    (R₁ * R₂ * R₃ - P₁ * P₂ * P₃) *
        ((s₁ * s₂ * s₃) * (p₁ * p₂ * p₃)) =
      (R₁ * R₂ * R₃) * ((s₁ * s₂ * s₃) * (p₁ * p₂ * p₃)) -
        (P₁ * P₂ * P₃) * ((s₁ * s₂ * s₃) *
          (p₁ * p₂ * p₃)) := by ring1
    _ = 0 := by rw [retained]; ring1

end DivineProportions
