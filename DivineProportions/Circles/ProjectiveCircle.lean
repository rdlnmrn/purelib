import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Conics.Circle

/-!
# Divine Proportions, §16.3: the projective circle

The projective circle is stored by its denominator-free equation
`x² + y² - y = 0`.  Its rational parametrization is executable for every
requested field element; the theorem carries the exact finite certificate
`λ² ≠ -1` needed to cancel its denominator.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

/-- The projective circle's displayed center `[0,1/2]`. -/
def projectiveCircleCenter : Point K := ⟨0, 1 / 2⟩

/-- The projective circle `x² + y² - y = 0`. -/
def projectiveCircle [Nontrivial K] : Conic K where
  d := 1
  e := 0
  f := 1
  a := 0
  b := -1
  c := 0
  quadratic_nonzero := Or.inl one_ne_zero

/-- The executable projective-circle point requested by a parameter. -/
def projectiveCirclePoint (parameter : K) : Point K :=
  ⟨parameter / (1 + parameter ^ 2), 1 / (1 + parameter ^ 2)⟩

/-- The parameter condition printed in Theorems 107 and 108 is exactly the
nonvanishing of their common denominator. -/
theorem projectiveParameter_denominator_ne_zero_iff (parameter : K) :
    1 + parameter ^ 2 ≠ 0 ↔ parameter ^ 2 ≠ -1 := by
  constructor
  · intro denominatorNonzero squareNegativeOne
    apply denominatorNonzero
    rw [squareNegativeOne]
    ring1
  · intro squareNotNegativeOne denominatorZero
    apply squareNotNegativeOne
    calc
      parameter ^ 2 = (1 + parameter ^ 2) - 1 := by ring1
      _ = -1 := by rw [denominatorZero]; ring1

/-- The projective circle evaluates to its printed equation. -/
theorem projectiveCircle_evaluate [Nontrivial K] (point : Point K) :
    projectiveCircle.evaluate point = point.x ^ 2 + point.y ^ 2 - point.y := by
  unfold projectiveCircle evaluate
  ring1

/-- Incidence with the projective circle is the printed polynomial equation. -/
theorem projectiveCircle_contains_iff [Nontrivial K] (point : Point K) :
    projectiveCircle.Contains point ↔
      point.x ^ 2 + point.y ^ 2 - point.y = 0 := by
  unfold Contains
  rw [projectiveCircle_evaluate]

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by ring1
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel]; ring1

/-- The coefficient conic really has center `[0,1/2]` and quadrance `1/4`. -/
theorem projectiveCircle_isCirclePresentation [Nontrivial K]
    (twoNonzero : (2 : K) ≠ 0) :
    projectiveCircle.IsCirclePresentation projectiveCircleCenter
      (1 / 4 : K) := by
  have twoCancel : (1 / 2 : K) * 2 = 1 :=
    RFAP.ExplicitField.div_mul_cancel (1 : K) twoNonzero
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero := RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    intro fourZero
    apply productNonzero
    calc
      (2 : K) * 2 = 4 := by ring1
      _ = 0 := fourZero
  have halfSquareTimesFour : (1 / 2 : K) ^ 2 * 4 = 1 := by
    calc
      (1 / 2 : K) ^ 2 * 4 = ((1 / 2 : K) * 2) ^ 2 := by ring1
      _ = 1 := by rw [twoCancel]; ring1
  have quarterTimesFour : (1 / 4 : K) * 4 = 1 :=
    RFAP.ExplicitField.div_mul_cancel (1 : K) fourNonzero
  have halfSquareEqualsQuarter : (1 / 2 : K) ^ 2 = 1 / 4 := by
    apply eq_of_mul_eq_mul_right fourNonzero
    calc
      (1 / 2 : K) ^ 2 * 4 = 1 := halfSquareTimesFour
      _ = (1 / 4 : K) * 4 := quarterTimesFour.symm
  change (0 : K) = 0 ∧ (1 : K) = 1 ∧ (1 : K) ≠ 0 ∧
    0 = -2 * 1 * 0 ∧
    -1 = -2 * 1 * (1 / 2) ∧
    0 = 1 * (0 ^ 2 + (1 / 2) ^ 2 - 1 / 4)
  refine ⟨rfl, rfl, one_ne_zero, ?_, ?_, ?_⟩
  · ring1
  · calc
      (-1 : K) = -((1 / 2 : K) * 2) := by rw [twoCancel]
      _ = -2 * 1 * (1 / 2) := by ring1
  · rw [halfSquareEqualsQuarter]
    ring1

/-- Forward half of Theorem 107: every admissible parameter produces a point
on the projective circle. -/
theorem projectiveCirclePoint_contains [Nontrivial K]
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    projectiveCircle.Contains (projectiveCirclePoint parameter) := by
  let denominator := 1 + parameter ^ 2
  have denominatorNonzero : denominator ≠ 0 :=
    (projectiveParameter_denominator_ne_zero_iff parameter).2
      squareNotNegativeOne
  have parameterCancel : (parameter / denominator) * denominator = parameter :=
    RFAP.ExplicitField.div_mul_cancel parameter denominatorNonzero
  have oneCancel : (1 / denominator) * denominator = 1 :=
    RFAP.ExplicitField.div_mul_cancel 1 denominatorNonzero
  have denominatorSquareNonzero : denominator * denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero denominatorNonzero denominatorNonzero
  apply (projectiveCircle_contains_iff
    (projectiveCirclePoint parameter)).2
  change (parameter / denominator) ^ 2 + (1 / denominator) ^ 2 -
      1 / denominator = 0
  let equation := (parameter / denominator) ^ 2 +
    (1 / denominator) ^ 2 - 1 / denominator
  have scaledEquation : equation * (denominator * denominator) = 0 := by
    calc
      equation * (denominator * denominator) =
          ((parameter / denominator) * denominator) ^ 2 +
            ((1 / denominator) * denominator) ^ 2 -
            ((1 / denominator) * denominator) * denominator := by
        unfold equation
        ring1
      _ = parameter ^ 2 + 1 - denominator := by
        rw [parameterCancel, oneCancel]
        ring1
      _ = 0 := by unfold denominator; ring1
  apply eq_of_mul_eq_mul_right denominatorSquareNonzero
  calc
    equation * (denominator * denominator) = 0 := scaledEquation
    _ = 0 * (denominator * denominator) := by ring1

/-- Converse half of Theorem 107: every non-origin projective-circle point
constructs its unique displayed parameter `x/y`. -/
theorem projectiveCirclePoint_exists [Nontrivial K] [DecidableEq K]
    (point : Point K) (pointOnCircle : projectiveCircle.Contains point)
    (pointNotOrigin : point ≠ (⟨0, 0⟩ : Point K)) :
    ∃ parameter : K,
      parameter ^ 2 ≠ -1 ∧ point = projectiveCirclePoint parameter := by
  have circleEquation : point.x ^ 2 + point.y ^ 2 - point.y = 0 :=
    (projectiveCircle_contains_iff point).1 pointOnCircle
  have yNonzero : point.y ≠ 0 := by
    intro yZero
    have xSquareZero : point.x ^ 2 = 0 := by
      calc
        point.x ^ 2 = point.x ^ 2 + point.y ^ 2 - point.y := by
          rw [yZero]
          ring1
        _ = 0 := circleEquation
    have xZero : point.x = 0 := by
      by_cases xZero : point.x = 0
      · exact xZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero xZero xZero)
            (by simpa [pow_two] using xSquareZero))
    apply pointNotOrigin
    apply Point.ext
    · exact xZero
    · exact yZero
  let parameter := point.x / point.y
  have parameterTimesY : parameter * point.y = point.x := by
    unfold parameter
    exact RFAP.ExplicitField.div_mul_cancel point.x yNonzero
  have factoredEquation :
      point.y * (point.y + point.y * parameter ^ 2 - 1) = 0 := by
    calc
      point.y * (point.y + point.y * parameter ^ 2 - 1) =
          (parameter * point.y) ^ 2 + point.y ^ 2 - point.y := by ring1
      _ = point.x ^ 2 + point.y ^ 2 - point.y := by
        rw [parameterTimesY]
      _ = 0 := circleEquation
  have secondFactorZero : point.y + point.y * parameter ^ 2 - 1 = 0 := by
    by_cases factorZero : point.y + point.y * parameter ^ 2 - 1 = 0
    · exact factorZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero yNonzero factorZero) factoredEquation)
  have denominatorProduct : point.y * (1 + parameter ^ 2) = 1 := by
    calc
      point.y * (1 + parameter ^ 2) =
          (point.y + point.y * parameter ^ 2 - 1) + 1 := by ring1
      _ = 1 := by rw [secondFactorZero]; ring1
  have denominatorNonzero : 1 + parameter ^ 2 ≠ 0 := by
    intro denominatorZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = point.y * (1 + parameter ^ 2) := denominatorProduct.symm
      _ = 0 := by rw [denominatorZero]; ring1
  have yFormula : point.y = 1 / (1 + parameter ^ 2) := by
    apply eq_of_mul_eq_mul_right denominatorNonzero
    calc
      point.y * (1 + parameter ^ 2) = 1 := denominatorProduct
      _ = (1 / (1 + parameter ^ 2)) * (1 + parameter ^ 2) :=
        (RFAP.ExplicitField.div_mul_cancel 1 denominatorNonzero).symm
  have xFormula : point.x = parameter / (1 + parameter ^ 2) := by
    calc
      point.x = parameter * point.y := parameterTimesY.symm
      _ = parameter * (1 / (1 + parameter ^ 2)) := by rw [yFormula]
      _ = parameter / (1 + parameter ^ 2) := by
        rw [RFAP.ExplicitField.div_eq_mul_inv,
          RFAP.ExplicitField.div_eq_mul_inv]
        ring1
  refine ⟨parameter,
    (projectiveParameter_denominator_ne_zero_iff parameter).1
      denominatorNonzero, ?_⟩
  apply Point.ext
  · exact xFormula
  · exact yFormula

/-- Theorem 107 (Projective circle), packaged in both directions. -/
theorem projective_circle [Nontrivial K] [DecidableEq K] :
    (∀ parameter : K, parameter ^ 2 ≠ -1 →
      projectiveCircle.Contains (projectiveCirclePoint parameter)) ∧
    (∀ point : Point K,
      projectiveCircle.Contains point → point ≠ (⟨0, 0⟩ : Point K) →
        ∃ parameter : K,
          parameter ^ 2 ≠ -1 ∧
            point = projectiveCirclePoint parameter) := by
  exact ⟨projectiveCirclePoint_contains, projectiveCirclePoint_exists⟩

/-- The four projective-circle points displayed immediately before Theorem
107 in the source. -/
theorem projectiveCircle_four_points [Nontrivial K]
    (twoNonzero : (2 : K) ≠ 0) :
    projectiveCircle.Contains (⟨0, 0⟩ : Point K) ∧
      projectiveCircle.Contains (⟨0, 1⟩ : Point K) ∧
      projectiveCircle.Contains (⟨1 / 2, 1 / 2⟩ : Point K) ∧
      projectiveCircle.Contains (⟨-(1 / 2), 1 / 2⟩ : Point K) := by
  have twoCancel : (1 / 2 : K) * 2 = 1 :=
    RFAP.ExplicitField.div_mul_cancel 1 twoNonzero
  repeat' apply And.intro
  all_goals
    apply (projectiveCircle_contains_iff _).2
    dsimp only
    try ring1
  · calc
      (1 / 2 : K) ^ 2 + (1 / 2) ^ 2 - 1 / 2 =
          (1 / 2) * ((1 / 2) * 2 - 1) := by ring1
      _ = 0 := by rw [twoCancel]; ring1
  · calc
      (-(1 / 2 : K)) ^ 2 + (1 / 2) ^ 2 - 1 / 2 =
          (1 / 2) * ((1 / 2) * 2 - 1) := by ring1
      _ = 0 := by rw [twoCancel]; ring1

end Conic

end DivineProportions
