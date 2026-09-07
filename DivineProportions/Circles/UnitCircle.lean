import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Circles.ProjectiveCircle

/-!
# Divine Proportions, §16.3: the unit circle

The source's map `[x,y] ↦ [2y-1,2x]` is stored as an executable point
transformation.  Its unit-circle equation is exactly four times the
projective-circle equation, so Theorem 108 follows from Theorem 107 with one
visible characteristic-two exclusion in the reverse direction.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

/-- The unit circle's displayed center. -/
def unitCircleCenter : Point K := ⟨0, 0⟩

/-- The unit circle `x²+y²=1`. -/
def unitCircle [Nontrivial K] : Conic K where
  d := 1
  e := 0
  f := 1
  a := 0
  b := 0
  c := -1
  quadratic_nonzero := Or.inl one_ne_zero

/-- The executable unit-circle point requested by parameter `λ`. -/
def unitCirclePoint (parameter : K) : Point K :=
  ⟨(1 - parameter ^ 2) / (1 + parameter ^ 2),
    (2 * parameter) / (1 + parameter ^ 2)⟩

/-- The one unit-circle point omitted by the rational parametrization. -/
def unitCircleExcludedPoint : Point K := ⟨-1, 0⟩

/-- The source's finite transform from the projective circle to the unit
circle. -/
def projectiveToUnit (point : Point K) : Point K :=
  ⟨2 * point.y - 1, 2 * point.x⟩

/-- Its explicit inverse when `2 ≠ 0`. -/
def unitToProjective (point : Point K) : Point K :=
  ⟨point.y / 2, (point.x + 1) / 2⟩

/-- The unit circle evaluates to its printed equation. -/
theorem unitCircle_evaluate [Nontrivial K] (point : Point K) :
    unitCircle.evaluate point = point.x ^ 2 + point.y ^ 2 - 1 := by
  unfold unitCircle evaluate
  ring1

/-- Incidence with the unit circle is the equation `x²+y²=1`. -/
theorem unitCircle_contains_iff [Nontrivial K] (point : Point K) :
    unitCircle.Contains point ↔ point.x ^ 2 + point.y ^ 2 - 1 = 0 := by
  unfold Contains
  rw [unitCircle_evaluate]

/-- The coefficient conic has the stated center and unit quadrance. -/
theorem unitCircle_isCirclePresentation [Nontrivial K] :
    unitCircle.IsCirclePresentation unitCircleCenter (1 : K) := by
  change (0 : K) = 0 ∧ (1 : K) = 1 ∧ (1 : K) ≠ 0 ∧
    0 = -2 * 1 * 0 ∧ 0 = -2 * 1 * 0 ∧
      -1 = 1 * (0 ^ 2 + 0 ^ 2 - 1)
  exact ⟨rfl, rfl, one_ne_zero, by ring1, by ring1, by ring1⟩

/-- The transformed unit equation is four times the projective equation. -/
theorem projectiveToUnit_equation [Nontrivial K] (point : Point K) :
    (projectiveToUnit point).x ^ 2 +
        (projectiveToUnit point).y ^ 2 - 1 =
      4 * (point.x ^ 2 + point.y ^ 2 - point.y) := by
  unfold projectiveToUnit
  ring1

/-- The finite transform sends every projective-circle point to the unit
circle. -/
theorem projectiveToUnit_contains [Nontrivial K]
    (point : Point K) (pointOnCircle : projectiveCircle.Contains point) :
    unitCircle.Contains (projectiveToUnit point) := by
  apply (unitCircle_contains_iff _).2
  calc
    (projectiveToUnit point).x ^ 2 +
        (projectiveToUnit point).y ^ 2 - 1 =
        4 * (point.x ^ 2 + point.y ^ 2 - point.y) :=
      projectiveToUnit_equation point
    _ = 0 := by
      rw [(projectiveCircle_contains_iff point).1 pointOnCircle]
      ring1

/-- Applying the inverse transform and then the forward transform recovers the
requested point. -/
theorem projectiveToUnit_unitToProjective
    (point : Point K) (twoNonzero : (2 : K) ≠ 0) :
    projectiveToUnit (unitToProjective point) = point := by
  have xCancel : ((point.x + 1) / 2) * 2 = point.x + 1 :=
    RFAP.ExplicitField.div_mul_cancel (point.x + 1) twoNonzero
  have yCancel : (point.y / 2) * 2 = point.y :=
    RFAP.ExplicitField.div_mul_cancel point.y twoNonzero
  apply Point.ext
  · change 2 * ((point.x + 1) / 2) - 1 = point.x
    calc
      2 * ((point.x + 1) / 2) - 1 =
          ((point.x + 1) / 2) * 2 - 1 := by ring1
      _ = point.x := by rw [xCancel]; ring1
  · change 2 * (point.y / 2) = point.y
    calc
      2 * (point.y / 2) = (point.y / 2) * 2 := by ring1
      _ = point.y := yCancel

private theorem eq_zero_of_mul_eq_zero_left
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have inverseCancel : factor⁻¹ * factor = (1 : K) := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = 1 * value := by ring1
    _ = (factor⁻¹ * factor) * value := by rw [inverseCancel]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero]; ring1

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

/-- A unit-circle point maps back to the projective circle outside
characteristic two. -/
theorem unitToProjective_contains [Nontrivial K]
    (point : Point K) (twoNonzero : (2 : K) ≠ 0)
    (pointOnCircle : unitCircle.Contains point) :
    projectiveCircle.Contains (unitToProjective point) := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero := RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    intro fourZero
    apply productNonzero
    calc
      (2 : K) * 2 = 4 := by ring1
      _ = 0 := fourZero
  let projectivePoint := unitToProjective point
  have recovered : projectiveToUnit projectivePoint = point :=
    projectiveToUnit_unitToProjective point twoNonzero
  have transformedEquation :
      (projectiveToUnit projectivePoint).x ^ 2 +
          (projectiveToUnit projectivePoint).y ^ 2 - 1 = 0 := by
    rw [recovered]
    exact (unitCircle_contains_iff point).1 pointOnCircle
  apply (projectiveCircle_contains_iff projectivePoint).2
  apply eq_zero_of_mul_eq_zero_left fourNonzero
  calc
    4 * (projectivePoint.x ^ 2 + projectivePoint.y ^ 2 -
        projectivePoint.y) =
        (projectiveToUnit projectivePoint).x ^ 2 +
          (projectiveToUnit projectivePoint).y ^ 2 - 1 :=
      (projectiveToUnit_equation projectivePoint).symm
    _ = 0 := transformedEquation

/-- The projective parametrization transforms into the printed unit-circle
parametrization. -/
theorem projectiveToUnit_projectiveCirclePoint
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    projectiveToUnit (projectiveCirclePoint parameter) =
      unitCirclePoint parameter := by
  let denominator := 1 + parameter ^ 2
  have denominatorNonzero : denominator ≠ 0 :=
    (projectiveParameter_denominator_ne_zero_iff parameter).2
      squareNotNegativeOne
  have oneCancel : (1 / denominator) * denominator = (1 : K) :=
    RFAP.ExplicitField.div_mul_cancel 1 denominatorNonzero
  apply Point.ext
  · change 2 * (1 / denominator) - 1 =
      (1 - parameter ^ 2) / denominator
    apply eq_of_mul_eq_mul_right denominatorNonzero
    calc
      (2 * (1 / denominator) - 1) * denominator =
          2 * ((1 / denominator) * denominator) - denominator := by ring1
      _ = 2 - denominator := by rw [oneCancel]; ring1
      _ = 1 - parameter ^ 2 := by unfold denominator; ring1
      _ = ((1 - parameter ^ 2) / denominator) * denominator :=
        (RFAP.ExplicitField.div_mul_cancel
          (1 - parameter ^ 2) denominatorNonzero).symm
  · change 2 * (parameter / denominator) =
      (2 * parameter) / denominator
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1

/-- Forward half of Theorem 108. -/
theorem unitCirclePoint_contains [Nontrivial K]
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    unitCircle.Contains (unitCirclePoint parameter) := by
  rw [← projectiveToUnit_projectiveCirclePoint parameter
    squareNotNegativeOne]
  exact projectiveToUnit_contains (projectiveCirclePoint parameter)
    (projectiveCirclePoint_contains parameter squareNotNegativeOne)

/-- Converse half of Theorem 108: every non-excluded unit-circle point
constructs its projective parameter. -/
theorem unitCirclePoint_exists [Nontrivial K] [DecidableEq K]
    (point : Point K) (twoNonzero : (2 : K) ≠ 0)
    (pointOnCircle : unitCircle.Contains point)
    (pointNotExcluded : point ≠ unitCircleExcludedPoint) :
    ∃ parameter : K,
      parameter ^ 2 ≠ -1 ∧ point = unitCirclePoint parameter := by
  let projectivePoint := unitToProjective point
  have projectivePointOnCircle :
      projectiveCircle.Contains projectivePoint :=
    unitToProjective_contains point twoNonzero pointOnCircle
  have recovered : projectiveToUnit projectivePoint = point :=
    projectiveToUnit_unitToProjective point twoNonzero
  have projectivePointNotOrigin :
      projectivePoint ≠ (⟨0, 0⟩ : Point K) := by
    intro projectivePointEqualsOrigin
    apply pointNotExcluded
    calc
      point = projectiveToUnit projectivePoint := recovered.symm
      _ = projectiveToUnit (⟨0, 0⟩ : Point K) := by
        rw [projectivePointEqualsOrigin]
      _ = unitCircleExcludedPoint := by
        unfold projectiveToUnit unitCircleExcludedPoint
        apply Point.ext <;> dsimp only <;> ring1
  rcases projectiveCirclePoint_exists projectivePoint
      projectivePointOnCircle projectivePointNotOrigin with
    ⟨parameter, squareNotNegativeOne, projectiveFormula⟩
  refine ⟨parameter, squareNotNegativeOne, ?_⟩
  calc
    point = projectiveToUnit projectivePoint := recovered.symm
    _ = projectiveToUnit (projectiveCirclePoint parameter) := by
      rw [projectiveFormula]
    _ = unitCirclePoint parameter :=
      projectiveToUnit_projectiveCirclePoint parameter squareNotNegativeOne

/-- Theorem 108 (Unit circle), packaged in both directions. -/
theorem unit_circle [Nontrivial K] [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    (∀ parameter : K, parameter ^ 2 ≠ -1 →
      unitCircle.Contains (unitCirclePoint parameter)) ∧
    (∀ point : Point K,
      unitCircle.Contains point → point ≠ unitCircleExcludedPoint →
        ∃ parameter : K,
          parameter ^ 2 ≠ -1 ∧ point = unitCirclePoint parameter) := by
  exact ⟨unitCirclePoint_contains,
    fun point pointOnCircle pointNotExcluded =>
      unitCirclePoint_exists point twoNonzero pointOnCircle pointNotExcluded⟩

/-- The four unit-circle points displayed immediately before Theorem 107. -/
theorem unitCircle_four_points [Nontrivial K] :
    unitCircle.Contains (⟨1, 0⟩ : Point K) ∧
      unitCircle.Contains (⟨-1, 0⟩ : Point K) ∧
      unitCircle.Contains (⟨0, 1⟩ : Point K) ∧
      unitCircle.Contains (⟨0, -1⟩ : Point K) := by
  repeat' apply And.intro
  all_goals
    apply (unitCircle_contains_iff _).2
    dsimp only
    ring1

end Conic

end DivineProportions
