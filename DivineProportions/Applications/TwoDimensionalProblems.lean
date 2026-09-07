import DivineProportions.Proportions.TwoStruts
import DivineProportions.Quadrilaterals.FourPoint
import DivineProportions.Trigonometry.TriangleRatios
import DivineProportions.Trigonometry.TripleSpread
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Chapter 21: two-dimensional problems

The applications are separated into their finite metric identities and the
geometric incidence arguments that supply those identities.  Denominators are
always accompanied by explicit nonzero certificates.
-/

namespace DivineProportions
namespace TwoDimensionalProblems

variable {K : Type*} [RFAP.ExplicitField K]

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

private theorem cross_mul_of_div_eq_div
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (ratiosEqual :
      leftNumerator / leftDenominator =
        rightNumerator / rightDenominator) :
    leftNumerator * rightDenominator =
      rightNumerator * leftDenominator := by
  calc
    leftNumerator * rightDenominator =
        (leftNumerator / leftDenominator * leftDenominator) *
          rightDenominator := by
            rw [RFAP.ExplicitField.div_mul_cancel leftNumerator leftNonzero]
    _ = (rightNumerator / rightDenominator * leftDenominator) *
        rightDenominator := by rw [ratiosEqual]
    _ = (rightNumerator / rightDenominator * rightDenominator) *
        leftDenominator := by ring1
    _ = rightNumerator * leftDenominator := by
      rw [RFAP.ExplicitField.div_mul_cancel rightNumerator rightNonzero]

private theorem perpendicular_of_parallel_left_direct [DecidableEq K]
    (source target other : Line K) (parallel : source.Parallel target)
    (sourcePerpendicular : source.Perpendicular other) :
    target.Perpendicular other := by
  rcases direction_scale_of_parallel source target parallel with
    ⟨scale, _scaleNonzero, targetA, targetB⟩
  unfold Line.Perpendicular at sourcePerpendicular ⊢
  rw [targetA, targetB]
  calc
    scale * source.a * other.a + scale * source.b * other.b =
        scale * (source.a * other.a + source.b * other.b) := by ring1
    _ = 0 := by rw [sourcePerpendicular]; ring1

private theorem parallel_pair_through_common_line [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (common : Line K)
    (containsFirst : common.Contains first)
    (containsSecond : common.Contains second)
    (containsThird : common.Contains third) :
    (lineThrough first second firstSecondDistinct).Parallel
      (lineThrough first third firstThirdDistinct) := by
  have firstEquivalent := lineThrough_unique first second
    firstSecondDistinct common containsFirst containsSecond
  have secondEquivalent := lineThrough_unique first third
    firstThirdDistinct common containsFirst containsThird
  exact line_parallel_trans
    (line_parallel_of_equivalent firstEquivalent)
    (Line.parallel_symm (line_parallel_of_equivalent secondEquivalent))

/-- Problem 4, finite algebraic core.  Equations (21.1) and (21.2) say,
without division, that `P₁Q₁=P₂Q₂=P₃Q₃`.  Normalizing the collinear
quad triple by `P₂` and using those two twist-ratio identities proves that
the three reciprocal altitude quadrances form a quad triple. -/
theorem problem_4_from_twist_relations [DecidableEq K]
    (p₁ p₂ p₃ q₁ q₂ q₃ : K)
    (p₂Nonzero : p₂ ≠ 0)
    (q₁Nonzero : q₁ ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (q₃Nonzero : q₃ ≠ 0)
    (baseQuadTriple : QuadTriple p₁ p₂ p₃)
    (firstTwistRelation : p₁ * q₁ = p₂ * q₂)
    (secondTwistRelation : p₃ * q₃ = p₂ * q₂) :
    QuadTriple (1 / q₁) (1 / q₂) (1 / q₃) := by
  have firstRatio : p₁ / p₂ = q₂ / q₁ :=
    div_eq_div_of_cross_mul p₂Nonzero q₁Nonzero (by
      calc
        p₁ * q₁ = p₂ * q₂ := firstTwistRelation
        _ = q₂ * p₂ := by ring1)
  have thirdRatio : p₃ / p₂ = q₂ / q₃ :=
    div_eq_div_of_cross_mul p₂Nonzero q₃Nonzero (by
      calc
        p₃ * q₃ = p₂ * q₂ := secondTwistRelation
        _ = q₂ * p₂ := by ring1)
  have middleRatio : p₂ / p₂ = (1 : K) := by
    calc
      p₂ / p₂ = (1 / p₂) * p₂ := by
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        ring1
      _ = 1 := RFAP.ExplicitField.div_mul_cancel 1 p₂Nonzero
  have normalized := quadTriple_normalize p₁ p₂ p₃ p₂ baseQuadTriple
  rw [firstRatio, middleRatio, thirdRatio] at normalized
  have reciprocalTriple :=
    quadTriple_normalize (q₂ / q₁) 1 (q₂ / q₃) q₂ normalized
  have q₂Cancel : q₂ * q₂⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel q₂ q₂Nonzero
  have firstCoordinate : (q₂ / q₁) / q₂ = 1 / q₁ := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      q₂ * q₁⁻¹ * q₂⁻¹ = (q₂ * q₂⁻¹) * q₁⁻¹ := by ring1
      _ = q₁⁻¹ := by rw [q₂Cancel, one_mul]
      _ = 1 * q₁⁻¹ := by rw [one_mul]
  have thirdCoordinate : (q₂ / q₃) / q₂ = 1 / q₃ := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      q₂ * q₃⁻¹ * q₂⁻¹ = (q₂ * q₂⁻¹) * q₃⁻¹ := by ring1
      _ = q₃⁻¹ := by rw [q₂Cancel, one_mul]
      _ = 1 * q₃⁻¹ := by rw [one_mul]
  rw [firstCoordinate, thirdCoordinate] at reciprocalTriple
  exact reciprocalTriple

/-- Problem 4, geometric form.  The displayed lines are the three finite line
witnesses in the source: the base line and the two transversal lines through
`B₁,B₂,A₃` and `A₁,B₂,B₃`.  The non-perpendicular and nonzero premises are
exactly the denominator conditions in the two applications of the Twist ratio
theorem and in the final reciprocal statement. -/
theorem problem_4 [Nontrivial K] [DecidableEq K]
    (a₁ a₂ a₃ b₁ b₂ b₃ : Point K)
    (base crossAtA₃ crossAtA₁ : Line K)
    (twoNonzero : (2 : K) ≠ 0)
    (a₁a₂Distinct : a₁ ≠ a₂) (a₁a₃Distinct : a₁ ≠ a₃)
    (a₂a₃Distinct : a₂ ≠ a₃)
    (a₁b₁Distinct : a₁ ≠ b₁) (a₂b₂Distinct : a₂ ≠ b₂)
    (a₃b₃Distinct : a₃ ≠ b₃)
    (a₃b₁Distinct : a₃ ≠ b₁) (a₃b₂Distinct : a₃ ≠ b₂)
    (a₁b₂Distinct : a₁ ≠ b₂) (a₁b₃Distinct : a₁ ≠ b₃)
    (baseContainsA₁ : base.Contains a₁)
    (baseContainsA₂ : base.Contains a₂)
    (baseContainsA₃ : base.Contains a₃)
    (crossAtA₃ContainsA₃ : crossAtA₃.Contains a₃)
    (crossAtA₃ContainsB₁ : crossAtA₃.Contains b₁)
    (crossAtA₃ContainsB₂ : crossAtA₃.Contains b₂)
    (crossAtA₁ContainsA₁ : crossAtA₁.Contains a₁)
    (crossAtA₁ContainsB₂ : crossAtA₁.Contains b₂)
    (crossAtA₁ContainsB₃ : crossAtA₁.Contains b₃)
    (firstAltitude :
      base.Perpendicular
        (lineThrough b₁ a₁ a₁b₁Distinct.symm))
    (secondAltitude :
      base.Perpendicular
        (lineThrough b₂ a₂ a₂b₂Distinct.symm))
    (thirdAltitude :
      base.Perpendicular
        (lineThrough b₃ a₃ a₃b₃Distinct.symm))
    (firstTwistAtA₃Defined :
      ¬ (lineThrough a₃ b₂ a₃b₂Distinct).Perpendicular
          (lineThrough a₃ a₂ a₂a₃Distinct.symm))
    (firstTwistAtA₃ComparisonDefined :
      ¬ (lineThrough a₃ b₁ a₃b₁Distinct).Perpendicular
          (lineThrough a₃ a₁ a₁a₃Distinct.symm))
    (secondTwistAtA₁Defined :
      ¬ (lineThrough a₁ b₂ a₁b₂Distinct).Perpendicular
          (lineThrough a₁ a₂ a₁a₂Distinct))
    (secondTwistAtA₁ComparisonDefined :
      ¬ (lineThrough a₁ b₃ a₁b₃Distinct).Perpendicular
          (lineThrough a₁ a₃ a₁a₃Distinct))
    (p₁Nonzero : quadrance a₂ a₃ ≠ 0)
    (p₂Nonzero : quadrance a₁ a₃ ≠ 0)
    (p₃Nonzero : quadrance a₁ a₂ ≠ 0)
    (q₁Nonzero : quadrance a₁ b₁ ≠ 0)
    (q₂Nonzero : quadrance a₂ b₂ ≠ 0)
    (q₃Nonzero : quadrance a₃ b₃ ≠ 0) :
    QuadTriple (1 / quadrance a₁ b₁) (1 / quadrance a₂ b₂)
      (1 / quadrance a₃ b₃) := by
  let base₃₂ := lineThrough a₃ a₂ a₂a₃Distinct.symm
  let base₃₁ := lineThrough a₃ a₁ a₁a₃Distinct.symm
  let base₁₂ := lineThrough a₁ a₂ a₁a₂Distinct
  let base₁₃ := lineThrough a₁ a₃ a₁a₃Distinct
  let altitude₁ := lineThrough b₁ a₁ a₁b₁Distinct.symm
  let altitude₂ := lineThrough b₂ a₂ a₂b₂Distinct.symm
  let altitude₃ := lineThrough b₃ a₃ a₃b₃Distinct.symm
  let cross₃₂ := lineThrough a₃ b₂ a₃b₂Distinct
  let cross₃₁ := lineThrough a₃ b₁ a₃b₁Distinct
  let cross₁₂ := lineThrough a₁ b₂ a₁b₂Distinct
  let cross₁₃ := lineThrough a₁ b₃ a₁b₃Distinct
  have base₃₂Parallel : base₃₂.Parallel base :=
    line_parallel_of_equivalent
      (lineThrough_unique a₃ a₂ a₂a₃Distinct.symm base
        baseContainsA₃ baseContainsA₂)
  have base₃₁Parallel : base₃₁.Parallel base :=
    line_parallel_of_equivalent
      (lineThrough_unique a₃ a₁ a₁a₃Distinct.symm base
        baseContainsA₃ baseContainsA₁)
  have base₁₂Parallel : base₁₂.Parallel base :=
    line_parallel_of_equivalent
      (lineThrough_unique a₁ a₂ a₁a₂Distinct base
        baseContainsA₁ baseContainsA₂)
  have base₁₃Parallel : base₁₃.Parallel base :=
    line_parallel_of_equivalent
      (lineThrough_unique a₁ a₃ a₁a₃Distinct base
        baseContainsA₁ baseContainsA₃)
  have rightAtA₂FromA₃ : base₃₂.Perpendicular altitude₂ :=
    perpendicular_of_parallel_left_direct base base₃₂ altitude₂
      (Line.parallel_symm base₃₂Parallel) secondAltitude
  have rightAtA₁FromA₃ : base₃₁.Perpendicular altitude₁ :=
    perpendicular_of_parallel_left_direct base base₃₁ altitude₁
      (Line.parallel_symm base₃₁Parallel) firstAltitude
  have rightAtA₂FromA₁ : base₁₂.Perpendicular altitude₂ :=
    perpendicular_of_parallel_left_direct base base₁₂ altitude₂
      (Line.parallel_symm base₁₂Parallel) secondAltitude
  have rightAtA₃FromA₁ : base₁₃.Perpendicular altitude₃ :=
    perpendicular_of_parallel_left_direct base base₁₃ altitude₃
      (Line.parallel_symm base₁₃Parallel) thirdAltitude
  have crossAtA₃Parallel : cross₃₂.Parallel cross₃₁ :=
    parallel_pair_through_common_line a₃ b₂ b₁ a₃b₂Distinct
      a₃b₁Distinct crossAtA₃ crossAtA₃ContainsA₃
      crossAtA₃ContainsB₂ crossAtA₃ContainsB₁
  have baseAtA₃Parallel : base₃₂.Parallel base₃₁ :=
    line_parallel_trans base₃₂Parallel (Line.parallel_symm base₃₁Parallel)
  have crossAtA₁Parallel : cross₁₂.Parallel cross₁₃ :=
    parallel_pair_through_common_line a₁ b₂ b₃ a₁b₂Distinct
      a₁b₃Distinct crossAtA₁ crossAtA₁ContainsA₁
      crossAtA₁ContainsB₂ crossAtA₁ContainsB₃
  have baseAtA₁Parallel : base₁₂.Parallel base₁₃ :=
    line_parallel_trans base₁₂Parallel (Line.parallel_symm base₁₃Parallel)
  have firstTwistRatio := twist_ratio a₃ b₂ a₂ a₃b₂Distinct
    a₂a₃Distinct.symm a₂b₂Distinct.symm
    (by simpa only [quadrance_symm] using p₁Nonzero)
    rightAtA₂FromA₃ firstTwistAtA₃Defined
  have firstComparisonRatio := twist_ratio a₃ b₁ a₁ a₃b₁Distinct
    a₁a₃Distinct.symm a₁b₁Distinct.symm
    (by simpa only [quadrance_symm] using p₂Nonzero)
    rightAtA₁FromA₃ firstTwistAtA₃ComparisonDefined
  have firstTwistsEqual := twist_eq_of_parallel_pairs
    cross₃₂ base₃₂ cross₃₁ base₃₁ firstTwistAtA₃Defined
      firstTwistAtA₃ComparisonDefined crossAtA₃Parallel baseAtA₃Parallel
  have firstRatiosEqual :
      quadrance a₂ b₂ / quadrance a₂ a₃ =
        quadrance a₁ b₁ / quadrance a₁ a₃ := by
    calc
      quadrance a₂ b₂ / quadrance a₂ a₃ =
          twist cross₃₂ base₃₂ firstTwistAtA₃Defined := by
            rw [firstTwistRatio]
            simp only [quadrance_symm]
      _ = twist cross₃₁ base₃₁ firstTwistAtA₃ComparisonDefined :=
        firstTwistsEqual
      _ = quadrance a₁ b₁ / quadrance a₁ a₃ := by
        rw [firstComparisonRatio]
        simp only [quadrance_symm]
  have secondTwistRatio := twist_ratio a₁ b₂ a₂ a₁b₂Distinct
    a₁a₂Distinct a₂b₂Distinct.symm p₃Nonzero
    rightAtA₂FromA₁ secondTwistAtA₁Defined
  have secondComparisonRatio := twist_ratio a₁ b₃ a₃ a₁b₃Distinct
    a₁a₃Distinct a₃b₃Distinct.symm p₂Nonzero
    rightAtA₃FromA₁ secondTwistAtA₁ComparisonDefined
  have secondTwistsEqual := twist_eq_of_parallel_pairs
    cross₁₂ base₁₂ cross₁₃ base₁₃ secondTwistAtA₁Defined
      secondTwistAtA₁ComparisonDefined crossAtA₁Parallel baseAtA₁Parallel
  have secondRatiosEqual :
      quadrance a₂ b₂ / quadrance a₁ a₂ =
        quadrance a₃ b₃ / quadrance a₁ a₃ := by
    calc
      quadrance a₂ b₂ / quadrance a₁ a₂ =
          twist cross₁₂ base₁₂ secondTwistAtA₁Defined := by
            rw [secondTwistRatio]
            simp only [quadrance_symm]
      _ = twist cross₁₃ base₁₃ secondTwistAtA₁ComparisonDefined :=
        secondTwistsEqual
      _ = quadrance a₃ b₃ / quadrance a₁ a₃ := by
        rw [secondComparisonRatio]
        simp only [quadrance_symm]
  have firstCrossRelation := cross_mul_of_div_eq_div
    (by simpa only [quadrance_symm] using p₁Nonzero)
    (by simpa only [quadrance_symm] using p₂Nonzero)
    firstRatiosEqual
  have secondCrossRelation := cross_mul_of_div_eq_div p₃Nonzero p₂Nonzero
    secondRatiosEqual
  have baseQuadTriple :
      QuadTriple (quadrance a₂ a₃) (quadrance a₁ a₃)
        (quadrance a₁ a₂) := by
    unfold QuadTriple
    apply (triple_quad_formula a₁ a₂ a₃ twoNonzero).2
    exact ⟨base, baseContainsA₁, baseContainsA₂, baseContainsA₃⟩
  apply problem_4_from_twist_relations
    (quadrance a₂ a₃) (quadrance a₁ a₃) (quadrance a₁ a₂)
    (quadrance a₁ b₁) (quadrance a₂ b₂) (quadrance a₃ b₃)
    p₂Nonzero q₁Nonzero q₂Nonzero q₃Nonzero baseQuadTriple
  · calc
      quadrance a₂ a₃ * quadrance a₁ b₁ =
          quadrance a₁ b₁ * quadrance a₂ a₃ := by ring1
      _ = quadrance a₂ b₂ * quadrance a₁ a₃ := firstCrossRelation.symm
      _ = quadrance a₁ a₃ * quadrance a₂ b₂ := by ring1
  · calc
      quadrance a₁ a₂ * quadrance a₃ b₃ =
          quadrance a₃ b₃ * quadrance a₁ a₂ := by ring1
      _ = quadrance a₂ b₂ * quadrance a₁ a₃ := secondCrossRelation.symm
      _ = quadrance a₁ a₃ * quadrance a₂ b₂ := by ring1

/-! ## Problem 5: overlapping triangles -/

/-- The book's third spread, represented by its coefficient pair over the
common denominator `950625`: `(487568 + 31584√154)/950625`. -/
def problem5ThirdSpreadNumerator (root : K) : K :=
  487568 + 31584 * root

/-- The coefficient pair for `Q(A,E)` over the common denominator `525625`. -/
def problem5QuadranceAENumerator (root : K) : K :=
  34556382 - 2238516 * root

/-- The coefficient pair for `Q(B,E)` over the common denominator `525625`. -/
def problem5QuadranceBENumerator (root : K) : K :=
  56649307 - 3669666 * root

/-- The coefficient pair for `Q(C,E)` over the common denominator `525625`. -/
def problem5QuadranceCENumerator (root : K) : K :=
  111662307 - 7758666 * root

/-- The coefficient pair for `Q(D,E)` over the common denominator `525625`. -/
def problem5QuadranceDENumerator (root : K) : K :=
  18789082 + 1476384 * root

/-- The selected third spread
`487568/950625 + (10528/316875)√154`. -/
def problem5ThirdSpread (root : K) : K :=
  problem5ThirdSpreadNumerator root / 950625

/-- The book's exact value of `Q(A,E)`. -/
def problem5QuadranceAE (root : K) : K :=
  problem5QuadranceAENumerator root / 525625

/-- The book's exact value of `Q(B,E)`. -/
def problem5QuadranceBE (root : K) : K :=
  problem5QuadranceBENumerator root / 525625

/-- The book's exact value of `Q(C,E)`. -/
def problem5QuadranceCE (root : K) : K :=
  problem5QuadranceCENumerator root / 525625

/-- The book's exact value of `Q(D,E)`. -/
def problem5QuadranceDE (root : K) : K :=
  problem5QuadranceDENumerator root / 525625

/-- Each displayed quotient has exactly the coefficient numerator recorded
above.  These equations make the two finite denominator boundaries visible. -/
theorem problem_5_value_definitions
    (root : K) (spreadDenominatorNonzero : (950625 : K) ≠ 0)
    (quadranceDenominatorNonzero : (525625 : K) ≠ 0) :
    problem5ThirdSpread root * 950625 =
        problem5ThirdSpreadNumerator root ∧
      problem5QuadranceAE root * 525625 =
        problem5QuadranceAENumerator root ∧
      problem5QuadranceBE root * 525625 =
        problem5QuadranceBENumerator root ∧
      problem5QuadranceCE root * 525625 =
        problem5QuadranceCENumerator root ∧
      problem5QuadranceDE root * 525625 =
        problem5QuadranceDENumerator root := by
  unfold problem5ThirdSpread problem5QuadranceAE problem5QuadranceBE
    problem5QuadranceCE problem5QuadranceDE
  exact ⟨RFAP.ExplicitField.div_mul_cancel _ spreadDenominatorNonzero,
    RFAP.ExplicitField.div_mul_cancel _ quadranceDenominatorNonzero,
    RFAP.ExplicitField.div_mul_cancel _ quadranceDenominatorNonzero,
    RFAP.ExplicitField.div_mul_cancel _ quadranceDenominatorNonzero,
    RFAP.ExplicitField.div_mul_cancel _ quadranceDenominatorNonzero⟩

/-- The two Cross-law calculations yielding `s₁=176/225` and
`s₂=2016/4225`, recorded without division. -/
theorem problem_5_initial_spread_certificates :
    (176 : K) * (4 * 25 * 81) =
        225 * (4 * 25 * 81 - (81 + 25 - 64) ^ 2) ∧
      (2016 : K) * (4 * 169 * 25) =
        4225 * (4 * 169 * 25 - (169 + 25 - 100) ^ 2) := by
  constructor <;> ring1

/-- The exact rational comparison used to select the `s₁+s₂≥1` row of the
Triangle spread table. -/
theorem problem_5_spread_sum_above_one :
    950625 < 176 * 4225 + 2016 * 225 := by decide

/-- The displayed root solves equation (21.3), after clearing the common
denominator. -/
theorem problem_5_quadratic_cleared
    (root : K) (rootSquare : root ^ 2 = 154) :
    problem5ThirdSpreadNumerator root ^ 2 -
        975136 * problem5ThirdSpreadNumerator root +
        215296 * 390625 = 0 := by
  calc
    problem5ThirdSpreadNumerator root ^ 2 -
          975136 * problem5ThirdSpreadNumerator root +
          215296 * 390625 =
        997549056 * (root ^ 2 - 154) := by
          unfold problem5ThirdSpreadNumerator
          ring1
    _ = 0 := by rw [rootSquare]; ring1

/-- With all three spreads put over `950625`, this is exactly the Triple
spread equation multiplied by the cube of that denominator. -/
theorem problem_5_triple_spread_cleared
    (root : K) (rootSquare : root ^ 2 = 154) :
    let firstNumerator : K := 176 * 4225
    let secondNumerator : K := 2016 * 225
    let thirdNumerator := problem5ThirdSpreadNumerator root
    950625 *
          ((firstNumerator + secondNumerator + thirdNumerator) ^ 2 -
            2 * (firstNumerator ^ 2 + secondNumerator ^ 2 +
              thirdNumerator ^ 2)) -
        4 * firstNumerator * secondNumerator * thirdNumerator = 0 := by
  dsimp only
  calc
    950625 *
          (((176 * 4225 : K) + 2016 * 225 +
              problem5ThirdSpreadNumerator root) ^ 2 -
            2 * ((176 * 4225 : K) ^ 2 + (2016 * 225 : K) ^ 2 +
              problem5ThirdSpreadNumerator root ^ 2)) -
        4 * (176 * 4225 : K) * (2016 * 225) *
          problem5ThirdSpreadNumerator root =
        -948295071360000 * (root ^ 2 - 154) := by
          unfold problem5ThirdSpreadNumerator
          ring1
    _ = 0 := by rw [rootSquare]; ring1

/-- The three cleared Spread-law equalities used to obtain `Q(A,E)` and
`Q(B,E)` from the selected third spread. -/
theorem problem_5_spread_law_cleared
    (root : K) (rootSquare : root ^ 2 = 154) :
    let firstNumerator : K := 176 * 4225
    let secondNumerator : K := 2016 * 225
    let thirdNumerator := problem5ThirdSpreadNumerator root
    let qAENumerator := problem5QuadranceAENumerator root
    let qBENumerator := problem5QuadranceBENumerator root
    firstNumerator * qAENumerator = secondNumerator * qBENumerator ∧
      25 * firstNumerator * 525625 = thirdNumerator * qBENumerator ∧
      25 * secondNumerator * 525625 = thirdNumerator * qAENumerator := by
  dsimp only
  constructor
  · unfold problem5QuadranceAENumerator problem5QuadranceBENumerator
    ring1
  constructor
  · have differenceZero :
        (25 : K) * (176 * 4225) * 525625 -
            problem5ThirdSpreadNumerator root *
              problem5QuadranceBENumerator root = 0 := by
      calc
        (25 : K) * (176 * 4225) * 525625 -
              problem5ThirdSpreadNumerator root *
                problem5QuadranceBENumerator root =
            115902730944 * (root ^ 2 - 154) := by
              unfold problem5ThirdSpreadNumerator
                problem5QuadranceBENumerator
              ring1
        _ = 0 := by rw [rootSquare]; ring1
    exact sub_eq_zero.mp differenceZero
  · have differenceZero :
        (25 : K) * (2016 * 225) * 525625 -
            problem5ThirdSpreadNumerator root *
              problem5QuadranceAENumerator root = 0 := by
      calc
        (25 : K) * (2016 * 225) * 525625 -
              problem5ThirdSpreadNumerator root *
                problem5QuadranceAENumerator root =
            70701289344 * (root ^ 2 - 154) := by
              unfold problem5ThirdSpreadNumerator
                problem5QuadranceAENumerator
              ring1
        _ = 0 := by rw [rootSquare]; ring1
    exact sub_eq_zero.mp differenceZero

/-- The Collinear quadrance rules for the two final answers.  Scaling all
three entries by `525625` leaves a quad triple, so these two statements are
the denominator-free forms of the printed `Q(C,E)` and `Q(D,E)` values. -/
theorem problem_5_collinear_quadrances_cleared
    (root : K) (rootSquare : root ^ 2 = 154) :
    QuadTriple (81 * 525625)
        (problem5QuadranceAENumerator root)
        (problem5QuadranceCENumerator root) ∧
      QuadTriple (169 * 525625)
        (problem5QuadranceBENumerator root)
        (problem5QuadranceDENumerator root) := by
  constructor
  · unfold QuadTriple archimedesFunction
    calc
      ((81 * 525625 : K) + problem5QuadranceAENumerator root +
            problem5QuadranceCENumerator root) ^ 2 -
          2 * ((81 * 525625 : K) ^ 2 +
            problem5QuadranceAENumerator root ^ 2 +
            problem5QuadranceCENumerator root ^ 2) =
          -30472056022500 * (root ^ 2 - 154) := by
            unfold problem5QuadranceAENumerator
              problem5QuadranceCENumerator
            ring1
      _ = 0 := by rw [rootSquare]; ring1
  · unfold QuadTriple archimedesFunction
    calc
      ((169 * 525625 : K) + problem5QuadranceBENumerator root +
            problem5QuadranceDENumerator root) ^ 2 -
          2 * ((169 * 525625 : K) ^ 2 +
            problem5QuadranceBENumerator root ^ 2 +
            problem5QuadranceDENumerator root ^ 2) =
          -26481830602500 * (root ^ 2 - 154) := by
            unfold problem5QuadranceBENumerator
              problem5QuadranceDENumerator
            ring1
      _ = 0 := by rw [rootSquare]; ring1

/-! ## Problem 6: the eyeball theorem -/

/-- The first Spread-ratio step in the Eyeball theorem.  A marker on the
source circle lies on the same displayed tangent ray as the tangent point on
the other circle, so replacing that ray representative preserves its spread
with the line of centers. -/
theorem eyeball_tangent_spread [DecidableEq K]
    (source other tangent marker : Point K)
    (tangentRay : Line K)
    (sourceOtherDistinct : source ≠ other)
    (sourceTangentDistinct : source ≠ tangent)
    (otherTangentDistinct : other ≠ tangent)
    (sourceMarkerDistinct : source ≠ marker)
    (sourceOtherNonNull :
      ¬ (lineThrough source other sourceOtherDistinct).IsNull)
    (sourceTangentNonNull :
      ¬ (lineThrough source tangent sourceTangentDistinct).IsNull)
    (sourceMarkerNonNull :
      ¬ (lineThrough source marker sourceMarkerDistinct).IsNull)
    (twoNonzero : (2 : K) ≠ 0)
    (rightAtTangent :
      (lineThrough source tangent sourceTangentDistinct).Perpendicular
        (lineThrough other tangent otherTangentDistinct))
    (rayContainsSource : tangentRay.Contains source)
    (rayContainsTangent : tangentRay.Contains tangent)
    (rayContainsMarker : tangentRay.Contains marker)
    (otherRadius centerSeparation : K)
    (otherRadiusValue : quadrance other tangent = otherRadius)
    (centerSeparationValue :
      quadrance source other = centerSeparation) :
    spread (lineThrough source marker sourceMarkerDistinct)
        (lineThrough source other sourceOtherDistinct)
        sourceMarkerNonNull sourceOtherNonNull =
      otherRadius / centerSeparation := by
  have tangentMarkerParallel :
      (lineThrough source tangent sourceTangentDistinct).Parallel
        (lineThrough source marker sourceMarkerDistinct) :=
    parallel_pair_through_common_line source tangent marker
      sourceTangentDistinct sourceMarkerDistinct tangentRay
      rayContainsSource rayContainsTangent rayContainsMarker
  have replacement := spread_eq_of_parallel_pairs
    (lineThrough source tangent sourceTangentDistinct)
    (lineThrough source other sourceOtherDistinct)
    (lineThrough source marker sourceMarkerDistinct)
    (lineThrough source other sourceOtherDistinct)
    sourceTangentNonNull sourceOtherNonNull sourceMarkerNonNull
    sourceOtherNonNull tangentMarkerParallel
    (Line.parallel_refl _)
  have ratio := spread_ratio source other tangent sourceOtherDistinct
    sourceTangentDistinct otherTangentDistinct sourceOtherNonNull
    sourceTangentNonNull twoNonzero rightAtTangent
  calc
    spread (lineThrough source marker sourceMarkerDistinct)
        (lineThrough source other sourceOtherDistinct)
        sourceMarkerNonNull sourceOtherNonNull =
      spread (lineThrough source tangent sourceTangentDistinct)
        (lineThrough source other sourceOtherDistinct)
        sourceTangentNonNull sourceOtherNonNull := replacement.symm
    _ = spread (lineThrough source other sourceOtherDistinct)
        (lineThrough source tangent sourceTangentDistinct)
        sourceOtherNonNull sourceTangentNonNull :=
      spread_symm _ _ sourceTangentNonNull sourceOtherNonNull
    _ = quadrance other tangent / quadrance source other := ratio
    _ = otherRadius / centerSeparation := by
      rw [otherRadiusValue, centerSeparationValue]

/-- The metric calculation for either eye of the Eyeball theorem.  A right
triangle from one endpoint of a chord to its midpoint converts the supplied
tangent spread `otherRadius / centerSeparation` into the common cleared chord
quadrance `centerSeparation * chord = 4 * ownRadius * otherRadius`. -/
theorem eyeball_chord_quadrance_cleared [DecidableEq K]
    (center first second : Point K)
    (centerFirstDistinct : center ≠ first)
    (centerMidpointDistinct : center ≠ midpoint first second)
    (firstMidpointDistinct : first ≠ midpoint first second)
    (centerFirstNonNull :
      ¬ (lineThrough center first centerFirstDistinct).IsNull)
    (centerMidpointNonNull :
      ¬ (lineThrough center (midpoint first second)
        centerMidpointDistinct).IsNull)
    (twoNonzero : (2 : K) ≠ 0)
    (rightAtMidpoint :
      (lineThrough center (midpoint first second)
          centerMidpointDistinct).Perpendicular
        (lineThrough first (midpoint first second)
          firstMidpointDistinct))
    (ownRadius otherRadius centerSeparation : K)
    (centerSeparationNonzero : centerSeparation ≠ 0)
    (ownRadiusValue : quadrance center first = ownRadius)
    (tangentSpreadValue :
      spread (lineThrough center first centerFirstDistinct)
          (lineThrough center (midpoint first second)
            centerMidpointDistinct)
          centerFirstNonNull centerMidpointNonNull =
        otherRadius / centerSeparation) :
    centerSeparation * quadrance first second =
      4 * ownRadius * otherRadius := by
  have ownQuadranceNonzero : quadrance center first ≠ 0 :=
    fun quadranceZero => centerFirstNonNull
      ((null_line_iff_quadrance_zero center first centerFirstDistinct).2
        quadranceZero)
  have ratioAtCenter := spread_ratio center first (midpoint first second)
    centerFirstDistinct centerMidpointDistinct firstMidpointDistinct
    centerFirstNonNull centerMidpointNonNull twoNonzero rightAtMidpoint
  have ratioEquality :
      otherRadius / centerSeparation =
        quadrance first (midpoint first second) /
          quadrance center first := by
    calc
      otherRadius / centerSeparation =
          spread (lineThrough center first centerFirstDistinct)
            (lineThrough center (midpoint first second)
              centerMidpointDistinct)
            centerFirstNonNull centerMidpointNonNull :=
        tangentSpreadValue.symm
      _ = quadrance first (midpoint first second) /
          quadrance center first := ratioAtCenter
  have spreadCrossProduct := cross_mul_of_div_eq_div
    centerSeparationNonzero ownQuadranceNonzero ratioEquality
  rw [ownRadiusValue] at spreadCrossProduct
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [fourAsProduct]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have midpointValue := midpoint_quadrance first second twoNonzero
  have midpointCleared :
      quadrance (midpoint first second) first * 4 =
        quadrance first second := by
    calc
      quadrance (midpoint first second) first * 4 =
          (quadrance first second / 4) * 4 := by rw [midpointValue]
      _ = quadrance first second :=
        RFAP.ExplicitField.div_mul_cancel _ fourNonzero
  calc
    centerSeparation * quadrance first second =
        centerSeparation *
          (quadrance (midpoint first second) first * 4) := by
            rw [midpointCleared]
    _ = 4 *
        (quadrance first (midpoint first second) * centerSeparation) := by
          rw [quadrance_symm (midpoint first second) first]
          ring1
    _ = 4 * (otherRadius * ownRadius) := by rw [← spreadCrossProduct]
    _ = 4 * ownRadius * otherRadius := by ring1

/-- Problem 6 (Eyeball theorem), final symmetric cancellation.  Applying
`eyeball_chord_quadrance_cleared` to the two circles supplies the two premises. -/
theorem problem_6
    (firstChord secondChord firstRadius secondRadius
      centerSeparation : K)
    (centerSeparationNonzero : centerSeparation ≠ 0)
    (firstChordFormula :
      centerSeparation * firstChord = 4 * firstRadius * secondRadius)
    (secondChordFormula :
      centerSeparation * secondChord = 4 * secondRadius * firstRadius) :
    firstChord = secondChord := by
  have productsEqual :
      centerSeparation * firstChord = centerSeparation * secondChord := by
    calc
      centerSeparation * firstChord = 4 * firstRadius * secondRadius :=
        firstChordFormula
      _ = 4 * secondRadius * firstRadius := by ring1
      _ = centerSeparation * secondChord := secondChordFormula.symm
  have centerCancel : centerSeparation * centerSeparation⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel centerSeparation
      centerSeparationNonzero
  have inverseCenterCancel :
      centerSeparation⁻¹ * centerSeparation = (1 : K) := by
    calc
      centerSeparation⁻¹ * centerSeparation =
          centerSeparation * centerSeparation⁻¹ := by ring1
      _ = 1 := centerCancel
  calc
    firstChord = 1 * firstChord := by rw [one_mul]
    _ = centerSeparation⁻¹ *
        (centerSeparation * firstChord) := by
          rw [← mul_assoc, inverseCenterCancel, one_mul]
    _ = centerSeparation⁻¹ *
        (centerSeparation * secondChord) := by rw [productsEqual]
    _ = secondChord := by rw [← mul_assoc, inverseCenterCancel, one_mul]

/-! ## Problem 7: the quadrilateral problem -/

/-- The literal Euler-function substitution in Solution 1 reduces to the
book's centered quadratic, with its harmless nonzero scalar factor exposed. -/
theorem problem_7_euler_reduction (unknown : K) :
    Quadrilateral.eulerFunction 100 65 49 61 26 unknown =
      -98 * ((unknown - 114) ^ 2 - 80 ^ 2) := by
  unfold Quadrilateral.eulerFunction Quadrilateral.determinantThree
  ring1

/-- The four-point relation for the six quadrances displayed in Figure 21.4. -/
theorem problem_7_four_point_relation
    (a₁ a₂ a₃ a₄ : Point K) (unknown : K)
    (q₂₄ : quadrance a₄ a₂ = 100)
    (q₁₂ : quadrance a₁ a₂ = 65)
    (q₁₄ : quadrance a₁ a₄ = 49)
    (q₁₃ : quadrance a₁ a₃ = 61)
    (q₃₄ : quadrance a₄ a₃ = 26)
    (q₂₃ : quadrance a₂ a₃ = unknown) :
    Quadrilateral.eulerFunction 100 65 49 61 26 unknown = 0 := by
  have relation := Quadrilateral.four_point_relation a₁ a₄ a₂ a₃
  rw [q₂₄, q₁₂, q₁₄, q₁₃, q₃₄, q₂₃] at relation
  exact relation

/-- The two algebraic candidates in Solution 1 are exactly `34` and `194`.
The factor `98` must be nonzero in the ambient explicit field. -/
theorem problem_7_euler_roots [DecidableEq K]
    (unknown : K) (ninetyEightNonzero : (98 : K) ≠ 0)
    (relation :
      Quadrilateral.eulerFunction 100 65 49 61 26 unknown = 0) :
    unknown = 34 ∨ unknown = 194 := by
  have negativeNinetyEightNonzero : (-98 : K) ≠ 0 := by
    intro negativeZero
    apply ninetyEightNonzero
    calc
      (98 : K) = -(-98) := by ring1
      _ = 0 := by rw [negativeZero]; ring1
  have scaledFactorZero :
      (-98 : K) * ((unknown - 34) * (unknown - 194)) = 0 := by
    calc
      (-98 : K) * ((unknown - 34) * (unknown - 194)) =
          Quadrilateral.eulerFunction 100 65 49 61 26 unknown := by
            rw [problem_7_euler_reduction]
            ring1
      _ = 0 := relation
  have factorZero : (unknown - 34) * (unknown - 194) = 0 := by
    by_cases zero : (unknown - 34) * (unknown - 194) = 0
    · exact zero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero negativeNinetyEightNonzero zero)
          scaledFactorZero)
  by_cases firstZero : unknown - 34 = 0
  · exact Or.inl (sub_eq_zero.mp firstZero)
  · by_cases secondZero : unknown - 194 = 0
    · exact Or.inr (sub_eq_zero.mp secondZero)
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero firstZero secondZero) factorZero)

abbrev ProblemSevenRational := RFAP.ConstructiveFraction.Rational

/-- Solution 1's acuteness bound rejects the upper candidate `194` and
selects `Q=34`.  The stated strict bound is the exact finite consequence of
the book's stronger `Q≤126` comparison needed by the root-selection step. -/
theorem problem_7_solution_one
    (unknown : ProblemSevenRational)
    (relation :
      Quadrilateral.eulerFunction 100 65 49 61 26 unknown = 0)
    (belowAlternate : unknown < 194) : unknown = 34 := by
  have ninetyEightPositive :
      (0 : ProblemSevenRational) < 98 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (by decide)
  have ninetyEightNonzero : (98 : ProblemSevenRational) ≠ 0 := by
    intro zero
    rw [zero] at ninetyEightPositive
    exact (lt_irrefl 0 ninetyEightPositive).elim
  rcases problem_7_euler_roots unknown
      ninetyEightNonzero relation with
    correct | alternate
  · exact correct
  · rw [← alternate] at belowAlternate
    exfalso
    exact lt_irrefl unknown belowAlternate

/-- The selected auxiliary spread `z=1521/1525` in Solution 2. -/
def problem7AuxiliarySpread : ProblemSevenRational := 1521 / 1525

/-- The selected sector spread `x=1849/3965` in Solution 2. -/
def problem7SectorSpread : ProblemSevenRational := 1849 / 3965

/-- A Triple spread equation with three numerators over one common
denominator, multiplied through by the cube of that denominator. -/
def clearedSpreadTriple
    (denominator first second third : K) : K :=
  denominator *
      ((first + second + third) ^ 2 -
        2 * (first ^ 2 + second ^ 2 + third ^ 2)) -
    4 * first * second * third

/-- All three literal spread triples used in Solution 2, with their finite
common denominators cleared, together with the centered equation selecting
`z`.  The respective scaled numerator triples are
`(625,976,1521)`, `(46225,98865,47824)`, and `(1849,1625,3904)`. -/
theorem problem_7_spread_certificates :
    clearedSpreadTriple (1525 : K) 625 976 1521 = 0 ∧
      clearedSpreadTriple (99125 : K) 46225 98865 47824 = 0 ∧
      clearedSpreadTriple (3965 : K) 1849 1625 3904 = 0 ∧
      ((1521 : K) - 801) ^ 2 = 720 ^ 2 := by
  unfold clearedSpreadTriple
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

/-- The two exact comparisons by which the Triangle spread rules select `z`
and classify `x` as acute. -/
theorem problem_7_spread_comparisons :
    1525 < 625 + 976 ∧ 1849 ≤ 1625 + 3904 := by decide

/-- The displayed Two spread triples quotient evaluates to `1849/3965`.
All four input spreads have been scaled to the common denominator `99125`,
so this is the exact cross-product form of the source's fraction. -/
theorem problem_7_two_spread_triples_value :
    let denominator : K := 99125
    let first : K := 98865
    let second : K := 47824
    let third : K := 40625
    let fourth : K := 97600
    3965 * ((first - second) ^ 2 - (third - fourth) ^ 2) =
      1849 * 2 *
        (denominator * (first + second - third - fourth) -
          2 * first * second + 2 * third * fourth) := by
  dsimp only
  ring1

/-- The source's bound `Q≤126` is strictly below both rejected algebraic
candidates.  This is a closed natural-number comparison, independent of any
completed ordered field. -/
theorem problem_7_candidate_bound_certificates :
    (126 : Nat) < 194 ∧ (126 : Nat) < 218 := by decide

/-- Both independent calculations accept the selected value `Q=34`. -/
theorem problem_7_selected_value_certificates :
    Quadrilateral.eulerFunction (100 : K) 65 49 61 26 34 = 0 ∧
      ((34 : K) - 126) ^ 2 = 92 ^ 2 := by
  constructor
  · rw [problem_7_euler_reduction]
    ring1
  · ring1

/-- Solution 2's Cross-law equation has candidates `34` and `218`; its acute
bound again selects `Q=34`. -/
theorem problem_7_solution_two
    (unknown : ProblemSevenRational)
    (crossLaw : (unknown - 126) ^ 2 = 92 ^ 2)
    (belowAlternate : unknown < 218) : unknown = 34 := by
  have factorZero :
      (unknown - 34) * (unknown - 218) = 0 := by
    calc
      (unknown - 34) * (unknown - 218) =
          (unknown - 126) ^ 2 - 92 ^ 2 := by ring1
      _ = 0 := by rw [crossLaw]; ring1
  by_cases firstZero : unknown - 34 = 0
  · exact sub_eq_zero.mp firstZero
  · by_cases secondZero : unknown - 218 = 0
    · have alternate : unknown = 218 := sub_eq_zero.mp secondZero
      rw [← alternate] at belowAlternate
      exfalso
      exact lt_irrefl unknown belowAlternate
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero firstZero secondZero) factorZero)

end TwoDimensionalProblems
end DivineProportions
