import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Circles.ProjectiveCircle

/-!
# Divine Proportions, Exercise 16.7: projective-circle rays

Line equality remains the explicit cross-product relation `Line.Equivalent`;
no quotient of coefficient triples is introduced.  The canonical ray for a
parameter `λ` is `⟨-1:λ:0⟩`.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

/-- The distinguished origin on the projective circle. -/
def projectiveCircleOrigin : Point K := ⟨0, 0⟩

/-- The canonical line through the origin corresponding to parameter `λ`. -/
def projectiveCircleLine [Nontrivial K] (parameter : K) : Line K where
  a := -1
  b := parameter
  c := 0
  direction_nonzero := Or.inl (neg_ne_zero.mpr one_ne_zero)

/-- An admissible projective-circle point is not the distinguished origin. -/
theorem projectiveCirclePoint_ne_origin [Nontrivial K]
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    projectiveCirclePoint parameter ≠ projectiveCircleOrigin := by
  have denominatorNonzero : 1 + parameter ^ 2 ≠ 0 :=
    (projectiveParameter_denominator_ne_zero_iff parameter).2
      squareNotNegativeOne
  intro pointEqualsOrigin
  have yEqualsZero := congrArg Point.y pointEqualsOrigin
  change 1 / (1 + parameter ^ 2) = 0 at yEqualsZero
  apply (one_ne_zero : (1 : K) ≠ 0)
  calc
    (1 : K) = (1 / (1 + parameter ^ 2)) *
        (1 + parameter ^ 2) :=
      (RFAP.ExplicitField.div_mul_cancel 1 denominatorNonzero).symm
    _ = 0 := by rw [yEqualsZero]; ring1

/-- The canonical ray contains the origin. -/
theorem projectiveCircleLine_contains_origin [Nontrivial K]
    (parameter : K) :
    (projectiveCircleLine parameter).Contains projectiveCircleOrigin := by
  unfold projectiveCircleLine projectiveCircleOrigin Line.Contains
  ring1

/-- The canonical ray contains its parametrized point. -/
theorem projectiveCircleLine_contains_point [Nontrivial K]
    (parameter : K) :
    (projectiveCircleLine parameter).Contains
      (projectiveCirclePoint parameter) := by
  unfold projectiveCircleLine projectiveCirclePoint Line.Contains
  rw [RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ExplicitField.div_eq_mul_inv]
  ring1

/-- The geometric line through the two points is equivalent to the canonical
coefficient representative `⟨-1:λ:0⟩`. -/
theorem lineThrough_projectiveCirclePoint_equivalent [Nontrivial K]
    [DecidableEq K]
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    (lineThrough projectiveCircleOrigin (projectiveCirclePoint parameter)
      (Ne.symm (projectiveCirclePoint_ne_origin parameter
        squareNotNegativeOne))).Equivalent
      (projectiveCircleLine parameter) := by
  apply lineThrough_unique projectiveCircleOrigin
    (projectiveCirclePoint parameter)
    (Ne.symm (projectiveCirclePoint_ne_origin parameter squareNotNegativeOne))
  · exact projectiveCircleLine_contains_origin parameter
  · exact projectiveCircleLine_contains_point parameter

/-- Canonical projective rays are equivalent exactly when their parameters
are equal. -/
theorem projectiveCircleLine_equivalent_iff [Nontrivial K]
    (left right : K) :
    (projectiveCircleLine left).Equivalent
        (projectiveCircleLine right) ↔ left = right := by
  constructor
  · intro equivalent
    have directionEquation := equivalent.1
    change (-1 : K) * right = -1 * left at directionEquation
    calc
      left = -((-1 : K) * left) := by ring1
      _ = -((-1 : K) * right) := by rw [directionEquation]
      _ = right := by ring1
  · intro equal
    rw [equal]
    exact Line.equivalent_refl _

/-- Two non-origin projective-circle points determine equivalent origin rays
exactly when the points are equal.  This is the injective half of Exercise
16.7 without quotienting displayed lines. -/
theorem projectiveCircle_origin_rays_equivalent_iff [Nontrivial K]
    [DecidableEq K]
    (left right : Point K)
    (leftOnCircle : projectiveCircle.Contains left)
    (rightOnCircle : projectiveCircle.Contains right)
    (leftNotOrigin : left ≠ projectiveCircleOrigin)
    (rightNotOrigin : right ≠ projectiveCircleOrigin) :
    (lineThrough projectiveCircleOrigin left (Ne.symm leftNotOrigin)).Equivalent
        (lineThrough projectiveCircleOrigin right (Ne.symm rightNotOrigin)) ↔
      left = right := by
  constructor
  · intro raysEquivalent
    rcases projectiveCirclePoint_exists left leftOnCircle leftNotOrigin with
      ⟨leftParameter, leftAdmissible, leftFormula⟩
    rcases projectiveCirclePoint_exists right rightOnCircle rightNotOrigin with
      ⟨rightParameter, rightAdmissible, rightFormula⟩
    have leftCanonical :
        (lineThrough projectiveCircleOrigin left
          (Ne.symm leftNotOrigin)).Equivalent
            (projectiveCircleLine leftParameter) := by
      apply lineThrough_unique projectiveCircleOrigin left
        (Ne.symm leftNotOrigin)
      · exact projectiveCircleLine_contains_origin leftParameter
      · rw [leftFormula]
        exact projectiveCircleLine_contains_point leftParameter
    have rightCanonical :
        (lineThrough projectiveCircleOrigin right
          (Ne.symm rightNotOrigin)).Equivalent
            (projectiveCircleLine rightParameter) := by
      apply lineThrough_unique projectiveCircleOrigin right
        (Ne.symm rightNotOrigin)
      · exact projectiveCircleLine_contains_origin rightParameter
      · rw [rightFormula]
        exact projectiveCircleLine_contains_point rightParameter
    have canonicalEquivalent :
        (projectiveCircleLine leftParameter).Equivalent
          (projectiveCircleLine rightParameter) :=
      line_equivalent_trans (Line.equivalent_symm leftCanonical)
        (line_equivalent_trans raysEquivalent rightCanonical)
    have parametersEqual :=
      (projectiveCircleLine_equivalent_iff
        leftParameter rightParameter).1 canonicalEquivalent
    calc
      left = projectiveCirclePoint leftParameter := leftFormula
      _ = projectiveCirclePoint rightParameter := by rw [parametersEqual]
      _ = right := rightFormula.symm
  · intro pointsEqual
    subst right
    exact Line.equivalent_refl _

/-- Exercise 16.7: non-origin points on the projective circle and displayed
lines through the origin with such an intersection are in one-to-one
correspondence, expressed through quotient-free line equivalence. -/
theorem exercise_16_7 [Nontrivial K] [DecidableEq K] :
    (∀ (left right : Point K)
      (_leftOnCircle : projectiveCircle.Contains left)
      (_rightOnCircle : projectiveCircle.Contains right)
      (leftNotOrigin : left ≠ projectiveCircleOrigin)
      (rightNotOrigin : right ≠ projectiveCircleOrigin),
      (lineThrough projectiveCircleOrigin left (Ne.symm leftNotOrigin)).Equivalent
          (lineThrough projectiveCircleOrigin right
            (Ne.symm rightNotOrigin)) ↔ left = right) ∧
    (∀ line : Line K,
      line.Contains projectiveCircleOrigin →
      (∃ point : Point K,
        projectiveCircle.Contains point ∧
          point ≠ projectiveCircleOrigin ∧ line.Contains point) →
      ∃ point : Point K,
        ∃ pointNotOrigin : point ≠ projectiveCircleOrigin,
          projectiveCircle.Contains point ∧
          (lineThrough projectiveCircleOrigin point
            (Ne.symm pointNotOrigin)).Equivalent line) := by
  constructor
  · exact projectiveCircle_origin_rays_equivalent_iff
  · intro line originOnLine
    rintro ⟨point, pointOnCircle, pointNotOrigin, pointOnLine⟩
    refine ⟨point, pointNotOrigin, pointOnCircle, ?_⟩
    exact lineThrough_unique projectiveCircleOrigin point
      (Ne.symm pointNotOrigin) line originOnLine pointOnLine

end Conic

end DivineProportions
