import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Conics.Center

/-!
# Divine Proportions, §15.6: intersections with lines

The restriction of a conic to a displayed line parameter is handled by one
finite interpolation identity.  Thus Theorem 102 needs no completed polynomial
object and no general theorem about a globally collected root set.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

/-- A displayed point of intersection of a conic and a line. -/
def IntersectsAt (conic : Conic K) (line : Line K) (point : Point K) : Prop :=
  line.Contains point ∧ conic.Contains point

/-- A chord is witnessed by exactly the two distinct intersections needed by
the definition. -/
def IsChord (conic : Conic K) (line : Line K) : Prop :=
  ∃ first second : Point K,
    first ≠ second ∧ conic.IntersectsAt line first ∧
      conic.IntersectsAt line second

/-- Three-or-more intersections are represented by three explicit pairwise
distinct witnesses. -/
def HasThreeDistinctIntersections (conic : Conic K) (line : Line K) : Prop :=
  ∃ first second third : Point K,
    first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      conic.IntersectsAt line first ∧
      conic.IntersectsAt line second ∧
      conic.IntersectsAt line third

/-- The quadratic coefficient obtained by restricting a conic to the direction
from `first` to `second`. -/
def lineRestrictionQuadratic (conic : Conic K)
    (first second : Point K) : K :=
  conic.d * (second.x - first.x) ^ 2 +
    conic.e * (second.x - first.x) * (second.y - first.y) +
    conic.f * (second.y - first.y) ^ 2

/-- Every point on a displayed line through two distinct points has one finite
Thales parameter. -/
theorem thalesPoint_exists_of_on_line [DecidableEq K]
    (first second point : Point K) (distinct : first ≠ second)
    (onLine : (lineThrough first second distinct).Contains point) :
    ∃ scale : K, thalesPoint scale first second = point := by
  rcases (affineCombination_iff_on_line first second point distinct).1 onLine with
    ⟨leftWeight, rightWeight, weights, combination⟩
  have leftFormula : leftWeight = 1 - rightWeight := by
    calc
      leftWeight = (leftWeight + rightWeight) - rightWeight := by ring1
      _ = 1 - rightWeight := by rw [weights]
  refine ⟨rightWeight, ?_⟩
  unfold thalesPoint
  rw [← leftFormula]
  exact combination

@[simp] theorem thalesPoint_zero (first second : Point K) :
    thalesPoint 0 first second = first := by
  apply Point.ext <;> unfold thalesPoint affineCombination <;> ring1

@[simp] theorem thalesPoint_one (first second : Point K) :
    thalesPoint 1 first second = second := by
  apply Point.ext <;> unfold thalesPoint affineCombination <;> ring1

/-- Exact quadratic interpolation for the conic restricted to a line. -/
theorem evaluate_thalesPoint (conic : Conic K)
    (first second : Point K) (scale : K) :
    conic.evaluate (thalesPoint scale first second) =
      (1 - scale) * conic.evaluate first +
        scale * conic.evaluate second +
        scale * (scale - 1) *
          conic.lineRestrictionQuadratic first second := by
  unfold evaluate thalesPoint affineCombination lineRestrictionQuadratic
  ring1

/-- Theorem 102 (Conic line intersection): three explicit distinct
intersections force the whole line to lie on the conic. -/
theorem conic_line_intersection [DecidableEq K]
    (conic : Conic K) (line : Line K)
    (threeIntersections : conic.HasThreeDistinctIntersections line) :
    ∀ point : Point K, line.Contains point → conic.Contains point := by
  rcases threeIntersections with
    ⟨first, second, third, firstSecondDistinct, firstThirdDistinct,
      secondThirdDistinct, firstIntersection, secondIntersection,
      thirdIntersection⟩
  have throughEquivalentLine :
      (lineThrough first second firstSecondDistinct).Equivalent line :=
    lineThrough_unique first second firstSecondDistinct line
      firstIntersection.1 secondIntersection.1
  have throughContains :
      ∀ point : Point K, line.Contains point →
        (lineThrough first second firstSecondDistinct).Contains point := by
    intro point onLine
    exact line_contains_of_equivalent
      (Line.equivalent_symm throughEquivalentLine) point onLine
  rcases thalesPoint_exists_of_on_line first second third
      firstSecondDistinct (throughContains third thirdIntersection.1) with
    ⟨thirdScale, thirdParameter⟩
  have thirdScaleNonzero : thirdScale ≠ 0 := by
    intro scaleZero
    apply firstThirdDistinct
    calc
      first = thalesPoint 0 first second := (thalesPoint_zero first second).symm
      _ = thalesPoint thirdScale first second := by rw [scaleZero]
      _ = third := thirdParameter
  have thirdScaleMinusOneNonzero : thirdScale - 1 ≠ 0 := by
    intro differenceZero
    have scaleOne : thirdScale = 1 := by
      calc
        thirdScale = (thirdScale - 1) + 1 := by ring1
        _ = 1 := by rw [differenceZero]; ring1
    apply secondThirdDistinct
    calc
      second = thalesPoint 1 first second := (thalesPoint_one first second).symm
      _ = thalesPoint thirdScale first second := by rw [scaleOne]
      _ = third := thirdParameter
  have firstZero : conic.evaluate first = 0 := firstIntersection.2
  have secondZero : conic.evaluate second = 0 := secondIntersection.2
  have thirdZero :
      conic.evaluate (thalesPoint thirdScale first second) = 0 := by
    rw [thirdParameter]
    exact thirdIntersection.2
  have restrictionProductZero :
      (thirdScale * (thirdScale - 1)) *
        conic.lineRestrictionQuadratic first second = 0 := by
    calc
      (thirdScale * (thirdScale - 1)) *
          conic.lineRestrictionQuadratic first second =
        conic.evaluate (thalesPoint thirdScale first second) := by
          rw [evaluate_thalesPoint, firstZero, secondZero]
          ring1
      _ = 0 := thirdZero
  have scaleProductNonzero : thirdScale * (thirdScale - 1) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero thirdScaleNonzero
      thirdScaleMinusOneNonzero
  have restrictionZero :
      conic.lineRestrictionQuadratic first second = 0 := by
    have inverseCancel :
        (thirdScale * (thirdScale - 1))⁻¹ *
            (thirdScale * (thirdScale - 1)) = (1 : K) := by
      calc
        (thirdScale * (thirdScale - 1))⁻¹ *
            (thirdScale * (thirdScale - 1)) =
          (thirdScale * (thirdScale - 1)) *
            (thirdScale * (thirdScale - 1))⁻¹ := by ring1
        _ = 1 := RFAP.ExplicitField.mul_inv_cancel _ scaleProductNonzero
    calc
      conic.lineRestrictionQuadratic first second =
          1 * conic.lineRestrictionQuadratic first second := by ring1
      _ = ((thirdScale * (thirdScale - 1))⁻¹ *
            (thirdScale * (thirdScale - 1))) *
          conic.lineRestrictionQuadratic first second := by rw [inverseCancel]
      _ = (thirdScale * (thirdScale - 1))⁻¹ *
          ((thirdScale * (thirdScale - 1)) *
            conic.lineRestrictionQuadratic first second) := mul_assoc _ _ _
      _ = 0 := by rw [restrictionProductZero]; ring1
  intro point onLine
  rcases thalesPoint_exists_of_on_line first second point
      firstSecondDistinct (throughContains point onLine) with
    ⟨scale, parameter⟩
  unfold Contains
  rw [← parameter, evaluate_thalesPoint, firstZero, secondZero,
    restrictionZero]
  ring1

end Conic

end DivineProportions
