import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Circles.Chord

/-!
# Divine Proportions, Exercise 16.6: antipodal quadrance sums

The printed exercise omits a non-null hypothesis.  An executable `F₅`
counterexample below shows that the claim fails on a null circle.  For a
non-null circle, its displayed intersection makes every diameter non-null;
midpoint uniqueness then identifies the two equidistant diameter points as
antipodes, giving an explicit constant quadrance sum.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

/-- A diameter of a circle with nonzero quadrance is non-null. -/
theorem diameter_nonNull_of_circleQuadrance_ne_zero [DecidableEq K]
    (circle : Conic K) (line : Line K) (center : Point K)
    (circleQuadrance : K) (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (diameter : circle.IsDiameter line center) :
    ¬ line.IsNull := by
  rcases diameter.2 with ⟨point, pointIntersection⟩
  have pointRadius : quadrance point center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center point circleQuadrance
      presentation).1 pointIntersection.2
  intro lineNull
  have radiusZero := quadrance_eq_zero_of_null_line_contains line lineNull
    point center pointIntersection.1 diameter.1
  apply quadranceNonzero
  calc
    circleQuadrance = quadrance point center := pointRadius.symm
    _ = 0 := radiusZero

/-- Nullness is invariant under the project's quotient-free line equivalence.
The proof uses the two-dimensional dot/determinant norm identity. -/
private theorem nonNull_of_equivalent [DecidableEq K]
    (left right : Line K) (equivalent : left.Equivalent right)
    (rightNonNull : ¬ right.IsNull) :
    ¬ left.IsNull := by
  intro leftNull
  let dot := left.a * right.a + left.b * right.b
  let determinant := left.a * right.b - left.b * right.a
  have determinantZero : determinant = 0 := by
    unfold determinant
    calc
      left.a * right.b - left.b * right.a =
          right.a * left.b - left.b * right.a := by rw [equivalent.1]
      _ = 0 := by ring1
  have dotSquareZero : dot ^ 2 = 0 := by
    calc
      dot ^ 2 = dot ^ 2 + determinant ^ 2 := by
        rw [determinantZero]
        ring1
      _ = (left.a ^ 2 + left.b ^ 2) *
          (right.a ^ 2 + right.b ^ 2) := by
        unfold dot determinant
        ring1
      _ = 0 := by rw [leftNull]; ring1
  have dotZero : dot = 0 := by
    by_cases dotZero : dot = 0
    · exact dotZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero dotZero dotZero)
          (by simpa [pow_two] using dotSquareZero))
  have rightNormNonzero : right.a ^ 2 + right.b ^ 2 ≠ 0 :=
    rightNonNull
  have leftATimesNorm :
      left.a * (right.a ^ 2 + right.b ^ 2) = 0 := by
    calc
      left.a * (right.a ^ 2 + right.b ^ 2) =
          right.a * dot + right.b * determinant := by
        unfold dot determinant
        ring1
      _ = 0 := by rw [dotZero, determinantZero]; ring1
  have leftAZero : left.a = 0 := by
    by_cases leftAZero : left.a = 0
    · exact leftAZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero leftAZero rightNormNonzero)
          leftATimesNorm)
  have leftBTimesNorm :
      left.b * (right.a ^ 2 + right.b ^ 2) = 0 := by
    calc
      left.b * (right.a ^ 2 + right.b ^ 2) =
          right.b * dot - right.a * determinant := by
        unfold dot determinant
        ring1
      _ = 0 := by rw [dotZero, determinantZero]; ring1
  have leftBZero : left.b = 0 := by
    by_cases leftBZero : left.b = 0
    · exact leftBZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero leftBZero rightNormNonzero)
          leftBTimesNorm)
  exact left.direction_nonzero.elim
    (fun nonzero => nonzero leftAZero)
    (fun nonzero => nonzero leftBZero)

/-- The polynomial antipodal-sum identity, stated using the two coordinate
equations which say that `center` is the midpoint of `first` and `second`. -/
theorem antipodal_quadrance_sum
    (first second center point : Point K)
    (xSum : first.x + second.x = 2 * center.x)
    (ySum : first.y + second.y = 2 * center.y) :
    quadrance first point + quadrance second point =
      2 * (quadrance first center + quadrance point center) := by
  unfold quadrance
  rw [show second.x = 2 * center.x - first.x by
      calc
        second.x = (first.x + second.x) - first.x := by ring1
        _ = 2 * center.x - first.x := by rw [xSum],
    show second.y = 2 * center.y - first.y by
      calc
        second.y = (first.y + second.y) - first.y := by ring1
        _ = 2 * center.y - first.y := by rw [ySum]]
  ring1

/-- Exercise 16.6, corrected by the necessary non-null-circle premise.  The
constant is exhibited explicitly rather than represented by a completed
family of all circle points. -/
theorem exercise_16_6 [DecidableEq K]
    (circle : Conic K) (line : Line K) (center first second point : Point K)
    (circleQuadrance : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (diameter : circle.IsDiameter line center)
    (firstSecondDistinct : first ≠ second)
    (firstOnDiameter : line.Contains first)
    (secondOnDiameter : line.Contains second)
    (equalCenterQuadrances :
      quadrance first center = quadrance second center)
    (pointOnCircle : circle.Contains point) :
    quadrance first point + quadrance second point =
      2 * (quadrance first center + circleQuadrance) := by
  have diameterNonNull := diameter_nonNull_of_circleQuadrance_ne_zero circle
    line center circleQuadrance quadranceNonzero presentation diameter
  have throughEquivalent :
      (lineThrough first second firstSecondDistinct).Equivalent line :=
    lineThrough_unique first second firstSecondDistinct line
      firstOnDiameter secondOnDiameter
  have throughNonNull :
      ¬ (lineThrough first second firstSecondDistinct).IsNull := by
    exact nonNull_of_equivalent
      (lineThrough first second firstSecondDistinct) line
      throughEquivalent diameterNonNull
  have centerEqualQuadrances :
      quadrance center first = quadrance center second := by
    calc
      quadrance center first = quadrance first center :=
        quadrance_symm center first
      _ = quadrance second center := equalCenterQuadrances
      _ = quadrance center second := quadrance_symm second center
  have centerIsMidpoint : center = midpoint first second :=
    midpoint_unique_of_equal_quadrance first second center
      firstSecondDistinct twoNonzero throughNonNull
      (line_contains_of_equivalent
        (Line.equivalent_symm throughEquivalent) center diameter.1)
      centerEqualQuadrances
  have midpointX := congrArg Point.x centerIsMidpoint
  have midpointY := congrArg Point.y centerIsMidpoint
  change center.x = (first.x + second.x) / 2 at midpointX
  change center.y = (first.y + second.y) / 2 at midpointY
  have xSum : first.x + second.x = 2 * center.x := by
    calc
      first.x + second.x = ((first.x + second.x) / 2) * 2 :=
        (RFAP.ExplicitField.div_mul_cancel
          (first.x + second.x) twoNonzero).symm
      _ = center.x * 2 := by rw [← midpointX]
      _ = 2 * center.x := by ring1
  have ySum : first.y + second.y = 2 * center.y := by
    calc
      first.y + second.y = ((first.y + second.y) / 2) * 2 :=
        (RFAP.ExplicitField.div_mul_cancel
          (first.y + second.y) twoNonzero).symm
      _ = center.y * 2 := by rw [← midpointY]
      _ = 2 * center.y := by ring1
  have pointRadius : quadrance point center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center point circleQuadrance
      presentation).1 pointOnCircle
  calc
    quadrance first point + quadrance second point =
        2 * (quadrance first center + quadrance point center) :=
      antipodal_quadrance_sum first second center point xSum ySum
    _ = 2 * (quadrance first center + circleQuadrance) := by
      rw [pointRadius]

/-- The corrected exercise's literal independence statement for two requested
circle points, still with only finite witnesses. -/
theorem exercise_16_6_independent [DecidableEq K]
    (circle : Conic K) (line : Line K) (center first second : Point K)
    (circleQuadrance : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (diameter : circle.IsDiameter line center)
    (firstSecondDistinct : first ≠ second)
    (firstOnDiameter : line.Contains first)
    (secondOnDiameter : line.Contains second)
    (equalCenterQuadrances :
      quadrance first center = quadrance second center)
    (left right : Point K)
    (leftOnCircle : circle.Contains left)
    (rightOnCircle : circle.Contains right) :
    quadrance first left + quadrance second left =
      quadrance first right + quadrance second right := by
  calc
    quadrance first left + quadrance second left =
        2 * (quadrance first center + circleQuadrance) :=
      exercise_16_6 circle line center first second left circleQuadrance
        twoNonzero quadranceNonzero presentation diameter firstSecondDistinct
        firstOnDiameter secondOnDiameter equalCenterQuadrances leftOnCircle
    _ = quadrance first right + quadrance second right :=
      (exercise_16_6 circle line center first second right circleQuadrance
        twoNonzero quadranceNonzero presentation diameter firstSecondDistinct
        firstOnDiameter secondOnDiameter equalCenterQuadrances
        rightOnCircle).symm

/-- The printed Exercise 16.6 is false without the non-null premise.  Over
`F₅`, two distinct equidistant points on a null diameter give different sums
at two points of the same null circle. -/
theorem exercise_16_6_null_circle_counterexample :
    let center : Point FieldFive.Element := ⟨0, 0⟩
    let first : Point FieldFive.Element := ⟨1, 2⟩
    let second : Point FieldFive.Element := ⟨2, 4⟩
    let left : Point FieldFive.Element := center
    let right : Point FieldFive.Element := ⟨1, 3⟩
    let circle := circleConic center 0
    let diameterLine : Line FieldFive.Element :=
      { a := 2
        b := -1
        c := 0
        direction_nonzero := Or.inl (by decide) }
    circle.IsDiameter diameterLine center ∧
      first ≠ second ∧
      diameterLine.Contains first ∧ diameterLine.Contains second ∧
      quadrance first center = quadrance second center ∧
      circle.Contains left ∧ circle.Contains right ∧
      quadrance first left + quadrance second left ≠
      quadrance first right + quadrance second right := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ⟨⟨1, 2⟩, ?_⟩⟩
    · unfold Line.Contains
      decide
    · constructor
      · unfold Line.Contains
        decide
      · unfold Contains circleConic evaluate
        decide
  · decide
  · unfold Line.Contains
    decide
  · unfold Line.Contains
    decide
  · unfold quadrance
    decide
  · unfold Contains circleConic evaluate
    decide
  · unfold Contains circleConic evaluate
    decide
  · unfold quadrance
    decide

end Conic

end DivineProportions
