import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Conics.Circle
import DivineProportions.Conics.LineIntersection
import DivineProportions.Triangles.Right

/-!
# Divine Proportions, §16.1: diameters

The source's midpoint proof of Theorem 103 requires a non-null diameter side,
the same visible hypothesis as the already formalized midpoint-uniqueness
theorem.  The statement below exposes that characteristic-dependent omission.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

/-- A diameter is a line through the circle center with one explicit point of
intersection. -/
def IsDiameter (circle : Conic K) (line : Line K) (center : Point K) : Prop :=
  line.Contains center ∧
    ∃ point : Point K, circle.IntersectsAt line point

/-- A displayed circle through the three vertices of a triangle. -/
def IsCircumcircleOf (circle : Conic K)
    (first second third center : Point K) (circleQuadrance : K) : Prop :=
  circle.IsCirclePresentation center circleQuadrance ∧
    circle.Contains first ∧ circle.Contains second ∧ circle.Contains third

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
    _ = factor⁻¹ * (factor * value) := mul_assoc _ _ _
    _ = 0 := by rw [productZero]; ring1

/-- The metric core of Theorem 103: once the displayed center is the midpoint,
the Right midpoint theorem gives the right vertex immediately. -/
theorem right_diameter_of_center_eq_midpoint [DecidableEq K]
    (first second third center : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0)
    (centerIsMidpoint : center = midpoint first second)
    (firstRadius : quadrance center first = quadrance center third) :
    (lineThrough first third firstThirdDistinct).Perpendicular
      (lineThrough second third secondThirdDistinct) := by
  apply (right_midpoint first second third firstThirdDistinct
    secondThirdDistinct twoNonzero).1
  rw [← centerIsMidpoint]
  exact firstRadius

/-- Theorem 103 (Right diameter), corrected by exposing the non-null diameter
side required by the source's appeal to midpoint uniqueness. -/
theorem right_diameter [DecidableEq K]
    (circle : Conic K) (first second third center : Point K)
    (circleQuadrance : K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0)
    (diameterSideNonNull :
      ¬ (lineThrough first second firstSecondDistinct).IsNull)
    (circumcircle : circle.IsCircumcircleOf
      first second third center circleQuadrance)
    (diameter : circle.IsDiameter
      (lineThrough first second firstSecondDistinct) center) :
    (lineThrough first third firstThirdDistinct).Perpendicular
      (lineThrough second third secondThirdDistinct) := by
  rcases circumcircle with
    ⟨presentation, firstOnCircle, secondOnCircle, thirdOnCircle⟩
  have firstRadiusFromPoint :
      quadrance first center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center first circleQuadrance
      presentation).1 firstOnCircle
  have secondRadiusFromPoint :
      quadrance second center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center second circleQuadrance
      presentation).1 secondOnCircle
  have thirdRadiusFromPoint :
      quadrance third center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center third circleQuadrance
      presentation).1 thirdOnCircle
  have firstRadius : quadrance center first = circleQuadrance := by
    calc
      quadrance center first = quadrance first center :=
        quadrance_symm center first
      _ = circleQuadrance := firstRadiusFromPoint
  have secondRadius : quadrance center second = circleQuadrance := by
    calc
      quadrance center second = quadrance second center :=
        quadrance_symm center second
      _ = circleQuadrance := secondRadiusFromPoint
  have thirdRadius : quadrance center third = circleQuadrance := by
    calc
      quadrance center third = quadrance third center :=
        quadrance_symm center third
      _ = circleQuadrance := thirdRadiusFromPoint
  have centerIsMidpoint : center = midpoint first second :=
    midpoint_unique_of_equal_quadrance first second center
      firstSecondDistinct twoNonzero diameterSideNonNull diameter.1
      (firstRadius.trans secondRadius.symm)
  exact right_diameter_of_center_eq_midpoint first second third center
    firstThirdDistinct secondThirdDistinct twoNonzero centerIsMidpoint
    (firstRadius.trans thirdRadius.symm)

/-- Rotation in a point preserves the quadrance from that point. -/
theorem rotateInPoint_quadrance_center (center point : Point K) :
    quadrance (rotateInPoint center point) center =
      quadrance point center := by
  unfold quadrance rotateInPoint
  ring1

/-- A line containing a point and the rotation center also contains the rotated
point. -/
theorem line_contains_rotateInPoint (line : Line K) (center point : Point K)
    (containsCenter : line.Contains center)
    (containsPoint : line.Contains point) :
    line.Contains (rotateInPoint center point) := by
  unfold Line.Contains at containsCenter containsPoint ⊢
  unfold rotateInPoint
  calc
    line.a * (2 * center.x - point.x) +
        line.b * (2 * center.y - point.y) + line.c =
      2 * (line.a * center.x + line.b * center.y + line.c) -
        (line.a * point.x + line.b * point.y + line.c) := by ring1
    _ = 0 := by rw [containsCenter, containsPoint]; ring1

/-- Exercise 16.1: reflecting one intersection of a non-null circle's diameter
through the center constructs a distinct second intersection. -/
theorem exercise_16_1 (circle : Conic K) (line : Line K)
    (center : Point K) (circleQuadrance : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation :
      circle.IsCirclePresentation center circleQuadrance)
    (diameter : circle.IsDiameter line center) :
    circle.IsChord line := by
  rcases diameter with ⟨centerOnLine, point, pointIntersection⟩
  have pointRadius : quadrance point center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center point circleQuadrance
      presentation).1 pointIntersection.2
  have pointDifferentCenter : point ≠ center := by
    intro pointEqualsCenter
    apply quadranceNonzero
    calc
      circleQuadrance = quadrance point center := pointRadius.symm
      _ = quadrance center center := by rw [pointEqualsCenter]
      _ = 0 := quadrance_self center
  let opposite := rotateInPoint center point
  have oppositeOnLine : line.Contains opposite :=
    line_contains_rotateInPoint line center point centerOnLine
      pointIntersection.1
  have oppositeOnCircle : circle.Contains opposite := by
    apply (contains_iff_quadrance_eq circle center opposite circleQuadrance
      presentation).2
    calc
      quadrance opposite center = quadrance point center := by
        exact rotateInPoint_quadrance_center center point
      _ = circleQuadrance := pointRadius
  have oppositeDifferent : opposite ≠ point := by
    intro oppositeEqualsPoint
    apply pointDifferentCenter
    have xEquation := congrArg Point.x oppositeEqualsPoint
    have yEquation := congrArg Point.y oppositeEqualsPoint
    change 2 * center.x - point.x = point.x at xEquation
    change 2 * center.y - point.y = point.y at yEquation
    have xProductZero : 2 * (center.x - point.x) = 0 := by
      calc
        2 * (center.x - point.x) =
            (2 * center.x - point.x) - point.x := by ring1
        _ = 0 := by rw [xEquation]; ring1
    have yProductZero : 2 * (center.y - point.y) = 0 := by
      calc
        2 * (center.y - point.y) =
            (2 * center.y - point.y) - point.y := by ring1
        _ = 0 := by rw [yEquation]; ring1
    have xDifferenceZero :=
      eq_zero_of_mul_eq_zero_left twoNonzero xProductZero
    have yDifferenceZero :=
      eq_zero_of_mul_eq_zero_left twoNonzero yProductZero
    apply Point.ext
    · calc
        point.x = center.x - (center.x - point.x) := by ring1
        _ = center.x := by rw [xDifferenceZero]; ring1
    · calc
        point.y = center.y - (center.y - point.y) := by ring1
        _ = center.y := by rw [yDifferenceZero]; ring1
  exact ⟨opposite, point, oppositeDifferent,
    ⟨oppositeOnLine, oppositeOnCircle⟩, pointIntersection⟩

end Conic

end DivineProportions
