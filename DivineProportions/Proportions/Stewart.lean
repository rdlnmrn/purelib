import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Proportions.TwoStruts

/-!
# Divine Proportions, Chapter 11: Stewart's theorem

The proof below is stronger than the source's two-case spread argument.  After
writing the base as two collinear displacement vectors, a finite two-dimensional
dot/determinant identity proves the formula uniformly, including the source's
`R₃ = 0` case.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Theorem 75 (Stewart's theorem).  No division or non-null hypothesis is
needed by the polynomial identity itself. -/
theorem stewart [DecidableEq K]
    (first second vertex point : Point K)
    (firstSecondDistinct : first ≠ second)
    (pointOnBase :
      (lineThrough first second firstSecondDistinct).Contains point) :
    quadrance second point *
        (quadrance vertex point + quadrance first point -
          quadrance first vertex) ^ 2 =
      quadrance first point *
        (quadrance vertex point + quadrance second point -
          quadrance second vertex) ^ 2 := by
  let a := point.x - first.x
  let b := point.y - first.y
  let c := second.x - point.x
  let d := second.y - point.y
  let u := vertex.x - point.x
  let v := vertex.y - point.y
  let firstDot := u * a + v * b
  let secondDot := u * c + v * d
  let determinant := a * d - b * c
  have pointOnBaseExpanded :
      (first.y - second.y) * point.x +
          (second.x - first.x) * point.y +
          (first.x * second.y - second.x * first.y) = 0 :=
    pointOnBase
  have determinantZero : determinant = 0 := by
    unfold determinant a b c d
    calc
      (point.x - first.x) * (second.y - point.y) -
          (point.y - first.y) * (second.x - point.x) =
        -((first.y - second.y) * point.x +
          (second.x - first.x) * point.y +
          (first.x * second.y - second.x * first.y)) := by ring1
      _ = 0 := by rw [pointOnBaseExpanded]; ring1
  have firstMetricIdentity :
      quadrance vertex point + quadrance first point -
          quadrance first vertex = -2 * firstDot := by
    unfold quadrance firstDot u v a b
    ring1
  have secondMetricIdentity :
      quadrance vertex point + quadrance second point -
          quadrance second vertex = 2 * secondDot := by
    unfold quadrance secondDot u v c d
    ring1
  have dotNormDifferenceZero :
      quadrance second point * firstDot ^ 2 -
        quadrance first point * secondDot ^ 2 = 0 := by
    calc
      quadrance second point * firstDot ^ 2 -
          quadrance first point * secondDot ^ 2 =
        determinant *
          ((a * d + b * c) * (u ^ 2 - v ^ 2) +
            2 * u * v * (b * d - a * c)) := by
        unfold quadrance firstDot secondDot determinant a b c d u v
        ring1
      _ = 0 := by rw [determinantZero]; ring1
  have dotNormEquality :
      quadrance second point * firstDot ^ 2 =
        quadrance first point * secondDot ^ 2 := by
    calc
      quadrance second point * firstDot ^ 2 =
          (quadrance second point * firstDot ^ 2 -
            quadrance first point * secondDot ^ 2) +
              quadrance first point * secondDot ^ 2 := by ring1
      _ = quadrance first point * secondDot ^ 2 := by
        rw [dotNormDifferenceZero]
        ring1
  rw [firstMetricIdentity, secondMetricIdentity]
  calc
    quadrance second point * (-2 * firstDot) ^ 2 =
        4 * (quadrance second point * firstDot ^ 2) := by ring1
    _ = 4 * (quadrance first point * secondDot ^ 2) := by
      rw [dotNormEquality]
    _ = quadrance first point * (2 * secondDot) ^ 2 := by ring1

end DivineProportions
