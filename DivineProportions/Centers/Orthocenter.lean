import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Centers.AffineCircumcenter

/-!
# Divine Proportions, §12.3: altitudes and the orthocenter

Each triangle altitude is an explicit line.  The first two are nonparallel
whenever the vertices are noncollinear, so their intersection is executable.
The coefficient determinant of all three altitude lines vanishes by a single
polynomial identity, proving that the third passes through the same point.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The altitude from `first` to the opposite side `second third`. -/
def triangleAltitudeFromFirst [DecidableEq K]
    (first second third : Point K) (secondThirdDistinct : second ≠ third) :
    Line K :=
  altitudeThrough first (lineThrough second third secondThirdDistinct)

/-- The altitude from `second` to the opposite side `first third`. -/
def triangleAltitudeFromSecond [DecidableEq K]
    (first second third : Point K) (firstThirdDistinct : first ≠ third) :
    Line K :=
  altitudeThrough second (lineThrough first third firstThirdDistinct)

/-- The altitude from `third` to the opposite side `first second`. -/
def triangleAltitudeFromThird [DecidableEq K]
    (first second third : Point K) (firstSecondDistinct : first ≠ second) :
    Line K :=
  altitudeThrough third (lineThrough first second firstSecondDistinct)

/-- The first two triangle altitudes are nonparallel for a noncollinear
triangle. -/
theorem triangle_altitudes_not_parallel
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third) :
    ¬ (triangleAltitudeFromFirst first second third secondThirdDistinct).Parallel
      (triangleAltitudeFromSecond first second third firstThirdDistinct) := by
  intro parallel
  apply notCollinear
  apply (collinear_iff_pointDeterminant_eq_zero first second third).2
  change
    (-(lineThrough second third secondThirdDistinct).b) *
        (lineThrough first third firstThirdDistinct).a -
      (-(lineThrough first third firstThirdDistinct).b) *
        (lineThrough second third secondThirdDistinct).a = 0 at parallel
  simp only [lineThrough_a, lineThrough_b] at parallel
  have parallelNormalized :
      (second.x - third.x) * (first.y - third.y) -
        (first.x - third.x) * (second.y - third.y) = 0 := by
    calc
      (second.x - third.x) * (first.y - third.y) -
          (first.x - third.x) * (second.y - third.y) =
        -(third.x - second.x) * (first.y - third.y) -
          -(third.x - first.x) * (second.y - third.y) := by ring1
      _ = 0 := parallel
  calc
    pointDeterminant first second third =
        -((second.x - third.x) * (first.y - third.y) -
          (first.x - third.x) * (second.y - third.y)) := by
            unfold pointDeterminant
            ring1
    _ = 0 := by rw [parallelNormalized]; ring1

/-- The displayed orthocenter: the explicit intersection of the altitudes
from the first two vertices. -/
def orthocenterPoint [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third) : Point K :=
  lineIntersection
    (triangleAltitudeFromFirst first second third secondThirdDistinct)
    (triangleAltitudeFromSecond first second third firstThirdDistinct)
    (triangle_altitudes_not_parallel first second third firstThirdDistinct
      secondThirdDistinct notCollinear)

/-- The coefficient determinant of the three triangle altitudes vanishes. -/
theorem triangle_altitudes_determinant_zero [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third) :
    lineDeterminant
        (triangleAltitudeFromFirst first second third secondThirdDistinct)
        (triangleAltitudeFromSecond first second third firstThirdDistinct)
        (triangleAltitudeFromThird first second third firstSecondDistinct) = 0 := by
  unfold lineDeterminant triangleAltitudeFromFirst
    triangleAltitudeFromSecond triangleAltitudeFromThird altitudeThrough
    lineThrough
  ring1

/-- Theorem 85 (Orthocenter).  The construction needs only noncollinearity;
in particular, unlike the source proof, it does not need the stronger
non-null-side hypotheses or any spread case split. -/
theorem orthocenter
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third) :
    let center := orthocenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear
    (triangleAltitudeFromFirst first second third
        secondThirdDistinct).Contains center ∧
      (triangleAltitudeFromSecond first second third
        firstThirdDistinct).Contains center ∧
      (triangleAltitudeFromThird first second third
        firstSecondDistinct).Contains center := by
  dsimp only
  let nonparallel := triangle_altitudes_not_parallel first second third
    firstThirdDistinct secondThirdDistinct notCollinear
  constructor
  · unfold orthocenterPoint
    exact lineIntersection_on_first
      (triangleAltitudeFromFirst first second third secondThirdDistinct)
      (triangleAltitudeFromSecond first second third firstThirdDistinct)
      nonparallel
  constructor
  · unfold orthocenterPoint
    exact lineIntersection_on_second
      (triangleAltitudeFromFirst first second third secondThirdDistinct)
      (triangleAltitudeFromSecond first second third firstThirdDistinct)
      nonparallel
  · unfold orthocenterPoint
    exact lineIntersection_on_third_of_determinant_eq_zero
      (triangleAltitudeFromFirst first second third secondThirdDistinct)
      (triangleAltitudeFromSecond first second third firstThirdDistinct)
      (triangleAltitudeFromThird first second third firstSecondDistinct)
      nonparallel
      (triangle_altitudes_determinant_zero first second third
        firstSecondDistinct firstThirdDistinct secondThirdDistinct)

end DivineProportions
