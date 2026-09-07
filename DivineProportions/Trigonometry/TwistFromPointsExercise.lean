import DivineProportions.Trigonometry.TriangleRatios

/-!
# Divine Proportions, Exercise 6.7

The twist analogue of the preceding Spread-from-points and Cross-from-points
theorems is a direct expansion of the two finite line coefficient triples.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Exercise 6.7: twist between the lines from `vertex` to `first` and
`second`, written in the exact point-coordinate form corresponding to
Theorems 43 and 44. -/
theorem exercise_6_7 [DecidableEq K]
    (first second vertex : Point K)
    (firstDistinct : first ≠ vertex)
    (secondDistinct : second ≠ vertex)
    (notPerpendicular :
      ¬ (lineThrough first vertex firstDistinct).Perpendicular
        (lineThrough second vertex secondDistinct)) :
    twist
        (lineThrough first vertex firstDistinct)
        (lineThrough second vertex secondDistinct)
        notPerpendicular =
      (((first.y - vertex.y) * (vertex.x - second.x) -
          (second.y - vertex.y) * (vertex.x - first.x)) ^ 2) /
        (((first.y - vertex.y) * (second.y - vertex.y) +
          (vertex.x - first.x) * (vertex.x - second.x)) ^ 2) := by
  unfold twist lineThrough
  ring1

end DivineProportions
