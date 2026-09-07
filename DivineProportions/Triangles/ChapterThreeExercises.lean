import DivineProportions.Plane.LineRelations
import DivineProportions.Trigonometry.Quadrance

/-!
# Divine Proportions, Exercises 3.11–3.12

A triangle is kept as three displayed points with explicit distinctness and
noncollinearity certificates.  Right vertices are perpendicularity equations
between its three finite side lines.  Null-side impossibility exposes the
book's standing characteristic-not-two assumption.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem triangle_side_pairs_nonparallel
    [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third) :
    ¬ (lineThrough first second firstSecondDistinct).Parallel
        (lineThrough second third secondThirdDistinct) ∧
      ¬ (lineThrough second third secondThirdDistinct).Parallel
        (lineThrough first third firstThirdDistinct) ∧
      ¬ (lineThrough first third firstThirdDistinct).Parallel
        (lineThrough first second firstSecondDistinct) := by
  constructor
  · intro parallel
    apply notCollinear
    let firstSide := lineThrough first second firstSecondDistinct
    let secondSide := lineThrough second third secondThirdDistinct
    have equivalent := line_equivalent_of_parallel_and_common_point
      firstSide secondSide second parallel
      (lineThrough_contains_second first second firstSecondDistinct)
      (lineThrough_contains_first second third secondThirdDistinct)
    have containsThird : firstSide.Contains third :=
      line_contains_of_equivalent (Line.equivalent_symm equivalent) third
        (lineThrough_contains_second second third secondThirdDistinct)
    exact ⟨firstSide,
      lineThrough_contains_first first second firstSecondDistinct,
      lineThrough_contains_second first second firstSecondDistinct,
      containsThird⟩
  constructor
  · intro parallel
    apply notCollinear
    let secondSide := lineThrough second third secondThirdDistinct
    let thirdSide := lineThrough first third firstThirdDistinct
    have equivalent := line_equivalent_of_parallel_and_common_point
      secondSide thirdSide third parallel
      (lineThrough_contains_second second third secondThirdDistinct)
      (lineThrough_contains_second first third firstThirdDistinct)
    have containsFirst : secondSide.Contains first :=
      line_contains_of_equivalent (Line.equivalent_symm equivalent) first
        (lineThrough_contains_first first third firstThirdDistinct)
    exact ⟨secondSide, containsFirst,
      lineThrough_contains_first second third secondThirdDistinct,
      lineThrough_contains_second second third secondThirdDistinct⟩
  · intro parallel
    apply notCollinear
    let thirdSide := lineThrough first third firstThirdDistinct
    let firstSide := lineThrough first second firstSecondDistinct
    have equivalent := line_equivalent_of_parallel_and_common_point
      thirdSide firstSide first parallel
      (lineThrough_contains_first first third firstThirdDistinct)
      (lineThrough_contains_first first second firstSecondDistinct)
    have containsSecond : thirdSide.Contains second :=
      line_contains_of_equivalent (Line.equivalent_symm equivalent) second
        (lineThrough_contains_second first second firstSecondDistinct)
    exact ⟨thirdSide,
      lineThrough_contains_first first third firstThirdDistinct,
      containsSecond,
      lineThrough_contains_second first third firstThirdDistinct⟩

/-- Exercise 3.11: among the three displayed vertex-perpendicularity
conditions of a noncollinear triangle, no two can hold simultaneously. -/
theorem exercise_3_11 [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third) :
    let firstSide := lineThrough first second firstSecondDistinct
    let secondSide := lineThrough second third secondThirdDistinct
    let thirdSide := lineThrough first third firstThirdDistinct
    let rightAtFirst := firstSide.Perpendicular thirdSide
    let rightAtSecond := firstSide.Perpendicular secondSide
    let rightAtThird := thirdSide.Perpendicular secondSide
    ¬ (rightAtFirst ∧ rightAtSecond) ∧
      ¬ (rightAtSecond ∧ rightAtThird) ∧
      ¬ (rightAtThird ∧ rightAtFirst) := by
  dsimp only
  rcases triangle_side_pairs_nonparallel first second third
      firstSecondDistinct firstThirdDistinct secondThirdDistinct
      notCollinear with
    ⟨firstSecondNonparallel, secondThirdNonparallel,
      thirdFirstNonparallel⟩
  constructor
  · rintro ⟨rightAtFirst, rightAtSecond⟩
    apply secondThirdNonparallel
    exact Line.parallel_symm (exercise_3_5
      (lineThrough first third firstThirdDistinct)
      (lineThrough first second firstSecondDistinct)
      (lineThrough second third secondThirdDistinct)
      (Line.perpendicular_symm rightAtFirst) rightAtSecond)
  constructor
  · rintro ⟨rightAtSecond, rightAtThird⟩
    apply thirdFirstNonparallel
    exact Line.parallel_symm (exercise_3_5
      (lineThrough first second firstSecondDistinct)
      (lineThrough second third secondThirdDistinct)
      (lineThrough first third firstThirdDistinct)
      rightAtSecond (Line.perpendicular_symm rightAtThird))
  · rintro ⟨rightAtThird, rightAtFirst⟩
    apply firstSecondNonparallel
    exact Line.parallel_symm (exercise_3_5
      (lineThrough second third secondThirdDistinct)
      (lineThrough first third firstThirdDistinct)
      (lineThrough first second firstSecondDistinct)
      (Line.perpendicular_symm rightAtThird)
      (Line.perpendicular_symm rightAtFirst))

/-- Exercise 3.12: a noncollinear triangle cannot have all three sides null.
The visible `2 ≠ 0` premise is the book's standing characteristic boundary. -/
theorem exercise_3_12 [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    ¬ ((lineThrough first second firstSecondDistinct).IsNull ∧
      (lineThrough first third firstThirdDistinct).IsNull ∧
      (lineThrough second third secondThirdDistinct).IsNull) := by
  rintro ⟨firstSideNull, thirdSideNull, secondSideNull⟩
  have firstQuadranceZero : quadrance first second = 0 :=
    (null_line_iff_quadrance_zero first second firstSecondDistinct).1
      firstSideNull
  have thirdQuadranceZero : quadrance first third = 0 :=
    (null_line_iff_quadrance_zero first third firstThirdDistinct).1
      thirdSideNull
  have secondQuadranceZero : quadrance second third = 0 :=
    (null_line_iff_quadrance_zero second third secondThirdDistinct).1
      secondSideNull
  apply notCollinear
  apply (triple_quad_formula first second third twoNonzero).1
  unfold archimedesFunction
  rw [firstQuadranceZero, thirdQuadranceZero, secondQuadranceZero]
  ring1

end DivineProportions
