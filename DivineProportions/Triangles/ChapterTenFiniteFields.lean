import DivineProportions.Algebra.FieldThree
import DivineProportions.Algebra.FieldFive
import DivineProportions.Triangles.ChapterTenExercises

/-!
# Divine Proportions, Exercises 10.10 and 10.11

The two small-field classifications are reduced to finite scalar certificates.
No list of field points, lines, or triangles is constructed.  The `F₅` null
case also makes explicit the boundary in the book's spread-based definition of
similarity: a triangle with two null sides has no vertex at which a spread is
defined.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- An unordered triple with two copies of `repeated` and one copy of
`single`, written as the three possible displayed positions. -/
def RepeatedEntryPattern (repeated single : K)
    (entries : ScalarTriple K) : Prop :=
  (entries.first = repeated ∧ entries.second = repeated ∧
      entries.third = single) ∨
    (entries.first = repeated ∧ entries.second = single ∧
      entries.third = repeated) ∨
    (entries.first = single ∧ entries.second = repeated ∧
      entries.third = repeated)

omit [RFAP.ExplicitField K] in
theorem sameEntries_of_repeatedEntryPattern
    {repeated single : K} {left right : ScalarTriple K}
    (leftPattern : RepeatedEntryPattern repeated single left)
    (rightPattern : RepeatedEntryPattern repeated single right) :
    ScalarTriple.SameEntries left right := by
  rcases leftPattern with leftFirst | leftSecond | leftThird
  · rcases leftFirst with ⟨leftOne, leftTwo, leftThree⟩
    rcases rightPattern with rightFirst | rightSecond | rightThird
    · rcases rightFirst with ⟨rightOne, rightTwo, rightThree⟩
      apply ScalarTriple.SameEntries.abc
      · exact leftOne.trans rightOne.symm
      · exact leftTwo.trans rightTwo.symm
      · exact leftThree.trans rightThree.symm
    · rcases rightSecond with ⟨rightOne, rightTwo, rightThree⟩
      apply ScalarTriple.SameEntries.acb
      · exact leftOne.trans rightOne.symm
      · exact leftTwo.trans rightThree.symm
      · exact leftThree.trans rightTwo.symm
    · rcases rightThird with ⟨rightOne, rightTwo, rightThree⟩
      apply ScalarTriple.SameEntries.bca
      · exact leftOne.trans rightTwo.symm
      · exact leftTwo.trans rightThree.symm
      · exact leftThree.trans rightOne.symm
  · rcases leftSecond with ⟨leftOne, leftTwo, leftThree⟩
    rcases rightPattern with rightFirst | rightSecond | rightThird
    · rcases rightFirst with ⟨rightOne, rightTwo, rightThree⟩
      apply ScalarTriple.SameEntries.acb
      · exact leftOne.trans rightOne.symm
      · exact leftTwo.trans rightThree.symm
      · exact leftThree.trans rightTwo.symm
    · rcases rightSecond with ⟨rightOne, rightTwo, rightThree⟩
      apply ScalarTriple.SameEntries.abc
      · exact leftOne.trans rightOne.symm
      · exact leftTwo.trans rightTwo.symm
      · exact leftThree.trans rightThree.symm
    · rcases rightThird with ⟨rightOne, rightTwo, rightThree⟩
      apply ScalarTriple.SameEntries.bac
      · exact leftOne.trans rightTwo.symm
      · exact leftTwo.trans rightOne.symm
      · exact leftThree.trans rightThree.symm
  · rcases leftThird with ⟨leftOne, leftTwo, leftThree⟩
    rcases rightPattern with rightFirst | rightSecond | rightThird
    · rcases rightFirst with ⟨rightOne, rightTwo, rightThree⟩
      apply ScalarTriple.SameEntries.cab
      · exact leftOne.trans rightThree.symm
      · exact leftTwo.trans rightOne.symm
      · exact leftThree.trans rightTwo.symm
    · rcases rightSecond with ⟨rightOne, rightTwo, rightThree⟩
      apply ScalarTriple.SameEntries.bca
      · exact leftOne.trans rightTwo.symm
      · exact leftTwo.trans rightThree.symm
      · exact leftThree.trans rightOne.symm
    · rcases rightThird with ⟨rightOne, rightTwo, rightThree⟩
      apply ScalarTriple.SameEntries.abc
      · exact leftOne.trans rightOne.symm
      · exact leftTwo.trans rightTwo.symm
      · exact leftThree.trans rightThree.symm

namespace NonNullTriangle

variable [DecidableEq K]

/-- A right isosceles vertex at the first displayed point. -/
def RightIsoscelesAtFirst (triangle : NonNullTriangle K) : Prop :=
  triangle.quadrances.second = triangle.quadrances.third ∧
    (lineThrough triangle.second triangle.first
        triangle.firstSecondDistinct.symm).Perpendicular
      (lineThrough triangle.third triangle.first
        triangle.firstThirdDistinct.symm)

/-- A right isosceles vertex at the second displayed point. -/
def RightIsoscelesAtSecond (triangle : NonNullTriangle K) : Prop :=
  triangle.quadrances.first = triangle.quadrances.third ∧
    (lineThrough triangle.first triangle.second
        triangle.firstSecondDistinct).Perpendicular
      (lineThrough triangle.third triangle.second
        triangle.secondThirdDistinct.symm)

/-- A right isosceles vertex at the third displayed point. -/
def RightIsoscelesAtThird (triangle : NonNullTriangle K) : Prop :=
  triangle.quadrances.first = triangle.quadrances.second ∧
    (lineThrough triangle.first triangle.third
        triangle.firstThirdDistinct).Perpendicular
      (lineThrough triangle.second triangle.third
        triangle.secondThirdDistinct)

/-- The three finite choices of a right isosceles vertex. -/
def IsRightIsosceles (triangle : NonNullTriangle K) : Prop :=
  triangle.RightIsoscelesAtFirst ∨
    triangle.RightIsoscelesAtSecond ∨
    triangle.RightIsoscelesAtThird

end NonNullTriangle

private theorem first_second_distinct_of_not_collinear
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (notCollinear : ¬ Collinear first second third) : first ≠ second := by
  intro equalPoints
  apply notCollinear
  apply (collinear_iff_pointDeterminant_eq_zero first second third).2
  rw [equalPoints]
  unfold pointDeterminant
  ring1

private theorem first_third_distinct_of_not_collinear
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (notCollinear : ¬ Collinear first second third) : first ≠ third := by
  intro equalPoints
  apply notCollinear
  apply (collinear_iff_pointDeterminant_eq_zero first second third).2
  rw [equalPoints]
  unfold pointDeterminant
  ring1

private theorem second_third_distinct_of_not_collinear
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (notCollinear : ¬ Collinear first second third) : second ≠ third := by
  intro equalPoints
  apply notCollinear
  apply (collinear_iff_pointDeterminant_eq_zero first second third).2
  rw [equalPoints]
  unfold pointDeterminant
  ring1

namespace FieldThree

theorem quadrance_ne_zero_of_distinct
    (first second : Point Element) (distinct : first ≠ second) :
    quadrance first second ≠ 0 := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  unfold quadrance
  decide +revert

/-- Every source triangle over `F₃` is automatically non-null. -/
def nonNullTriangle (first second third : Point Element)
    (notCollinear : ¬ Collinear first second third) :
    NonNullTriangle Element where
  first := first
  second := second
  third := third
  notCollinear := notCollinear
  firstSecondDistinct :=
    first_second_distinct_of_not_collinear first second third notCollinear
  firstThirdDistinct :=
    first_third_distinct_of_not_collinear first second third notCollinear
  secondThirdDistinct :=
    second_third_distinct_of_not_collinear first second third notCollinear
  firstSecondNonNull := by
    intro nullSide
    exact quadrance_ne_zero_of_distinct first second
      (first_second_distinct_of_not_collinear first second third notCollinear)
      ((null_line_iff_quadrance_zero first second
        (first_second_distinct_of_not_collinear first second third
          notCollinear)).1 nullSide)
  firstThirdNonNull := by
    intro nullSide
    exact quadrance_ne_zero_of_distinct first third
      (first_third_distinct_of_not_collinear first second third notCollinear)
      ((null_line_iff_quadrance_zero first third
        (first_third_distinct_of_not_collinear first second third
          notCollinear)).1 nullSide)
  secondThirdNonNull := by
    intro nullSide
    exact quadrance_ne_zero_of_distinct second third
      (second_third_distinct_of_not_collinear first second third notCollinear)
      ((null_line_iff_quadrance_zero second third
        (second_third_distinct_of_not_collinear first second third
          notCollinear)).1 nullSide)

private theorem quadrance_pattern
    (q₁ q₂ q₃ : Element)
    (firstNonzero : q₁ ≠ 0) (secondNonzero : q₂ ≠ 0)
    (thirdNonzero : q₃ ≠ 0)
    (areaNonzero : archimedesFunction q₁ q₂ q₃ ≠ 0) :
    (q₂ = q₃ ∧ q₂ + q₃ = q₁) ∨
      (q₁ = q₃ ∧ q₁ + q₃ = q₂) ∨
      (q₁ = q₂ ∧ q₁ + q₂ = q₃) := by
  decide +revert

private theorem scalar_spread_pattern
    (q₁ q₂ q₃ s₁ s₂ s₃ : Element)
    (firstNonzero : q₁ ≠ 0) (secondNonzero : q₂ ≠ 0)
    (thirdNonzero : q₃ ≠ 0)
    (areaNonzero : archimedesFunction q₁ q₂ q₃ ≠ 0)
    (firstProduct :
      archimedesFunction q₁ q₂ q₃ = 4 * q₂ * q₃ * s₁)
    (secondProduct :
      archimedesFunction q₁ q₂ q₃ = 4 * q₁ * q₃ * s₂)
    (thirdProduct :
      archimedesFunction q₁ q₂ q₃ = 4 * q₁ * q₂ * s₃) :
    RepeatedEntryPattern (2 : Element) 1 ⟨s₁, s₂, s₃⟩ := by
  unfold RepeatedEntryPattern
  decide +revert

theorem spread_pattern (triangle : NonNullTriangle Element) :
    RepeatedEntryPattern (2 : Element) 1 triangle.spreads := by
  have areaNonzero :
      quadrea triangle.first triangle.second triangle.third ≠ 0 :=
    (quadrea_ne_zero_iff_not_collinear triangle.first triangle.second
      triangle.third (by decide : (2 : Element) ≠ 0)).2
      triangle.notCollinear
  have products := triangle.quadrea_spread_products
  exact scalar_spread_pattern triangle.quadrances.first
    triangle.quadrances.second triangle.quadrances.third
    triangle.spreads.first triangle.spreads.second triangle.spreads.third
    triangle.firstQuadranceNonzero triangle.secondQuadranceNonzero
    triangle.thirdQuadranceNonzero areaNonzero products.1 products.2.1
    products.2.2

/-- Exercise 10.10: any two triangles over `F₃` have the same unordered
spread triple `{2,2,1}`. -/
theorem exercise_10_10_similar
    (left right : NonNullTriangle Element) : left.Similar right :=
  sameEntries_of_repeatedEntryPattern (spread_pattern left)
    (spread_pattern right)

/-- Exercise 10.10: every triangle over `F₃` has one displayed vertex which
is simultaneously right and isosceles. -/
theorem exercise_10_10_right_isosceles
    (triangle : NonNullTriangle Element) : triangle.IsRightIsosceles := by
  have areaNonzero :
      quadrea triangle.first triangle.second triangle.third ≠ 0 :=
    (quadrea_ne_zero_iff_not_collinear triangle.first triangle.second
      triangle.third (by decide : (2 : Element) ≠ 0)).2
      triangle.notCollinear
  have pattern := quadrance_pattern triangle.quadrances.first
    triangle.quadrances.second triangle.quadrances.third
    triangle.firstQuadranceNonzero triangle.secondQuadranceNonzero
    triangle.thirdQuadranceNonzero areaNonzero
  rcases pattern with atFirst | atSecond | atThird
  · apply Or.inl
    refine ⟨atFirst.1, ?_⟩
    apply (pythagoras_iff_perpendicular triangle.second triangle.third
      triangle.first triangle.firstSecondDistinct.symm
      triangle.firstThirdDistinct.symm
      (by decide : (2 : Element) ≠ 0)).1
    calc
      quadrance triangle.third triangle.first +
          quadrance triangle.second triangle.first =
        quadrance triangle.first triangle.third +
          quadrance triangle.first triangle.second := by
            rw [quadrance_symm triangle.third triangle.first,
              quadrance_symm triangle.second triangle.first]
      _ = triangle.quadrances.second + triangle.quadrances.third := rfl
      _ = triangle.quadrances.first := atFirst.2
  · apply Or.inr
    apply Or.inl
    refine ⟨atSecond.1, ?_⟩
    apply (pythagoras_iff_perpendicular triangle.first triangle.third
      triangle.second triangle.firstSecondDistinct
      triangle.secondThirdDistinct.symm
      (by decide : (2 : Element) ≠ 0)).1
    calc
      quadrance triangle.third triangle.second +
          quadrance triangle.first triangle.second =
        quadrance triangle.second triangle.third +
          quadrance triangle.first triangle.second := by
            rw [quadrance_symm triangle.third triangle.second]
      _ = triangle.quadrances.first + triangle.quadrances.third := rfl
      _ = triangle.quadrances.second := atSecond.2
  · apply Or.inr
    apply Or.inr
    refine ⟨atThird.1, ?_⟩
    exact (pythagoras_iff_perpendicular triangle.first triangle.second
      triangle.third triangle.firstThirdDistinct
      triangle.secondThirdDistinct (by decide : (2 : Element) ≠ 0)).1
      atThird.2

/-- The complete two-triangle form of Exercise 10.10. -/
theorem exercise_10_10 (left right : NonNullTriangle Element) :
    left.Similar right ∧ left.IsRightIsosceles ∧ right.IsRightIsosceles :=
  ⟨exercise_10_10_similar left right,
    exercise_10_10_right_isosceles left,
    exercise_10_10_right_isosceles right⟩

end FieldThree

namespace FieldFive

private theorem quadrea_values
    (first second third : Point Element)
    (notCollinear : ¬ Collinear first second third) :
    quadrea first second third = 1 ∨ quadrea first second third = 4 := by
  have determinantNonzero : pointDeterminant first second third ≠ 0 := by
    intro determinantZero
    exact notCollinear
      ((collinear_iff_pointDeterminant_eq_zero first second third).2
        determinantZero)
  rcases square_eq_one_or_four_of_nonzero
      (pointDeterminant first second third) determinantNonzero with
    squareOne | squareFour
  · apply Or.inr
    rw [quadrea_coordinate_formula, squareOne]
    decide
  · apply Or.inl
    rw [quadrea_coordinate_formula, squareFour]
    decide

private theorem scalar_isosceles
    (q₁ q₂ q₃ : Element)
    (firstNonzero : q₁ ≠ 0) (secondNonzero : q₂ ≠ 0)
    (thirdNonzero : q₃ ≠ 0)
    (areaValue : archimedesFunction q₁ q₂ q₃ = 1 ∨
      archimedesFunction q₁ q₂ q₃ = 4) :
    q₁ = q₂ ∨ q₁ = q₃ ∨ q₂ = q₃ := by
  decide +revert

private theorem scalar_spread_pattern
    (q₁ q₂ q₃ s₁ s₂ s₃ : Element)
    (firstNonzero : q₁ ≠ 0) (secondNonzero : q₂ ≠ 0)
    (thirdNonzero : q₃ ≠ 0)
    (areaValue : archimedesFunction q₁ q₂ q₃ = 1 ∨
      archimedesFunction q₁ q₂ q₃ = 4)
    (firstProduct :
      archimedesFunction q₁ q₂ q₃ = 4 * q₂ * q₃ * s₁)
    (secondProduct :
      archimedesFunction q₁ q₂ q₃ = 4 * q₁ * q₃ * s₂)
    (thirdProduct :
      archimedesFunction q₁ q₂ q₃ = 4 * q₁ * q₂ * s₃) :
    RepeatedEntryPattern (3 : Element) 1 ⟨s₁, s₂, s₃⟩ := by
  unfold RepeatedEntryPattern
  decide +revert

private theorem triangle_area_values (triangle : NonNullTriangle Element) :
    archimedesFunction triangle.quadrances.first
        triangle.quadrances.second triangle.quadrances.third = 1 ∨
      archimedesFunction triangle.quadrances.first
        triangle.quadrances.second triangle.quadrances.third = 4 := by
  exact quadrea_values triangle.first triangle.second triangle.third
    triangle.notCollinear

theorem spread_pattern (triangle : NonNullTriangle Element) :
    RepeatedEntryPattern (3 : Element) 1 triangle.spreads := by
  have products := triangle.quadrea_spread_products
  exact scalar_spread_pattern triangle.quadrances.first
    triangle.quadrances.second triangle.quadrances.third
    triangle.spreads.first triangle.spreads.second triangle.spreads.third
    triangle.firstQuadranceNonzero triangle.secondQuadranceNonzero
    triangle.thirdQuadranceNonzero (triangle_area_values triangle)
    products.1 products.2.1 products.2.2

/-- Exercise 10.11: every non-null triangle over `F₅` is isosceles. -/
theorem exercise_10_11_isosceles (triangle : NonNullTriangle Element) :
    triangle.quadrances.first = triangle.quadrances.second ∨
      triangle.quadrances.first = triangle.quadrances.third ∨
      triangle.quadrances.second = triangle.quadrances.third :=
  scalar_isosceles triangle.quadrances.first triangle.quadrances.second
    triangle.quadrances.third triangle.firstQuadranceNonzero
    triangle.secondQuadranceNonzero triangle.thirdQuadranceNonzero
    (triangle_area_values triangle)

/-- Exercise 10.11: any two non-null triangles over `F₅` have the same
unordered spread triple `{3,3,1}`. -/
theorem exercise_10_11_similar
    (left right : NonNullTriangle Element) : left.Similar right :=
  sameEntries_of_repeatedEntryPattern (spread_pattern left)
    (spread_pattern right)

/-- The complete non-null part of Exercise 10.11. -/
theorem exercise_10_11_nonNull
    (left right : NonNullTriangle Element) :
    left.Similar right ∧
      (left.quadrances.first = left.quadrances.second ∨
        left.quadrances.first = left.quadrances.third ∨
        left.quadrances.second = left.quadrances.third) ∧
      (right.quadrances.first = right.quadrances.second ∨
        right.quadrances.first = right.quadrances.third ∨
        right.quadrances.second = right.quadrances.third) :=
  ⟨exercise_10_11_similar left right,
    exercise_10_11_isosceles left, exercise_10_11_isosceles right⟩

/-- A null triangle with exactly the first opposite side null.  The other two
sides are retained as explicit nonzero quadrances, so the spread at the first
vertex is the sole vertex spread defined by the book. -/
structure SinglyNullAtFirst where
  first : Point Element
  second : Point Element
  third : Point Element
  notCollinear : ¬ Collinear first second third
  firstQuadranceZero : quadrance second third = 0
  secondQuadranceNonzero : quadrance first third ≠ 0
  thirdQuadranceNonzero : quadrance first second ≠ 0

namespace SinglyNullAtFirst

theorem firstSecondDistinct (triangle : SinglyNullAtFirst) :
    triangle.first ≠ triangle.second := by
  intro equalPoints
  apply triangle.thirdQuadranceNonzero
  calc
    quadrance triangle.first triangle.second =
        quadrance triangle.second triangle.second := by rw [equalPoints]
    _ = 0 := quadrance_self triangle.second

theorem firstThirdDistinct (triangle : SinglyNullAtFirst) :
    triangle.first ≠ triangle.third := by
  intro equalPoints
  apply triangle.secondQuadranceNonzero
  calc
    quadrance triangle.first triangle.third =
        quadrance triangle.third triangle.third := by rw [equalPoints]
    _ = 0 := quadrance_self triangle.third

theorem firstSecondNonNull (triangle : SinglyNullAtFirst) :
    ¬ (lineThrough triangle.first triangle.second
      triangle.firstSecondDistinct).IsNull := by
  intro nullSide
  exact triangle.thirdQuadranceNonzero
    ((null_line_iff_quadrance_zero triangle.first triangle.second
      triangle.firstSecondDistinct).1 nullSide)

theorem firstThirdNonNull (triangle : SinglyNullAtFirst) :
    ¬ (lineThrough triangle.first triangle.third
      triangle.firstThirdDistinct).IsNull := by
  intro nullSide
  exact triangle.secondQuadranceNonzero
    ((null_line_iff_quadrance_zero triangle.first triangle.third
      triangle.firstThirdDistinct).1 nullSide)

theorem secondFirstNonNull (triangle : SinglyNullAtFirst) :
    ¬ (lineThrough triangle.second triangle.first
      triangle.firstSecondDistinct.symm).IsNull := by
  intro nullSide
  apply triangle.thirdQuadranceNonzero
  calc
    quadrance triangle.first triangle.second =
        quadrance triangle.second triangle.first :=
      quadrance_symm triangle.first triangle.second
    _ = 0 :=
      (null_line_iff_quadrance_zero triangle.second triangle.first
        triangle.firstSecondDistinct.symm).1 nullSide

theorem thirdFirstNonNull (triangle : SinglyNullAtFirst) :
    ¬ (lineThrough triangle.third triangle.first
      triangle.firstThirdDistinct.symm).IsNull := by
  intro nullSide
  apply triangle.secondQuadranceNonzero
  calc
    quadrance triangle.first triangle.third =
        quadrance triangle.third triangle.first :=
      quadrance_symm triangle.first triangle.third
    _ = 0 :=
      (null_line_iff_quadrance_zero triangle.third triangle.first
        triangle.firstThirdDistinct.symm).1 nullSide

/-- The only spread defined at a vertex of this singly-null triangle. -/
def oppositeSpread (triangle : SinglyNullAtFirst) : Element :=
  spread
    (lineThrough triangle.second triangle.first
      triangle.firstSecondDistinct.symm)
    (lineThrough triangle.third triangle.first
      triangle.firstThirdDistinct.symm)
    triangle.secondFirstNonNull triangle.thirdFirstNonNull

private theorem scalar_opposite_spread
    (q₂ q₃ s : Element)
    (secondNonzero : q₂ ≠ 0) (thirdNonzero : q₃ ≠ 0)
    (areaValue : archimedesFunction 0 q₂ q₃ = 1 ∨
      archimedesFunction 0 q₂ q₃ = 4)
    (areaProduct : archimedesFunction 0 q₂ q₃ = 4 * q₂ * q₃ * s) :
    s = 1 ∨ s = 3 := by
  decide +revert

/-- Corrected null part of Exercise 10.11: for a triangle with exactly one
null side, the sole defined vertex spread gives exactly the two possible
types `1` and `3`. -/
theorem oppositeSpread_eq_one_or_three (triangle : SinglyNullAtFirst) :
    triangle.oppositeSpread = 1 ∨ triangle.oppositeSpread = 3 := by
  have geometricAreaValues := quadrea_values triangle.first triangle.second
    triangle.third triangle.notCollinear
  have scalarAreaEqualsGeometric :
      archimedesFunction 0
          (quadrance triangle.third triangle.first)
          (quadrance triangle.second triangle.first) =
        quadrea triangle.first triangle.second triangle.third := by
    unfold quadrea
    rw [triangle.firstQuadranceZero,
      quadrance_symm triangle.third triangle.first,
      quadrance_symm triangle.second triangle.first]
  have areaValues :
      archimedesFunction 0
          (quadrance triangle.third triangle.first)
          (quadrance triangle.second triangle.first) = 1 ∨
        archimedesFunction 0
          (quadrance triangle.third triangle.first)
          (quadrance triangle.second triangle.first) = 4 := by
    rcases geometricAreaValues with areaOne | areaFour
    · exact Or.inl (scalarAreaEqualsGeometric.trans areaOne)
    · exact Or.inr (scalarAreaEqualsGeometric.trans areaFour)
  have reversedProduct := quadrea_spread triangle.second triangle.third
    triangle.first triangle.firstSecondDistinct.symm
    triangle.firstThirdDistinct.symm
    triangle.secondFirstNonNull triangle.thirdFirstNonNull
  have areaProduct :
      archimedesFunction 0
          (quadrance triangle.third triangle.first)
          (quadrance triangle.second triangle.first) =
        4 * quadrance triangle.third triangle.first *
          quadrance triangle.second triangle.first *
            triangle.oppositeSpread := by
    calc
      archimedesFunction 0
          (quadrance triangle.third triangle.first)
          (quadrance triangle.second triangle.first) =
        quadrea triangle.first triangle.second triangle.third :=
          scalarAreaEqualsGeometric
      _ = quadrea triangle.second triangle.third triangle.first :=
        (quadrea_cyclic triangle.first triangle.second triangle.third).symm
      _ = 4 * quadrance triangle.third triangle.first *
          quadrance triangle.second triangle.first *
            triangle.oppositeSpread := reversedProduct
  have secondReversedNonzero :
      quadrance triangle.third triangle.first ≠ 0 := by
    rw [quadrance_symm triangle.third triangle.first]
    exact triangle.secondQuadranceNonzero
  have thirdReversedNonzero :
      quadrance triangle.second triangle.first ≠ 0 := by
    rw [quadrance_symm triangle.second triangle.first]
    exact triangle.thirdQuadranceNonzero
  exact scalar_opposite_spread
    (quadrance triangle.third triangle.first)
    (quadrance triangle.second triangle.first) triangle.oppositeSpread
    secondReversedNonzero thirdReversedNonzero areaValues areaProduct

end SinglyNullAtFirst

private theorem not_collinear_swap_first_second
    {first second third : Point Element}
    (notCollinear : ¬ Collinear first second third) :
    ¬ Collinear second first third := by
  intro swappedCollinear
  apply notCollinear
  apply (collinear_iff_pointDeterminant_eq_zero first second third).2
  have swappedZero :=
    pointDeterminant_eq_zero_of_collinear swappedCollinear
  calc
    pointDeterminant first second third =
        -pointDeterminant second first third := by
      unfold pointDeterminant
      ring1
    _ = 0 := by rw [swappedZero]; exact neg_zero

private theorem not_collinear_cyclic_right
    {first second third : Point Element}
    (notCollinear : ¬ Collinear first second third) :
    ¬ Collinear third first second := by
  intro cyclicCollinear
  apply notCollinear
  apply (collinear_iff_pointDeterminant_eq_zero first second third).2
  have cyclicZero :=
    pointDeterminant_eq_zero_of_collinear cyclicCollinear
  calc
    pointDeterminant first second third =
        pointDeterminant third first second := by
      unfold pointDeterminant
      ring1
    _ = 0 := cyclicZero

/-- Every `F₅` triangle with exactly one null side can be relabelled by one of
three displayed permutations so that the null side is first.  Its sole
defined vertex spread is then one of the two values `1` and `3`. -/
theorem exercise_10_11_singlyNull
    (first second third : Point Element)
    (notCollinear : ¬ Collinear first second third)
    (exactlyOneNull :
      (quadrance second third = 0 ∧
        quadrance first third ≠ 0 ∧ quadrance first second ≠ 0) ∨
      (quadrance first third = 0 ∧
        quadrance second third ≠ 0 ∧ quadrance first second ≠ 0) ∨
      (quadrance first second = 0 ∧
        quadrance second third ≠ 0 ∧ quadrance first third ≠ 0)) :
    ∃ normalized : SinglyNullAtFirst,
      ((normalized.first = first ∧ normalized.second = second ∧
          normalized.third = third) ∨
        (normalized.first = second ∧ normalized.second = first ∧
          normalized.third = third) ∨
        (normalized.first = third ∧ normalized.second = first ∧
          normalized.third = second)) ∧
      (normalized.oppositeSpread = 1 ∨ normalized.oppositeSpread = 3) := by
  rcases exactlyOneNull with firstNull | secondOrThirdNull
  · let normalized : SinglyNullAtFirst :=
      { first := first
        second := second
        third := third
        notCollinear := notCollinear
        firstQuadranceZero := firstNull.1
        secondQuadranceNonzero := firstNull.2.1
        thirdQuadranceNonzero := firstNull.2.2 }
    exact ⟨normalized, Or.inl ⟨rfl, rfl, rfl⟩,
      normalized.oppositeSpread_eq_one_or_three⟩
  · rcases secondOrThirdNull with secondNull | thirdNull
    · have thirdReversedNonzero : quadrance second first ≠ 0 := by
        rw [quadrance_symm second first]
        exact secondNull.2.2
      let normalized : SinglyNullAtFirst :=
        { first := second
          second := first
          third := third
          notCollinear := not_collinear_swap_first_second notCollinear
          firstQuadranceZero := secondNull.1
          secondQuadranceNonzero := secondNull.2.1
          thirdQuadranceNonzero := thirdReversedNonzero }
      exact ⟨normalized, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩),
        normalized.oppositeSpread_eq_one_or_three⟩
    · have secondReversedNonzero : quadrance third second ≠ 0 := by
        rw [quadrance_symm third second]
        exact thirdNull.2.1
      have thirdReversedNonzero : quadrance third first ≠ 0 := by
        rw [quadrance_symm third first]
        exact thirdNull.2.2
      let normalized : SinglyNullAtFirst :=
        { first := third
          second := first
          third := second
          notCollinear := not_collinear_cyclic_right notCollinear
          firstQuadranceZero := thirdNull.1
          secondQuadranceNonzero := secondReversedNonzero
          thirdQuadranceNonzero := thirdReversedNonzero }
      exact ⟨normalized, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩),
        normalized.oppositeSpread_eq_one_or_three⟩

end FieldFive

end DivineProportions
