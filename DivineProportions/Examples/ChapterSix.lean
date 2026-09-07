import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Trigonometry.VertexBisector
import DivineProportions.Algebra.FieldEleven
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Chapter 6 worked examples

The numerical examples use the project's executable constructive rational
field.  Every equality below reduces to finite integer arithmetic; no decimal
or completed-real interpretation is involved.
-/

namespace DivineProportions

namespace ChapterSixExamples

abbrev Rational := RFAP.ConstructiveFraction.Rational

private theorem rational_two_nonzero : (2 : Rational) ≠ 0 := by decide

private theorem rational_natCast_nonzero {value : Nat}
    (valueNonzero : value ≠ 0) : (value : Rational) ≠ 0 := by
  intro castZero
  exact valueNonzero
    (RFAP.ConstructiveFraction.natCast_injective_direct castZero)

private theorem rational_ten_nonzero : (10 : Rational) ≠ 0 :=
  rational_natCast_nonzero (by decide)

private theorem rational_fifty_nonzero : (50 : Rational) ≠ 0 :=
  rational_natCast_nonzero (by decide)

private theorem ratio_eq_of_cross_product
    {K : Type*} [RFAP.ExplicitField K]
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ rightNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
            rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

namespace ExampleSixOne

/-- Example 6.1's exact quadrea and three displayed spread quotients.  The
book's decimal-field calculation is retained entirely in the constructive
rationals. -/
theorem example_6_1 :
    archimedesFunction (16 : Rational) 36 9 = 455 ∧
      (455 : Rational) / (4 * 36 * 9) = 455 / 1296 ∧
      (455 : Rational) / (4 * 16 * 9) = 455 / 576 ∧
      (455 : Rational) / (4 * 16 * 36) = 455 / 2304 := by
  constructor
  · unfold archimedesFunction
    ring1
  constructor
  · rw [show (4 : Rational) * 36 * 9 = 1296 by ring1]
  constructor
  · rw [show (4 : Rational) * 16 * 9 = 576 by ring1]
  · rw [show (4 : Rational) * 16 * 36 = 2304 by ring1]

end ExampleSixOne

namespace ExampleSixTwo

/-- Example 6.2: no constructive-rational triangle has quadrances
`16,36,9`, because its forced quadrea `455` is not a rational square. -/
theorem example_6_2 :
    ¬ HasTriangleQuadrances (16 : Rational) 36 9 := by
  rintro ⟨first, second, third, _notCollinear,
    firstQuadrance, secondQuadrance, thirdQuadrance⟩
  apply RFAP.ConstructiveFraction.square_ne_455
    (2 * pointDeterminant first second third)
  calc
    (2 * pointDeterminant first second third) ^ 2 =
        4 * pointDeterminant first second third ^ 2 := by ring1
    _ = quadrea first second third :=
      (quadrea_coordinate_formula first second third).symm
    _ = archimedesFunction (16 : Rational) 36 9 := by
      unfold quadrea
      rw [firstQuadrance, secondQuadrance, thirdQuadrance]
    _ = 455 := by
      unfold archimedesFunction
      ring1

end ExampleSixTwo

namespace ExampleSixThree

abbrev F₁₁ := FieldEleven.Element

/-- A concrete first vertex realizing the existence assertion in Example
6.3. -/
def firstPoint : Point F₁₁ := ⟨0, 5⟩

/-- A concrete second vertex realizing the existence assertion in Example
6.3. -/
def secondPoint : Point F₁₁ := ⟨2, 1⟩

/-- The origin is the third vertex of the displayed realization. -/
def thirdPoint : Point F₁₁ := ⟨0, 0⟩

private theorem firstSecondDistinct : firstPoint ≠ secondPoint := by decide

private theorem firstThirdDistinct : firstPoint ≠ thirdPoint := by decide

private theorem secondThirdDistinct : secondPoint ≠ thirdPoint := by decide

private theorem firstSecondNonNull :
    ¬ (lineThrough firstPoint secondPoint firstSecondDistinct).IsNull := by
  unfold Line.IsNull lineThrough firstPoint secondPoint
  decide

private theorem firstThirdNonNull :
    ¬ (lineThrough firstPoint thirdPoint firstThirdDistinct).IsNull := by
  unfold Line.IsNull lineThrough firstPoint thirdPoint
  decide

private theorem secondThirdNonNull :
    ¬ (lineThrough secondPoint thirdPoint secondThirdDistinct).IsNull := by
  unfold Line.IsNull lineThrough secondPoint thirdPoint
  decide

private theorem firstSecondReversedNonNull :
    ¬ (lineThrough secondPoint firstPoint firstSecondDistinct.symm).IsNull := by
  unfold Line.IsNull lineThrough firstPoint secondPoint
  decide

private theorem firstThirdReversedNonNull :
    ¬ (lineThrough thirdPoint firstPoint firstThirdDistinct.symm).IsNull := by
  unfold Line.IsNull lineThrough firstPoint thirdPoint
  decide

private theorem secondThirdReversedNonNull :
    ¬ (lineThrough thirdPoint secondPoint secondThirdDistinct.symm).IsNull := by
  unfold Line.IsNull lineThrough secondPoint thirdPoint
  decide

theorem triangle_exists : HasTriangleQuadrances (5 : F₁₁) 3 9 := by
  refine ⟨firstPoint, secondPoint, thirdPoint, ?_, by decide,
    by decide, by decide⟩
  intro collinear
  have determinantZero :=
    (collinear_iff_pointDeterminant_eq_zero
      firstPoint secondPoint thirdPoint).1 collinear
  have determinantNonzero :
      pointDeterminant firstPoint secondPoint thirdPoint ≠ 0 := by
    unfold pointDeterminant firstPoint secondPoint thirdPoint
    decide
  exact determinantNonzero determinantZero

/-- Example 6.3's exact characteristic-eleven quadrea and three spread
values, together with an explicit triangle realizing its quadrances. -/
theorem example_6_3 :
    archimedesFunction (5 : F₁₁) 3 9 = 4 ∧
      spread
          (lineThrough firstPoint secondPoint firstSecondDistinct)
          (lineThrough firstPoint thirdPoint firstThirdDistinct)
          firstSecondNonNull firstThirdNonNull = 9 ∧
      spread
          (lineThrough secondPoint firstPoint firstSecondDistinct.symm)
          (lineThrough secondPoint thirdPoint secondThirdDistinct)
          firstSecondReversedNonNull secondThirdNonNull = 1 ∧
      spread
          (lineThrough thirdPoint firstPoint firstThirdDistinct.symm)
          (lineThrough thirdPoint secondPoint secondThirdDistinct.symm)
          firstThirdReversedNonNull secondThirdReversedNonNull = 3 ∧
      HasTriangleQuadrances (5 : F₁₁) 3 9 := by
  refine ⟨by decide, ?_, ?_, ?_, triangle_exists⟩
  · unfold spread lineNorm lineThrough firstPoint secondPoint thirdPoint
    decide
  · unfold spread lineNorm lineThrough firstPoint secondPoint thirdPoint
    decide
  · unfold spread lineNorm lineThrough firstPoint secondPoint thirdPoint
    decide

end ExampleSixThree

namespace ExampleSixFour

/-- Example 6.4 over any requested finite field fragment carrying an element
`i` with `i²=-1`.  This records all printed complex arithmetic without
introducing a completed complex carrier. -/
theorem example_6_4 {K : Type*} [RFAP.ExplicitField K] [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1) (twoNonzero : (2 : K) ≠ 0) :
    archimedesFunction (1 : K) 2 i = 6 * i ∧
      archimedesFunction (1 : K) 2 i / (4 * 2 * i) = 3 / 4 ∧
      archimedesFunction (1 : K) 2 i / (4 * 1 * i) = 3 / 2 ∧
      archimedesFunction (1 : K) 2 i / (4 * 1 * 2) = 3 * i / 4 := by
  have iNonzero : i ≠ 0 := by
    intro iZero
    have negativeOneZero : (-1 : K) = 0 := by
      calc
        (-1 : K) = i ^ 2 := iSquare.symm
        _ = 0 := by rw [iZero]; ring1
    have oneNonzero : (1 : K) ≠ 0 := one_ne_zero
    apply oneNonzero
    calc
      (1 : K) = -(-1) := by ring1
      _ = 0 := by rw [negativeOneZero]; ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    have fourAsProduct : (4 : K) = 2 * 2 := by ring1
    rw [fourAsProduct]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have firstDenominatorNonzero : (4 : K) * 2 * i ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero fourNonzero twoNonzero) iNonzero
  have secondDenominatorNonzero : (4 : K) * 1 * i ≠ 0 := by
    simpa only [mul_one] using
      RFAP.ExplicitField.mul_ne_zero fourNonzero iNonzero
  have thirdDenominatorNonzero : (4 : K) * 1 * 2 ≠ 0 := by
    simpa only [mul_one] using
      RFAP.ExplicitField.mul_ne_zero fourNonzero twoNonzero
  have areaFormula : archimedesFunction (1 : K) 2 i = 6 * i := by
    calc
      archimedesFunction (1 : K) 2 i = 6 * i - (1 + i ^ 2) := by
        unfold archimedesFunction
        ring1
      _ = 6 * i := by rw [iSquare]; ring1
  refine ⟨areaFormula, ?_, ?_, ?_⟩
  · apply ratio_eq_of_cross_product firstDenominatorNonzero fourNonzero
    rw [areaFormula]
    ring1
  · apply ratio_eq_of_cross_product secondDenominatorNonzero twoNonzero
    rw [areaFormula]
    ring1
  · apply ratio_eq_of_cross_product thirdDenominatorNonzero fourNonzero
    rw [areaFormula]
    ring1

end ExampleSixFour

namespace ExampleSixFive

/-- Example 6.5's first line `⟨2 : 1 : -1⟩`. -/
def first : Line Rational where
  a := 2
  b := 1
  c := -1
  direction_nonzero := Or.inl (by decide)

/-- Example 6.5's second line `⟨11 : 2 : -4⟩`. -/
def second : Line Rational where
  a := 11
  b := 2
  c := -4
  direction_nonzero := Or.inl (by decide)

/-- The first displayed book bisector `⟨1 : -3 : 1⟩`. -/
def firstBisector : Line Rational where
  a := 1
  b := -3
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The second displayed book bisector `⟨21 : 7 : -9⟩`. -/
def secondBisector : Line Rational where
  a := 21
  b := 7
  c := -9
  direction_nonzero := Or.inl (by decide)

theorem first_nonNull : ¬ first.IsNull := by
  unfold Line.IsNull first
  decide

theorem second_nonNull : ¬ second.IsNull := by
  unfold Line.IsNull second
  decide

theorem not_parallel : ¬ first.Parallel second := by
  unfold Line.Parallel first second
  decide

theorem norm_product_square :
    (25 : Rational) ^ 2 = lineNorm first * lineNorm second := by decide

theorem negative_candidate_is_firstBisector :
    (negativeVertexBisector first second 25 first_nonNull not_parallel).Equivalent
      firstBisector := by
  unfold Line.Equivalent negativeVertexBisector first second firstBisector lineNorm
  exact ⟨by ring1, by ring1, by ring1⟩

theorem positive_candidate_is_secondBisector :
    (positiveVertexBisector first second 25 first_nonNull not_parallel).Equivalent
      secondBisector := by
  unfold Line.Equivalent positiveVertexBisector first second secondBisector lineNorm
  exact ⟨by ring1, by ring1, by ring1⟩

theorem firstBisector_nonNull : ¬ firstBisector.IsNull := by
  unfold Line.IsNull firstBisector
  decide

theorem secondBisector_nonNull : ¬ secondBisector.IsNull := by
  unfold Line.IsNull secondBisector
  decide

/-- Example 6.5's first pair of equal spreads. -/
theorem firstBisector_spreads :
    spread first firstBisector first_nonNull firstBisector_nonNull =
        (49 : Rational) / 50 ∧
      spread second firstBisector second_nonNull firstBisector_nonNull =
        (49 : Rational) / 50 := by
  constructor
  · unfold spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero first_nonNull firstBisector_nonNull)
      rational_fifty_nonzero
    unfold first firstBisector
    ring1
  · unfold spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero second_nonNull firstBisector_nonNull)
      rational_fifty_nonzero
    unfold second firstBisector
    ring1

/-- Example 6.5's second pair of equal spreads. -/
theorem secondBisector_spreads :
    spread first secondBisector first_nonNull secondBisector_nonNull =
        (1 : Rational) / 50 ∧
      spread second secondBisector second_nonNull secondBisector_nonNull =
        (1 : Rational) / 50 := by
  constructor
  · unfold spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero first_nonNull secondBisector_nonNull)
      rational_fifty_nonzero
    unfold first secondBisector
    ring1
  · unfold spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero second_nonNull secondBisector_nonNull)
      rational_fifty_nonzero
    unfold second secondBisector
    ring1

theorem bisectors_perpendicular : firstBisector.Perpendicular secondBisector := by
  unfold Line.Perpendicular firstBisector secondBisector
  ring1

/-- The complete exact-arithmetic content of Example 6.5. -/
theorem example_6_5 :
    IsNonzeroSquare (spread first second first_nonNull second_nonNull) ∧
      firstBisector.Perpendicular secondBisector ∧
      spread first firstBisector first_nonNull firstBisector_nonNull =
          (49 : Rational) / 50 ∧
      spread second firstBisector second_nonNull firstBisector_nonNull =
          (49 : Rational) / 50 ∧
      spread first secondBisector first_nonNull secondBisector_nonNull =
          (1 : Rational) / 50 ∧
      spread second secondBisector second_nonNull secondBisector_nonNull =
          (1 : Rational) / 50 := by
  refine ⟨?_, bisectors_perpendicular,
    firstBisector_spreads.1, firstBisector_spreads.2,
    secondBisector_spreads.1, secondBisector_spreads.2⟩
  exact (vertex_bisector_exists_iff_spread_isNonzeroSquare first second
    first_nonNull second_nonNull not_parallel rational_two_nonzero).1
      ⟨negativeVertexBisector first second 25 first_nonNull not_parallel,
        negativeVertexBisector_isVertexBisector first second 25 first_nonNull
          second_nonNull not_parallel rational_two_nonzero norm_product_square⟩

end ExampleSixFive

namespace ExampleSixSix

/-- Example 6.6's first line `⟨3 : 1 : 5⟩`. -/
def first : Line Rational where
  a := 3
  b := 1
  c := 5
  direction_nonzero := Or.inl (by decide)

/-- Example 6.6's second line `⟨-3 : 1 : 2⟩`. -/
def second : Line Rational where
  a := -3
  b := 1
  c := 2
  direction_nonzero := Or.inl (by decide)

/-- The first displayed book bisector `⟨2 : 0 : 1⟩`. -/
def firstBisector : Line Rational where
  a := 2
  b := 0
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The second displayed book bisector `⟨0 : 2 : 7⟩`. -/
def secondBisector : Line Rational where
  a := 0
  b := 2
  c := 7
  direction_nonzero := Or.inr (by decide)

theorem first_nonNull : ¬ first.IsNull := by
  unfold Line.IsNull first
  decide

theorem second_nonNull : ¬ second.IsNull := by
  unfold Line.IsNull second
  decide

theorem not_parallel : ¬ first.Parallel second := by
  unfold Line.Parallel first second
  decide

theorem norm_product_square :
    (10 : Rational) ^ 2 = lineNorm first * lineNorm second := by decide

theorem negative_candidate_is_firstBisector :
    (negativeVertexBisector first second 10 first_nonNull not_parallel).Equivalent
      firstBisector := by
  unfold Line.Equivalent negativeVertexBisector first second firstBisector lineNorm
  exact ⟨by ring1, by ring1, by ring1⟩

theorem positive_candidate_is_secondBisector :
    (positiveVertexBisector first second 10 first_nonNull not_parallel).Equivalent
      secondBisector := by
  unfold Line.Equivalent positiveVertexBisector first second secondBisector lineNorm
  exact ⟨by ring1, by ring1, by ring1⟩

theorem firstBisector_nonNull : ¬ firstBisector.IsNull := by
  unfold Line.IsNull firstBisector
  decide

theorem secondBisector_nonNull : ¬ secondBisector.IsNull := by
  unfold Line.IsNull secondBisector
  decide

/-- Example 6.6's first pair of equal spreads. -/
theorem firstBisector_spreads :
    spread first firstBisector first_nonNull firstBisector_nonNull =
        (1 : Rational) / 10 ∧
      spread second firstBisector second_nonNull firstBisector_nonNull =
        (1 : Rational) / 10 := by
  constructor
  · unfold spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero first_nonNull firstBisector_nonNull)
      rational_ten_nonzero
    unfold first firstBisector
    ring1
  · unfold spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero second_nonNull firstBisector_nonNull)
      rational_ten_nonzero
    unfold second firstBisector
    ring1

/-- Example 6.6's second pair of equal spreads. -/
theorem secondBisector_spreads :
    spread first secondBisector first_nonNull secondBisector_nonNull =
        (9 : Rational) / 10 ∧
      spread second secondBisector second_nonNull secondBisector_nonNull =
        (9 : Rational) / 10 := by
  constructor
  · unfold spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero first_nonNull secondBisector_nonNull)
      rational_ten_nonzero
    unfold first secondBisector
    ring1
  · unfold spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero second_nonNull secondBisector_nonNull)
      rational_ten_nonzero
    unfold second secondBisector
    ring1

theorem bisectors_perpendicular : firstBisector.Perpendicular secondBisector := by
  unfold Line.Perpendicular firstBisector secondBisector
  ring1

/-- The complete exact-arithmetic content of Example 6.6. -/
theorem example_6_6 :
    IsNonzeroSquare (spread first second first_nonNull second_nonNull) ∧
      firstBisector.Perpendicular secondBisector ∧
      spread first firstBisector first_nonNull firstBisector_nonNull =
          (1 : Rational) / 10 ∧
      spread second firstBisector second_nonNull firstBisector_nonNull =
          (1 : Rational) / 10 ∧
      spread first secondBisector first_nonNull secondBisector_nonNull =
          (9 : Rational) / 10 ∧
      spread second secondBisector second_nonNull secondBisector_nonNull =
          (9 : Rational) / 10 := by
  refine ⟨?_, bisectors_perpendicular,
    firstBisector_spreads.1, firstBisector_spreads.2,
    secondBisector_spreads.1, secondBisector_spreads.2⟩
  exact (vertex_bisector_exists_iff_spread_isNonzeroSquare first second
    first_nonNull second_nonNull not_parallel rational_two_nonzero).1
      ⟨positiveVertexBisector first second 10 first_nonNull not_parallel,
        positiveVertexBisector_isVertexBisector first second 10 first_nonNull
          second_nonNull not_parallel rational_two_nonzero norm_product_square⟩

end ExampleSixSix

end ChapterSixExamples

end DivineProportions
