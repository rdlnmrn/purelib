module
import Purelib.Algebra.Field.Ratio
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Bounds.Division
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Literal
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Cast
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Cross
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Data.Rat

open Purelib.Geometry.Plane

section
/-!
# Divine Proportions, Chapter 7 rational inequalities

Exercise 7.4 is proved with the explicit order on constructive fractions.
Exercise 7.9, as printed, is false for obtuse triangles; the second section
records a fully executable rational counterexample to both claimed bounds.
-/

@[expose] public section

namespace formalisations.DivineProportions.Chapters.Trigonometry

namespace ChapterSevenInequalities
namespace ExerciseSevenNineCounterexample

/-- A thin, non-collinear rational triangle. -/
def firstPoint : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨0, 0⟩
/-- The second vertex (1, 0) of the rational counterexample triangle. -/
def secondPoint : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨1, 0⟩
/-- The third vertex (2, 1) of the rational counterexample triangle. -/
def thirdPoint : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨2, 1⟩

/-- Side through the second and third points. -/
def firstLine : Purelib.Geometry.Plane.Line Fraction.Rational where
  a := 1
  b := -1
  c := -1
  direction_nonzero := Or.inl (by decide)

/-- Side through the first and third points. -/
def secondLine : Purelib.Geometry.Plane.Line Fraction.Rational where
  a := 1
  b := -2
  c := 0
  direction_nonzero := Or.inl (by decide)

/-- Side through the first and second points. -/
def thirdLine : Purelib.Geometry.Plane.Line Fraction.Rational where
  a := 0
  b := 1
  c := 0
  direction_nonzero := Or.inr (by decide)

/-- The side through the second and third vertices has nonzero norm. -/
theorem firstLine_nonNull : ¬ firstLine.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull firstLine
  decide

/-- The side through the first and third vertices has nonzero norm. -/
theorem secondLine_nonNull : ¬ secondLine.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull secondLine
  decide

/-- The horizontal side through the first two vertices has nonzero norm. -/
theorem thirdLine_nonNull : ¬ thirdLine.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull thirdLine
  decide

/-- The displayed points really form a non-collinear triangle and the three
displayed lines are its sides. -/
theorem triangle_certificate :
    Line.Incidence.pointDeterminant firstPoint secondPoint thirdPoint ≠ 0 ∧
      firstLine.Contains secondPoint ∧ firstLine.Contains thirdPoint ∧
      secondLine.Contains firstPoint ∧ secondLine.Contains thirdPoint ∧
      thirdLine.Contains firstPoint ∧ thirdLine.Contains secondPoint := by
  unfold Line.Incidence.pointDeterminant Purelib.Geometry.Plane.Line.Contains firstPoint secondPoint thirdPoint
    firstLine secondLine thirdLine
  exact ⟨by decide, by ring1, by ring1, by ring1, by ring1, by ring1, by ring1⟩

/-- The three vertex crosses of the displayed triangle are 4/5, 1/2 and 9/10. -/
theorem cross_values :
    Line.Cross.cross secondLine thirdLine secondLine_nonNull thirdLine_nonNull =
        (4 : Fraction.Rational) / 5 ∧
      Line.Cross.cross firstLine thirdLine firstLine_nonNull thirdLine_nonNull =
        (1 : Fraction.Rational) / 2 ∧
      Line.Cross.cross firstLine secondLine firstLine_nonNull secondLine_nonNull =
        (9 : Fraction.Rational) / 10 := by
  constructor
  · unfold Line.Cross.cross
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero secondLine_nonNull thirdLine_nonNull)
      (Fraction.Order.Cast.rational_natCast_nonzero (by decide : 5 ≠ 0))
    unfold secondLine thirdLine
    ring1
  constructor
  · unfold Line.Cross.cross
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero firstLine_nonNull thirdLine_nonNull)
      (Fraction.Order.Cast.rational_natCast_nonzero (by decide : 2 ≠ 0))
    unfold firstLine thirdLine
    ring1
  · unfold Line.Cross.cross
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero firstLine_nonNull secondLine_nonNull)
      (Fraction.Order.Cast.rational_natCast_nonzero (by decide : 10 ≠ 0))
    unfold firstLine secondLine
    ring1

/-- Exercise 7.9's claimed product bound fails on the rational triangle. -/
theorem product_bound_fails :
    ¬ (Line.Cross.cross secondLine thirdLine secondLine_nonNull thirdLine_nonNull *
          Line.Cross.cross firstLine thirdLine firstLine_nonNull thirdLine_nonNull *
          Line.Cross.cross firstLine secondLine firstLine_nonNull secondLine_nonNull ≤
        (1 : Fraction.Rational) / 64) := open Purelib in by
  rw [cross_values.1, cross_values.2.1, cross_values.2.2]
  intro claimedBound
  have firstHalf : (1 : Fraction.Rational) / 2 ≤ 4 / 5 :=
    Data.Rat.Bounds.Division.half_le_nat_ratio 4 5 (by decide) (by decide)
  have secondHalf : (1 : Fraction.Rational) / 2 ≤ 1 / 2 := le_rfl
  have thirdHalf : (1 : Fraction.Rational) / 2 ≤ 9 / 10 :=
    Data.Rat.Bounds.Division.half_le_nat_ratio 9 10 (by decide) (by decide)
  have halfNonnegative : (0 : Fraction.Rational) ≤ (1 : Fraction.Rational) / 2 := by decide
  have firstNonnegative : (0 : Fraction.Rational) ≤ 4 / 5 :=
    halfNonnegative.trans firstHalf
  have secondNonnegative : (0 : Fraction.Rational) ≤ 1 / 2 :=
    halfNonnegative.trans secondHalf
  have firstTwo :
      ((1 : Fraction.Rational) / 2) * ((1 : Fraction.Rational) / 2) ≤
        (4 / 5) * (1 / 2) :=
    Fraction.Order.Arithmetic.mul_le_mul_direct firstHalf secondHalf
      halfNonnegative firstNonnegative
  have firstTwoNonnegative : (0 : Fraction.Rational) ≤ (4 / 5) * (1 / 2) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct firstNonnegative
      secondNonnegative
  have productLower :
      ((1 : Fraction.Rational) / 2) * ((1 : Fraction.Rational) / 2) * ((1 : Fraction.Rational) / 2) ≤
        (4 / 5) * (1 / 2) * (9 / 10) :=
    Fraction.Order.Arithmetic.mul_le_mul_direct firstTwo thirdHalf
      halfNonnegative firstTwoNonnegative
  have strictConstant :
      (1 : Fraction.Rational) / 64 <
        ((1 : Fraction.Rational) / 2) * ((1 : Fraction.Rational) / 2) * ((1 : Fraction.Rational) / 2) := by
    rw [Fraction.Literal.half_cube_eq_eighth]
    have sixtyFourPositive : (0 : Fraction.Rational) < 64 :=
      Fraction.Cast.Order.natCast_pos_direct (by decide)
    have eightNonzero : (8 : Fraction.Rational) ≠ 0 :=
      Fraction.Order.Cast.rational_natCast_nonzero (by decide)
    apply (Fraction.Order.Field.div_lt_iff_pos sixtyFourPositive).2
    calc
      (1 : Fraction.Rational) < 8 :=
        Fraction.Cast.Order.natCast_lt_direct
          (show (1 : Nat) < 8 from by decide)
      _ = ((1 : Fraction.Rational) / 8) * 64 := by
        calc
          (8 : Fraction.Rational) = (((1 : Fraction.Rational) / 8) * 8) * 8 := by
            rw [ExplicitField.div_mul_cancel 1 eightNonzero]
            ring1
          _ = ((1 : Fraction.Rational) / 8) * 64 := by ring1
  exact (not_lt_of_ge claimedBound) (strictConstant.trans_le productLower)

/-- Exercise 7.9's claimed upper sum bound fails on the same triangle. -/
theorem sum_bound_fails :
    ¬ (Line.Cross.cross secondLine thirdLine secondLine_nonNull thirdLine_nonNull +
          Line.Cross.cross firstLine thirdLine firstLine_nonNull thirdLine_nonNull +
          Line.Cross.cross firstLine secondLine firstLine_nonNull secondLine_nonNull ≤
        (5 : Fraction.Rational) / 4) := open Purelib in by
  rw [cross_values.1, cross_values.2.1, cross_values.2.2]
  intro claimedBound
  have firstHalf : (1 : Fraction.Rational) / 2 ≤ 4 / 5 :=
    Data.Rat.Bounds.Division.half_le_nat_ratio 4 5 (by decide) (by decide)
  have secondHalf : (1 : Fraction.Rational) / 2 ≤ 1 / 2 := le_rfl
  have thirdHalf : (1 : Fraction.Rational) / 2 ≤ 9 / 10 :=
    Data.Rat.Bounds.Division.half_le_nat_ratio 9 10 (by decide) (by decide)
  have sumLower :
      (1 : Fraction.Rational) / 2 + (1 : Fraction.Rational) / 2 + (1 : Fraction.Rational) / 2 ≤
        4 / 5 + 1 / 2 + 9 / 10 :=
    Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Arithmetic.add_le_add_direct firstHalf secondHalf)
      thirdHalf
  have strictConstant :
      (5 : Fraction.Rational) / 4 <
        (1 : Fraction.Rational) / 2 + (1 : Fraction.Rational) / 2 + (1 : Fraction.Rational) / 2 := by
    decide
  exact (not_lt_of_ge claimedBound) (strictConstant.trans_le sumLower)

end ExerciseSevenNineCounterexample

end ChapterSevenInequalities

end formalisations.DivineProportions.Chapters.Trigonometry

end

end
