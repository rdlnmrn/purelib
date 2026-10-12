module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

namespace Purelib.Data.Rat.Additive.TriangleBounds

section TriangleSpreadRules

section
open Purelib.Data.Rat
/-- Require the second and third rational values each to be bounded by the sum of the other two. -/
def SpreadDifferenceBound
    (first second third : Fraction.Rational) : Prop :=
  second ≤ first + third ∧ third ≤ first + second

/-- Require each of three rational values to be at most the sum of the other two. -/
def TriangleSpreadRules.AcuteSpreadBounds (first second third :
  Fraction.Rational) : Prop :=
  third ≤ first + second ∧
    first ≤ second + third ∧
    second ≤ third + first

end

section
open Purelib.Data.Rat
/-- Any two cyclic paired spread bounds imply the third pair and all three triangle inequalities. -/
theorem exercise_20_3 (first second third : Fraction.Rational) :
    (SpreadDifferenceBound first second third ∧
        SpreadDifferenceBound second third first →
      SpreadDifferenceBound third first second ∧
        Additive.TriangleBounds.TriangleSpreadRules.AcuteSpreadBounds first second third) ∧
    (SpreadDifferenceBound second third first ∧
        SpreadDifferenceBound third first second →
      SpreadDifferenceBound first second third ∧
        Additive.TriangleBounds.TriangleSpreadRules.AcuteSpreadBounds first second third) ∧
    (SpreadDifferenceBound third first second ∧
        SpreadDifferenceBound first second third →
      SpreadDifferenceBound second third first ∧
        Additive.TriangleBounds.TriangleSpreadRules.AcuteSpreadBounds first second third) := by
  unfold SpreadDifferenceBound Additive.TriangleBounds.TriangleSpreadRules.AcuteSpreadBounds
  constructor
  · rintro ⟨⟨secondBound, thirdBound⟩, ⟨_thirdBound, firstBound⟩⟩
    exact ⟨⟨by simpa only [add_comm] using firstBound,
        by simpa only [add_comm] using secondBound⟩,
      ⟨thirdBound, firstBound, by simpa only [add_comm] using secondBound⟩⟩
  constructor
  · rintro ⟨⟨thirdBound, firstBound⟩, ⟨_firstBound, secondBound⟩⟩
    exact ⟨⟨by simpa only [add_comm] using secondBound,
        by simpa only [add_comm] using thirdBound⟩,
      ⟨by simpa only [add_comm] using thirdBound,
        firstBound, secondBound⟩⟩
  · rintro ⟨⟨firstBound, secondBound⟩, ⟨_secondBound, thirdBound⟩⟩
    exact ⟨⟨by simpa only [add_comm] using thirdBound,
        by simpa only [add_comm] using firstBound⟩,
      ⟨thirdBound, by simpa only [add_comm] using firstBound,
        secondBound⟩⟩

/-- Require the sum of the second and third rational values to be at most the first. -/
def ObtuseAtFirst (first second third : Fraction.Rational) : Prop :=
  second + third ≤ first

/-- A positive third value prevents both first and second values from dominating the sum of the other two. -/
private theorem not_two_obtuse
    (first second third : Fraction.Rational)
    (thirdPositive : 0 < third)
    (firstObtuse : ObtuseAtFirst first second third)
    (secondObtuse : ObtuseAtFirst second first third) : False := by
  have thirdNonnegative : (0 : Fraction.Rational) ≤ third :=
    Fraction.Order.Arithmetic.le_of_lt_direct thirdPositive
  have secondAtMostFirst : second ≤ first := by
    calc
      second = 0 + second := by ring1
      _ ≤ third + second :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          thirdNonnegative second
      _ = second + third := by ring1
      _ ≤ first := firstObtuse
  have sumAtMostFirst : first + third ≤ first :=
    secondObtuse.trans secondAtMostFirst
  have firstBelowSum : first < first + third := by
    calc
      first = 0 + first := by ring1
      _ < third + first :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct thirdPositive first
      _ = first + third := by ring1
  exact (not_lt_of_ge sumAtMostFirst firstBelowSum).elim

/-- For three positive rationals, no two cyclic obtuse-at-first inequalities can hold together. -/
theorem exercise_20_4 (first second third : Fraction.Rational)
    (firstPositive : 0 < first) (secondPositive : 0 < second)
    (thirdPositive : 0 < third) :
    ¬ (ObtuseAtFirst first second third ∧
        ObtuseAtFirst second first third) ∧
    ¬ (ObtuseAtFirst second third first ∧
        ObtuseAtFirst third second first) ∧
    ¬ (ObtuseAtFirst third first second ∧
        ObtuseAtFirst first third second) := by
  constructor
  · rintro ⟨firstObtuse, secondObtuse⟩
    exact not_two_obtuse first second third thirdPositive
      firstObtuse secondObtuse
  constructor
  · rintro ⟨secondObtuse, thirdObtuse⟩
    exact not_two_obtuse second third first firstPositive
      secondObtuse thirdObtuse
  · rintro ⟨thirdObtuse, firstObtuse⟩
    exact not_two_obtuse third first second secondPositive
      thirdObtuse firstObtuse

end

open Purelib.Data.Rat in
/-- Require each of three rational values to be at most the sum of the other two. -/
def TriangleSpreadRules.AcuteQuadranceBounds
    (first second third : Fraction.Rational) : Prop :=
  third ≤ first + second ∧
    first ≤ second + third ∧
    second ≤ third + first
end TriangleSpreadRules
end Purelib.Data.Rat.Additive.TriangleBounds

end
