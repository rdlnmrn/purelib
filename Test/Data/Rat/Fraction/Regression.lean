module
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Nat.Coprime.Basic
import Purelib.Data.Rat.Fraction

@[expose] public section

/-!
# Executable regression table for canonical fractions

These closed checks cover scalar normalization and arithmetic. Each equality is
decided by the kernel over structural canonical records; building the module also compiles the underlying executable
normalizers and arithmetic operations.
-/

namespace Test.Data.Rat.Fraction.Regression

open Purelib.Data.Rat.Fraction

/-- The canonical rational one thirtieth. -/
private def oneThirtieth : Rational :=
  ⟨1, 30, by decide, ⟨⟨1, 0, by decide⟩⟩⟩

/-- The canonical rational one forty-second. -/
private def oneFortySecond : Rational :=
  ⟨1, 42, by decide, ⟨⟨1, 0, by decide⟩⟩⟩

/-- The canonical rational two thirty-fifths. -/
private def twoThirtyFifths : Rational :=
  ⟨2, 35, by decide, ⟨⟨18, -1, by decide⟩⟩⟩

/-- The canonical rational two thirds. -/
private def twoThirds : Rational :=
  ⟨2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩

/-- The canonical rational three halves. -/
private def threeHalves : Rational :=
  ⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩

/-- The canonical rational negative two thirds. -/
private def negativeTwoThirds : Rational :=
  ⟨-2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩

/-- The canonical rational negative three halves. -/
private def negativeThreeHalves : Rational :=
  ⟨-3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩

/-- Kernel evaluation adds one thirtieth and one forty-second to two thirty-fifths. -/
theorem regression_shared_denominator_addition :
    let oneThirtieth : Rational :=
      ⟨1, 30, by decide, ⟨⟨1, 0, by decide⟩⟩⟩
    let oneFortySecond : Rational :=
      ⟨1, 42, by decide, ⟨⟨1, 0, by decide⟩⟩⟩
    let twoThirtyFifths : Rational :=
      ⟨2, 35, by decide, ⟨⟨18, -1, by decide⟩⟩⟩
    oneThirtieth + oneFortySecond = twoThirtyFifths := by decide

/-- Kernel evaluation inverts two thirds to three halves. -/
theorem regression_positive_inverse :
    let twoThirds : Rational :=
      ⟨2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩
    let threeHalves : Rational :=
      ⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩
    twoThirds⁻¹ = threeHalves := by decide

/-- Kernel evaluation inverts negative two thirds to negative three halves. -/
theorem regression_negative_inverse :
    let negativeTwoThirds : Rational :=
      ⟨-2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩
    let negativeThreeHalves : Rational :=
      ⟨-3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩
    negativeTwoThirds⁻¹ = negativeThreeHalves := by decide

/-- The total canonical rational reciprocal maps zero to zero. -/
theorem regression_zero_inverse : (0 : Rational)⁻¹ = 0 := by decide

/-- Normalizing six eighths and three quarters yields the identical canonical rational. -/
theorem regression_equivalent_displays :
    normalize ⟨6, 8, by decide⟩ = normalize ⟨3, 4, by decide⟩ := by decide

/-- The integer embedding of negative seven is below the natural embedding of two. -/
theorem regression_cast_and_order :
    ((-7 : Int) : Rational) < ((2 : Nat) : Rational) := by decide

/-- One executable Boolean used by the compiled regression runner. -/
def compiledRegressionPassed : Bool :=
  let oneThirtieth : Rational :=
    ⟨1, 30, by decide, ⟨⟨1, 0, by decide⟩⟩⟩
  let oneFortySecond : Rational :=
    ⟨1, 42, by decide, ⟨⟨1, 0, by decide⟩⟩⟩
  let twoThirtyFifths : Rational :=
    ⟨2, 35, by decide, ⟨⟨18, -1, by decide⟩⟩⟩
  let twoThirds : Rational :=
    ⟨2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩
  let threeHalves : Rational :=
    ⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩
  let negativeTwoThirds : Rational :=
    ⟨-2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩
  let negativeThreeHalves : Rational :=
    ⟨-3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩
  decide (oneThirtieth + oneFortySecond = twoThirtyFifths) &&
    decide (twoThirds⁻¹ = threeHalves) &&
    decide (negativeTwoThirds⁻¹ = negativeThreeHalves) &&
    decide ((0 : Rational)⁻¹ = 0) &&
    decide (normalize ⟨6, 8, by decide⟩ = normalize ⟨3, 4, by decide⟩) &&
    decide (((-7 : Int) : Rational) < ((2 : Nat) : Rational))

/-- The executable canonical rational arithmetic and order regression table passes. -/
theorem compiledRegressionPassed_eq_true : compiledRegressionPassed = true := by
  decide

end Test.Data.Rat.Fraction.Regression
