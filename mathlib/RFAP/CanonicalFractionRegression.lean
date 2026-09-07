import mathlib.RFAP.CanonicalFractionSize

/-!
# Executable regression table for canonical fractions

These closed checks cover the scalar cases required before downstream
migration.  Each equality is decided by the kernel over structural canonical
records; building the module also compiles the underlying executable
normalizers and arithmetic operations.
-/

namespace RFAP.CanonicalFraction

private def oneThirtieth : Rational :=
  ⟨1, 30, by decide, ⟨⟨1, 0, by decide⟩⟩⟩

private def oneFortySecond : Rational :=
  ⟨1, 42, by decide, ⟨⟨1, 0, by decide⟩⟩⟩

private def twoThirtyFifths : Rational :=
  ⟨2, 35, by decide, ⟨⟨18, -1, by decide⟩⟩⟩

private def twoThirds : Rational :=
  ⟨2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩

private def threeHalves : Rational :=
  ⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩

private def negativeTwoThirds : Rational :=
  ⟨-2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩

private def negativeThreeHalves : Rational :=
  ⟨-3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩

theorem regression_shared_denominator_addition :
    oneThirtieth + oneFortySecond = twoThirtyFifths := by decide

theorem regression_positive_inverse : twoThirds⁻¹ = threeHalves := by decide

theorem regression_negative_inverse :
    negativeTwoThirds⁻¹ = negativeThreeHalves := by decide

theorem regression_zero_inverse : (0 : Rational)⁻¹ = 0 := by decide

theorem regression_equivalent_displays :
    normalize ⟨6, 8, by decide⟩ = normalize ⟨3, 4, by decide⟩ := by decide

theorem regression_cast_and_order :
    ((-7 : Int) : Rational) < ((2 : Nat) : Rational) := by decide

/-- One executable Boolean used by the compiled regression runner. -/
def compiledRegressionPassed : Bool :=
  decide (oneThirtieth + oneFortySecond = twoThirtyFifths) &&
    decide (twoThirds⁻¹ = threeHalves) &&
    decide (negativeTwoThirds⁻¹ = negativeThreeHalves) &&
    decide ((0 : Rational)⁻¹ = 0) &&
    decide (normalize ⟨6, 8, by decide⟩ = normalize ⟨3, 4, by decide⟩) &&
    decide (((-7 : Int) : Rational) < ((2 : Nat) : Rational))

theorem compiledRegressionPassed_eq_true : compiledRegressionPassed = true := by
  decide

end RFAP.CanonicalFraction
