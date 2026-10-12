module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Int.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.SignedFraction.Normalization

/-!
# Canonical rational records with unit numerator
-/

namespace Purelib.Data.Rat.Fraction.UnitNumerator

open Purelib.Data.Rat

public section

/-- Gcd-reduced record for `1 / scale`.

The supplied positive natural scale is retained exactly as denominator. Unit numerator and the original Bézout
coefficients one and zero certify the reduced record. -/
@[expose] def unitReduced (scale : Nat) (positive : 0 < scale) :
    Fraction.Basic.ReducedFraction :=
  { num := 1
    den := scale
    den_pos := positive
    reduced := ⟨⟨1, 0, by
      simp only [Int.natAbs_one, Int.one_mul, Purelib.Data.Int.Arithmetic.zero_mul,
        Int.add_zero, Int.natCast_one, -eq_self, -iff_self]
      rfl⟩⟩ }

/-- Normalize the signed display of the already reduced one-over-scale record.

The supplied positive natural scale is retained as denominator. Representative readback recovers the exact
unit-numerator record and its explicit Bézout certificate. -/
@[expose] def unitCoordinate (scale : Nat) (positive : 0 < scale) : Fraction.Rational :=
  SignedFraction.Normalization.ofFraction (SignedFraction.Normalization.toFraction (Fraction.UnitNumerator.unitReduced
    scale positive))

/-- The representative of the unit fraction constructor is exactly its retained one-over-scale record. -/
@[simp] theorem representative_unitCoordinate (scale : Nat)
    (positive : 0 < scale) :
    Fraction.Basic.representative
        (Fraction.UnitNumerator.unitCoordinate scale positive) = Fraction.UnitNumerator.unitReduced scale positive := by
  exact SignedFraction.Normalization.representative_of_reduced _

/-- Multiplying a retained positive-scale unit fraction by that scale gives one. -/
theorem unitCoordinate_mul_scale (scale : Nat) (positive : 0 < scale) :
    Fraction.UnitNumerator.unitCoordinate scale positive * (scale : Fraction.Rational) = 1 := by
  have clearance := Fraction.Cast.representative_mul_den
    (Fraction.UnitNumerator.unitCoordinate scale positive)
  rw [Fraction.UnitNumerator.representative_unitCoordinate scale positive] at clearance
  exact clearance

/-- A unit fraction with retained positive natural scale is nonzero. -/
theorem unitCoordinate_ne_zero (scale : Nat) (positive : 0 < scale) :
    Fraction.UnitNumerator.unitCoordinate scale positive ≠ 0 := by
  intro zero
  have clearance := Fraction.UnitNumerator.unitCoordinate_mul_scale scale positive
  rw [zero, Fraction.Field.zero_mul_direct] at clearance
  exact Fraction.Field.zero_ne_one clearance

end

end Purelib.Data.Rat.Fraction.UnitNumerator
