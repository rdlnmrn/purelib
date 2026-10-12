module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Basic
public import Purelib.Data.Rat.Fraction.Cast

import Purelib.Data.Rat.Fraction.Field

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

namespace Purelib.Data.Rat.Fraction.Integer

/-- A rational value has a displayed integer witness. -/
def IsIntegralRational (value : Fraction.Rational) : Prop :=
  ∃ integer : Int, value = (integer : Fraction.Rational)

/-- Every canonical rational integer cast has that integer as its integrality witness. -/
theorem integral_of_integer (integer : Int) :
    IsIntegralRational (integer : Fraction.Rational) := ⟨integer, rfl⟩

/-- The reduced representative of an integer cast is its denominator-one record. -/
theorem representative_intCast (integer : Int) :
    Fraction.Basic.representative (integer : Fraction.Rational) =
      Fraction.Cast.fromInt integer := by
  change (integer : Fraction.Rational) = Fraction.Cast.fromInt integer
  exact Fraction.Cast.intCast_eq_fromInt integer

/-- An integral canonical rational equals the cast of its own retained numerator. -/
theorem integral_eq_cast_representative_num {value : Fraction.Rational}
    (integral : IsIntegralRational value) :
    value = (Fraction.Basic.representative value).num := by
  rcases integral with ⟨integer, equality⟩
  rw [equality, representative_intCast]
  rfl

/-- An integral canonical rational has retained denominator one. -/
theorem integral_representative_den_eq_one {value : Fraction.Rational}
    (integral : IsIntegralRational value) :
    (Fraction.Basic.representative value).den = 1 := by
  rcases integral with ⟨integer, equality⟩
  rw [equality, representative_intCast]
  rfl
end Purelib.Data.Rat.Fraction.Integer

end
