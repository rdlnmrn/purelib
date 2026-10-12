module
import Purelib.Data.Rat.Fraction
-- Exposed constructors retain the direct integer denominator sign certificate.
import Purelib.Data.Int.Order
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.SignedFraction.Arithmetic
public import Purelib.Data.Rat.SignedFraction.Normalization

public import Purelib.Data.Rat.Fraction.Field

open Purelib.Data.Rat

open Purelib.Data.Int

/-!
# Rational construction with a successor denominator

The natural denominator parameter supplies its original successor and positive
sign certificate to executable signed-fraction normalization.
-/

@[expose] public section

namespace Purelib.Data.Rat.Fraction.Construction

/-- Normalize an integer numerator over a successor natural denominator.

The retained successor fixes a nonzero denominator without extra input; its
integer display and sign certificate enter the original signed normalization. -/
def rational
    (numerator : Int) (denominatorMinusOne : Nat) : Fraction.Rational :=
  SignedFraction.Normalization.ofFraction
    ⟨numerator, Int.ofNat (denominatorMinusOne + 1),
      Order.natCast_pos (Nat.zero_lt_succ denominatorMinusOne)⟩

end Purelib.Data.Rat.Fraction.Construction
