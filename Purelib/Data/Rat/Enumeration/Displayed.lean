module
public import Purelib.Data.Rat.SignedFraction.Normalization
import Purelib.Data.Rat.Fraction
import Purelib.Data.Int.Order

/-!
# Displayed rational fractions

Each integer numerator is normalized with its displayed successor denominator.
The positive denominator certificate retains that same natural successor.
-/

namespace Purelib.Data.Rat.Enumeration.Displayed

open Purelib.Data.Int Purelib.Data.Rat

/-- Normalize an integer numerator over the displayed successor denominator.

The signed fraction retains the original integer numerator and natural successor
cast. Direct integer order certifies that exact denominator before normalization. -/
@[expose] public def displayedFraction (num : Int) (denominatorIndex : Nat) : Fraction.Rational :=
  SignedFraction.Normalization.ofFraction
    ⟨num, (denominatorIndex + 1 : Nat), by
      exact Order.natCast_pos (Nat.zero_lt_succ denominatorIndex)⟩
end Purelib.Data.Rat.Enumeration.Displayed
