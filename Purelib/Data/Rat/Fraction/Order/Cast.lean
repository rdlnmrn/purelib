module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Field

/-! Nonzero natural casts into the canonical rational carrier. -/

namespace Purelib.Data.Rat.Fraction.Order.Cast

open Purelib.Data.Rat

/-- A nonzero natural number has a nonzero canonical rational cast. -/
public theorem rational_natCast_nonzero {value : Nat}
    (valueNonzero : value ≠ 0) : (value : Fraction.Rational) ≠ 0 := by
  intro castZero
  exact valueNonzero
    (Fraction.Cast.Compatibility.natCast_injective_direct castZero)

end Purelib.Data.Rat.Fraction.Order.Cast
