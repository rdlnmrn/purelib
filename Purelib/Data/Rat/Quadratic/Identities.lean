module
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

namespace Purelib.Data.Rat.Quadratic

open Purelib.Data.Rat

/-- The squared difference plus four times the product is the squared sum.

Both sides use the original rational endpoints, and the scalar polynomial identity holds without sign conditions. -/
public theorem sub_square_add_four_product (left right : Fraction.Rational) :
    (left - right) ^ 2 + 4 * left * right = (left + right) ^ 2 := by
  ring1

end Purelib.Data.Rat.Quadratic
