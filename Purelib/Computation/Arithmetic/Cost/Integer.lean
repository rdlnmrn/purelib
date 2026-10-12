module
public import Purelib.Data.Int.BitWidth

public import Purelib.Algebra.Semiring.Nat

/-!
# Integer multiplication width charges

The charge retains both operand widths and the width of their actual product.
Its quadratic natural power uses the original executable natural monoid parent
with direct structural proof certificates.
-/

namespace Purelib.Computation.Arithmetic.Cost.Integer

/-! ## Clearance, pools, and finite comparison passes -/

open Purelib.Data.Int in
/-- A quadratic signed-width charge for integer multiplication.

The charge includes both operand widths and the width of their actual product, with one added before squaring. -/
@[expose] public def intMultiplicationCost (left right : Int) : Nat :=
  (BitWidth.signedIntWidth left + BitWidth.signedIntWidth right + BitWidth.signedIntWidth (left * right) + 1) ^ 2
end Purelib.Computation.Arithmetic.Cost.Integer
