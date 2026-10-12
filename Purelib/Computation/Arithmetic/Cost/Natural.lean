module

public import Purelib.Data.Nat.BitWidth
public import Purelib.Algebra.Semiring.Nat

/-!
# Natural multiplication width charges

The charge retains both operand widths and the width of their actual product.
Its quadratic natural power uses the original executable natural monoid parent
with direct structural proof certificates.
-/

namespace Purelib.Computation.Arithmetic.Cost.Natural

open Purelib.Data.Nat in
/-- A quadratic binary-width charge for natural-number multiplication.

The charge is the square of one plus the combined widths of both inputs and their actual product. -/
@[expose] public def natMultiplicationCost (left right : Nat) : Nat :=
  (BitWidth.natWidth left + BitWidth.natWidth right + BitWidth.natWidth (left * right) + 1) ^ 2
end Purelib.Computation.Arithmetic.Cost.Natural
