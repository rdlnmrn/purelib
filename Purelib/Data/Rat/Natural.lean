module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order

import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Finite integration, an algebraic FTC, and polynomial ODE certificates

Integration here is coefficient arithmetic on a displayed finite polynomial.
The antiderivative divides each coefficient by its positive natural degree.
The fundamental theorem is the pair of exact finite statements that
differentiating this table returns the original table and that an interval
increment factors through the antiderivative's secant kernel.

The final section packages elementary initial-value problems with polynomial
forcing and records the exact finite defect of the exponential polynomial for
`y' = y`.  No measure, completed interval, limiting partition, or
function-as-an-infinite-set is used.
-/

namespace Purelib.Data.Rat.Natural

open Purelib.Data.Rat in
/-- A positive natural number has a nonzero canonical rational cast. -/
public theorem degreeCast_ne_zero (degree : Nat) (positive : 0 < degree) :
    (degree : Fraction.Rational) ≠ 0 :=
  (Fraction.Cast.Order.natCast_pos_direct positive).ne'

end Purelib.Data.Rat.Natural

end
