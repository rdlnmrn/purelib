module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Two-way residual and chordal bounds for rational functions

For a reduced coprime pair, a protectedState source track has a uniform positive
margin for the opposite polynomial.  This converts the polynomial
box-to-residual and residual-to-box theorems into corresponding theorems for
the quotient.  Swapping source and opposite gives the pole statements.
-/

namespace Purelib.Data.Rat.Bounds.Reciprocal

open Purelib.Algebra in
open Purelib.Data.Rat in
/-- A strict positive-scale square bound yields the reciprocal-square lower bound on the opposite-to-source quotient. -/
theorem reciprocalQuotientLower
    {sourceNorm oppositeNorm epsilon : Fraction.Rational}
    (sourcePositive : 0 < sourceNorm)
    (epsilonPositive : 0 < epsilon)
    (sourceStrict : sourceNorm < epsilon ^ 2 * oppositeNorm) :
    1 / epsilon ^ 2 ≤ oppositeNorm / sourceNorm := by
  have epsilonSquarePositive :=
    Fraction.Order.Arithmetic.pow_pos_direct epsilonPositive 2
  have multiplied : sourceNorm < oppositeNorm * epsilon ^ 2 := by
    rw [Fraction.Field.mul_comm oppositeNorm (epsilon ^ 2)]
    exact sourceStrict
  have divided : sourceNorm / epsilon ^ 2 < oppositeNorm :=
    (Fraction.Order.Field.div_lt_iff_pos epsilonSquarePositive).2
      multiplied
  apply (Fraction.Order.Field.le_div_iff_pos sourcePositive).2
  have rearranged : (1 / epsilon ^ 2) * sourceNorm =
      sourceNorm / epsilon ^ 2 := by
    simp only [Field.ExplicitField.div_eq_mul_inv]
    rw [Fraction.Field.one_mul,
      Fraction.Field.mul_comm]
  rw [rearranged]
  exact divided.le

end Purelib.Data.Rat.Bounds.Reciprocal

end
