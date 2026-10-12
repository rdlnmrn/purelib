module
public import Purelib.Algebra.Field.ExplicitField
-- The exposed recurrence retains the constructive natural numeral certificates.
public import Purelib.Data.Nat.Order

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs

open Purelib.Algebra.Field
open scoped Purelib.Data.Nat

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: spread polynomials

Spread polynomials are primitive-recursive finite expressions.  No sequence
or limit object is introduced: evaluating index `n` performs exactly `n`
finite recurrence steps in the coefficient field.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Basic

variable {K : Type*} [ExplicitField K]

/-- Primitive-recursive evaluation of the spread polynomial at a displayed index.

The initial values are zero and the argument. Each later value is twice
`1-2x` times its predecessor, minus the preceding value, plus `2x`, using
the supplied commutative ring's retained arithmetic operations. -/
def spreadPolynomial {R : Type*} [CommRing R] : Nat → R → R
  | 0, _ => 0
  | 1, value => value
  | index + 2, value =>
      2 * (1 - 2 * value) * spreadPolynomial (index + 1) value -
        spreadPolynomial index value + 2 * value

open Purelib.Polynomial
/-- The index-zero spread polynomial value is zero. -/
@[simp] theorem spreadPolynomial_zero
    {R : Type*} [CommRing R] (value : R) :
    spreadPolynomial 0 value = 0 := rfl

/-- The index-one spread polynomial value is the argument. -/
@[simp] theorem spreadPolynomial_one
    {R : Type*} [CommRing R] (value : R) :
    spreadPolynomial 1 value = value := rfl

/-- The next spread value is twice (1−2x) times the previous value, minus its predecessor, plus 2x. -/
@[simp] theorem spreadPolynomial_succ_succ
    {R : Type*} [CommRing R] (index : Nat) (value : R) :
    spreadPolynomial (index + 2) value =
      2 * (1 - 2 * value) * spreadPolynomial (index + 1) value -
        spreadPolynomial index value + 2 * value := rfl
end Purelib.Polynomial.Recurrence.Spread.Basic

end
