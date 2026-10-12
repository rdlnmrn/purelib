module
public import Purelib.Data.Nat.Order

public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Ring.Defs

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: cross polynomials

The cross-polynomial exercises are proved from their primitive recursion and
the already finite spread-polynomial recurrence.  Every index requests only a
bounded number of arithmetic steps.
-/

namespace Purelib.Polynomial.Recurrence.Cross.Basic

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]

/-- The recursively defined cross polynomial `Cₙ`. -/
def crossPolynomial : Nat → K → K
  | 0, _ => 1
  | 1, value => value
  | index + 2, value =>
      2 * (2 * value - 1) * crossPolynomial (index + 1) value -
        crossPolynomial index value + 2 * (1 - value)

open Purelib.Polynomial
/-- The index-zero cross polynomial value is one. -/
@[simp] theorem crossPolynomial_zero (value : K) :
    crossPolynomial 0 value = 1 := rfl

/-- The index-one cross polynomial value is the argument. -/
@[simp] theorem crossPolynomial_one (value : K) :
    crossPolynomial 1 value = value := rfl

/-- The next cross value is twice (2x−1) times the previous value, minus its predecessor, plus 2(1−x). -/
@[simp] theorem crossPolynomial_succ_succ (index : Nat) (value : K) :
    crossPolynomial (index + 2) value =
      2 * (2 * value - 1) * crossPolynomial (index + 1) value -
        crossPolynomial index value + 2 * (1 - value) := rfl
end Purelib.Polynomial.Recurrence.Cross.Basic

end
