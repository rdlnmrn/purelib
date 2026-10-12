module
import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Composition

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Cross.Basic
import Purelib.Polynomial.Recurrence.Cross.Spread
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: cross polynomials

The cross-polynomial exercises are proved from their primitive recursion and
the already finite spread-polynomial recurrence.  Every index requests only a
bounded number of arithmetic steps.
-/

namespace Purelib.Polynomial.Recurrence.Cross.Composition

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]

/-- Composing two cross polynomials multiplies their finite indices.

The identity follows from the spread-polynomial composition formula through the exact complement relation in the
explicit coefficient field. -/
theorem cross_polynomial_composition
    (outer inner : Nat) (value : K) :
    Recurrence.Cross.Basic.crossPolynomial outer (Recurrence.Cross.Basic.crossPolynomial inner value) =
      Recurrence.Cross.Basic.crossPolynomial (outer * inner) value := by
  calc
    Recurrence.Cross.Basic.crossPolynomial outer (Recurrence.Cross.Basic.crossPolynomial inner value) =
        1 - Recurrence.Spread.Basic.spreadPolynomial outer
          (1 - Recurrence.Cross.Basic.crossPolynomial inner value) :=
      Recurrence.Cross.Spread.crossPolynomial_eq_one_sub_spreadPolynomial outer _
    _ = 1 - Recurrence.Spread.Basic.spreadPolynomial outer
          (Recurrence.Spread.Basic.spreadPolynomial inner (1 - value)) := by
      rw [Recurrence.Cross.Spread.crossPolynomial_eq_one_sub_spreadPolynomial inner value]
      congr 2
      ring1
    _ = 1 - Recurrence.Spread.Basic.spreadPolynomial (outer * inner) (1 - value) := by
      rw [Recurrence.Spread.Composition.spread_polynomial_composition]
    _ = Recurrence.Cross.Basic.crossPolynomial (outer * inner) value :=
      (Recurrence.Cross.Spread.crossPolynomial_eq_one_sub_spreadPolynomial (outer * inner) value).symm
end Purelib.Polynomial.Recurrence.Cross.Composition

end
