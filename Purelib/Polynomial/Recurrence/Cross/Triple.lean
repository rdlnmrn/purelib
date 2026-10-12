module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Triple

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Cross.Basic
import Purelib.Polynomial.Recurrence.Cross.Spread
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib.Algebra.Field

open Purelib.Polynomial

section
public section

/-!
# Divine Proportions, Chapter 8: cross polynomials

The cross-polynomial exercises are proved from their primitive recursion and
the already finite spread-polynomial recurrence.  Every index requests only a
bounded number of arithmetic steps.
-/

namespace Purelib.Polynomial.Recurrence.Cross.Triple

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]

/-- Consecutive cross polynomials and their argument satisfy the cross-triple identity.

The identity holds at every natural index over the supplied explicit field. -/
theorem exercise_8_14 (index : Nat) (value : K) :
    (Recurrence.Cross.Basic.crossPolynomial index value + value +
          Recurrence.Cross.Basic.crossPolynomial (index + 1) value - 1) ^ 2 =
      4 * Recurrence.Cross.Basic.crossPolynomial index value * value *
        Recurrence.Cross.Basic.crossPolynomial (index + 1) value := open Purelib in by
  have triple := Recurrence.Spread.Triple.recursive_spreads index (1 - value)
  unfold Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple at triple
  rw [Recurrence.Cross.Spread.crossPolynomial_eq_one_sub_spreadPolynomial index value,
    Recurrence.Cross.Spread.crossPolynomial_eq_one_sub_spreadPolynomial (index + 1) value]
  apply Group.eq_of_sub_eq_zero
  calc
    ((1 - Recurrence.Spread.Basic.spreadPolynomial index (1 - value)) + value +
          (1 - Recurrence.Spread.Basic.spreadPolynomial (index + 1) (1 - value)) - 1) ^ 2 -
        4 * (1 - Recurrence.Spread.Basic.spreadPolynomial index (1 - value)) * value *
          (1 - Recurrence.Spread.Basic.spreadPolynomial (index + 1) (1 - value)) =
      -Geometry.Trigonometry.Spread.Triple.TripleSpread.tripleSpreadFunction
        (Recurrence.Spread.Basic.spreadPolynomial index (1 - value)) (1 - value)
        (Recurrence.Spread.Basic.spreadPolynomial (index + 1) (1 - value)) := by
          unfold Geometry.Trigonometry.Spread.Triple.TripleSpread.tripleSpreadFunction
          ring1
    _ = 0 := by rw [triple]; ring1
end Purelib.Polynomial.Recurrence.Cross.Triple

end

end
