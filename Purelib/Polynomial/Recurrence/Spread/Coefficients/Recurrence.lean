module

import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Nat.Order
import Purelib.Polynomial.Ascending.Integer.Basic
public import Purelib.Polynomial.Recurrence.Spread.Basic
public import Purelib.Polynomial.Recurrence.Spread.Cyclotomic.Substitution
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Algebra.Field
open Purelib.Algebra
open scoped Purelib.Data.Nat

open Purelib.Polynomial

section
@[expose] public section

/-!
# The finite Goh--Wildberger spread-cyclotomic factorization

This file completes Exercise 8.13 without roots, completed fields, or an
infinite polynomial family.  Ordinary cyclotomic factors are constructed by
finite monic long division over the constructive rationals.  Their integer
coefficients are reduced through the formal quadratic relation
`a^2 = t*a - 1`, and the resulting norm is evaluated at `t = 2 - 4s`.

The sole exceptional norm is `Phi_1`, whose norm is `4s`; this supplies the
one global factor `4` in the spread--Lucas identity.  Cancellation is done
only over the constructive rationals, after which the resulting integer
coefficient identity is transported to every explicitly supplied field,
including finite characteristic.
-/

open Purelib.Polynomial.Recurrence.Spread

namespace Purelib.Polynomial.Recurrence.Spread.Coefficients.ExerciseEightThirteen.IntegerPolynomial

variable {K : Type*} [ExplicitField K]

section ExerciseEightThirteen
section IntegerPolynomial

/-- Executable ascending integer coefficients of `S_n`, following the
defining two-step recurrence literally. -/
def
  spreadPolynomialCoefficients
  : Nat → List Int
  | 0 => []
  | 1 => [0, 1]
  | index + 2 =>
      Ascending.Integer.Basic.Certificate.add
        (Ascending.Integer.Basic.sub
          (Ascending.Integer.Basic.Certificate.mul
            Cyclotomic.Substitution.ExerciseEightThirteen.IntegerPolynomial.centeredSpreadSubstitution

              (ExerciseEightThirteen.IntegerPolynomial.spreadPolynomialCoefficients
              (index + 1)))

            (ExerciseEightThirteen.IntegerPolynomial.spreadPolynomialCoefficients
            index))
        [0, 2]

/-- The zeroth spread polynomial has an empty ascending coefficient list. -/
@[simp] theorem
  spreadPolynomialCoefficients_zero
  :
    spreadPolynomialCoefficients 0 =
      [] := rfl

/-- The first spread polynomial has the ascending coefficient list of the coordinate. -/
@[simp] theorem
  spreadPolynomialCoefficients_one
  :
    spreadPolynomialCoefficients 1 =
      [0, 1] := rfl

/-- The ascending spread coefficients satisfy their defining recurrence.

Multiply the current list by the centered substitution, subtract the preceding list, and add twice the coordinate. -/
@[simp] theorem
  spreadPolynomialCoefficients_succ_succ
  (index : Nat) :
    spreadPolynomialCoefficients
      (index + 2) =
      Ascending.Integer.Basic.Certificate.add
        (Ascending.Integer.Basic.sub
          (Ascending.Integer.Basic.Certificate.mul
            Cyclotomic.Substitution.ExerciseEightThirteen.IntegerPolynomial.centeredSpreadSubstitution

              (ExerciseEightThirteen.IntegerPolynomial.spreadPolynomialCoefficients
              (index + 1)))

            (ExerciseEightThirteen.IntegerPolynomial.spreadPolynomialCoefficients
            index))
        [0, 2] := rfl

/-- The coefficient program evaluates to the book's spread polynomial in
every explicit field. -/
theorem
  eval_spreadPolynomialCoefficients
  :
    ∀ index : Nat, ∀ value : K,
    Ascending.Integer.Basic.eval
      (spreadPolynomialCoefficients
      index) value =
      Basic.spreadPolynomial index value
  | 0, value => by
      rw
        [ExerciseEightThirteen.IntegerPolynomial.spreadPolynomialCoefficients_zero,
        Ascending.Integer.Basic.eval_nil,
        Basic.spreadPolynomial_zero]
  | 1, value => by
      simp only
        [ExerciseEightThirteen.IntegerPolynomial.spreadPolynomialCoefficients_one,
        Ascending.Integer.Basic.eval_cons, Ascending.Integer.Basic.eval_nil,
        Ring.IntCast.cast_zero, Int.cast_one, mul_zero, add_zero, zero_add, mul_one,
        Basic.spreadPolynomial_one, -eq_self, -iff_self]
      rfl
  | index + 2, value => by
      rw
        [ExerciseEightThirteen.IntegerPolynomial.spreadPolynomialCoefficients_succ_succ,
        Ascending.Integer.Basic.eval_add, Ascending.Integer.Basic.eval_sub,
        Ascending.Integer.Basic.eval_mul,
          Cyclotomic.Substitution.ExerciseEightThirteen.IntegerPolynomial.eval_centeredSpreadSubstitution,

          ExerciseEightThirteen.IntegerPolynomial.eval_spreadPolynomialCoefficients
          (index + 1) value,

          ExerciseEightThirteen.IntegerPolynomial.eval_spreadPolynomialCoefficients
          index value,
        Basic.spreadPolynomial_succ_succ]
      have twoCast : ((2 : Int) : K) = (2 : K) :=
        AddGroupWithOne.intCast_ofNat 2
      simp only [Ascending.Integer.Basic.eval_cons, Ascending.Integer.Basic.eval_nil, Ring.IntCast.cast_zero, twoCast,
        mul_zero, add_zero, zero_add, -eq_self, -iff_self]
      ring0
end IntegerPolynomial
end ExerciseEightThirteen
end Purelib.Polynomial.Recurrence.Spread.Coefficients.ExerciseEightThirteen.IntegerPolynomial

end
