module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Ascending.Integer.Basic
public import Purelib.Polynomial.Recurrence.Lucas.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Algebra.Ring.IntCast
import Mathlib.Data.Int.Cast.Basic

open Purelib.Algebra.Field
open Purelib.Algebra

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite Lucas reduction for spread-cyclotomic factorization

Exercise 8.13 was the Goh--Wildberger factorization conjecture; a proof only
appeared in Cigler--Herbig (2026).  This module isolates the entirely finite
algebraic part of that proof.  Lucas values are primitive recursion, their
product and square identities come from the finite Chebyshev recurrence, and
Euler's totient is the bounded count in `Purelib.NumberTheory.Totient`.

No roots, cosine values, completed fields, or infinite polynomial family are
introduced here.
-/

namespace Purelib.Polynomial.Recurrence.Lucas.Coefficients

variable {K : Type*} [ExplicitField K]

section ExerciseEightThirteen
section IntegerPolynomial

/-- Integer coefficient lists for the Lucas recurrence, in ascending degree
order.  This is the coefficient-level object needed for a constructive
cyclotomic factor algorithm. -/
def ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients :
  Nat → List Int
  | 0 => [2]
  | 1 => [0, 1]
  | index + 2 =>
      Ascending.Integer.Basic.sub (Ascending.Integer.Basic.shift
        (Purelib.Polynomial.Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients
        (index + 1)))
        (Purelib.Polynomial.Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients
          index)

/-- The zeroth Lucas coefficient list is the constant two. -/
@[simp] theorem
  ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients_zero
  :
    Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients 0 = [2] := rfl

/-- The first Lucas coefficient list represents the coordinate polynomial. -/
@[simp] theorem
  ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients_one
  :
    Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients 1 = [0, 1] := rfl

/-- The ascending Lucas coefficients satisfy their two-step recurrence.

Shift the current list by one coordinate power and subtract the preceding list. -/
@[simp] theorem
  ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients_succ_succ
  (index : Nat) :
    Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients (index + 2) =
      Ascending.Integer.Basic.sub (Ascending.Integer.Basic.shift
        (Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients (index + 1)))
        (Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients index) := rfl

/-- The coefficient recurrence evaluates to the Lucas recurrence in every
constructive explicit field. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.evalLucasCoefficients
  : ∀ index : Nat, ∀ value : K,
    Ascending.Integer.Basic.eval
      (Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients index) value =
      Recurrence.Lucas.Basic.lucas index value
  | 0, value => by
      simp only [Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients_zero,
        Ascending.Integer.Basic.eval_cons, Ascending.Integer.Basic.eval_nil,
        Int.cast_ofNat, mul_zero, add_zero, Recurrence.Lucas.Basic.ExerciseEightThirteen.lucas_zero,
        -eq_self, -iff_self]
      rfl
  | 1, value => by
      simp only [Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients_one,
        Ascending.Integer.Basic.eval_cons, Ascending.Integer.Basic.eval_nil,
        Ring.IntCast.cast_zero, Int.cast_one, mul_zero, add_zero, zero_add, mul_one,
        Recurrence.Lucas.Basic.ExerciseEightThirteen.lucas_one, -eq_self, -iff_self]
      rfl
  | index + 2, value => by
      rw [Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients_succ_succ,
        Ascending.Integer.Basic.eval_sub, Ascending.Integer.Basic.eval_shift,
        Purelib.Polynomial.Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.evalLucasCoefficients
          (index + 1) value,
        Purelib.Polynomial.Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.evalLucasCoefficients
          index value,
        Recurrence.Lucas.Basic.ExerciseEightThirteen.lucas_succ_succ]

/-- The coefficient list has the exact expected slot count. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients_length
  : ∀ index : Nat,
    (Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients index).length = index + 1
  | 0 => rfl
  | 1 => rfl
  | index + 2 => by
      rw [Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients_succ_succ,
        Ascending.Integer.Basic.length_sub]
      simp only [Ascending.Integer.Basic.shift, List.length_cons,

          ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients_length
          (index + 1),

          ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients_length
          index]
      rewrite [Nat.max_def]
      rewrite [if_neg (by omega0 : ¬ index + 1 + 1 + 1 ≤ index + 1)]
      rfl

/-- Every positive-index Lucas coefficient list is monic.  Together with the
slot-count theorem, this gives exact degree `n` without appealing to a
completed polynomial type. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients_monic
  : ∀ index : Nat,
    (Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients (index + 1)).getLast? =
      some 1
  | 0 => rfl
  | index + 1 => by
      rw [show index + 1 + 1 = index + 2 by omega0,
        Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients_succ_succ]
      have shorter :
          (Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients index).length <
            (Ascending.Integer.Basic.shift
              (Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients (index +
              1))).length := by
        rw [Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients_length,
          show (Ascending.Integer.Basic.shift
            (Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients (index +
            1))).length =
              (Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients (index +
                1)).length + 1 by rfl,
          Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients_length]
        omega0
      rw [Ascending.Integer.Basic.getLast?_sub_of_length_lt _ _ shorter,
        Ascending.Integer.Basic.getLast?_shift_of_ne_nil]
      · exact
          ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients_monic
          index
      · intro empty
        have lengthEquation :=
          Recurrence.Lucas.Coefficients.ExerciseEightThirteen.IntegerPolynomial.lucasCoefficients_length (index + 1)
        rw [empty] at lengthEquation
        simp only [List.length_nil]
          at lengthEquation
        omega0
end IntegerPolynomial
end ExerciseEightThirteen

end Purelib.Polynomial.Recurrence.Lucas.Coefficients

end
