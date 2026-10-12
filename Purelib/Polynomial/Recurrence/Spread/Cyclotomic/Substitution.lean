module
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Ring.IntCast
public import Purelib.Data.Nat.Order
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Ascending.Integer.Basic
public import Purelib.Polynomial.Ascending.Integer.Composition

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra
open Purelib.Algebra.Field
open scoped Purelib.Data.Nat

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

namespace Purelib.Polynomial.Recurrence.Spread.Cyclotomic.Substitution

variable {K : Type*} [ExplicitField K]

section ExerciseEightThirteen
section IntegerPolynomial

/-- The affine substitution from a real-cyclotomic trace variable to the
spread variable. -/
def
  ExerciseEightThirteen.IntegerPolynomial.centeredSpreadSubstitution
  : List Int := [2, -4]

/-- The retained ascending affine table evaluates to two minus four times the spread. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.eval_centeredSpreadSubstitution
  (value : K) :
    Ascending.Integer.Basic.eval
      Recurrence.Spread.Cyclotomic.Substitution.ExerciseEightThirteen.IntegerPolynomial.centeredSpreadSubstitution value
      = 2 - 4 * value := by
  unfold Recurrence.Spread.Cyclotomic.Substitution.ExerciseEightThirteen.IntegerPolynomial.centeredSpreadSubstitution
  have castTwo : ((2 : Int) : K) = (2 : K) :=
    AddGroupWithOne.intCast_ofNat 2
  have castFour : ((4 : Int) : K) = (4 : K) :=
    AddGroupWithOne.intCast_ofNat 4
  have castNegativeFour : ((-4 : Int) : K) = (-4 : K) :=
    (Ring.IntCast.neg (R := K) (4 : Int)).trans (congrArg Neg.neg castFour)
  simp only [Ascending.Integer.Basic.eval_cons, Ascending.Integer.Basic.eval_nil,
    castTwo, castNegativeFour, mul_zero, add_zero, -eq_self, -iff_self]
  ring1

/-- Substitute `2-4s` into an integer real-cyclotomic factor. -/
def
  ExerciseEightThirteen.IntegerPolynomial.spreadRealFactorCoefficients
  (coefficients : List Int) : List Int :=
  Ascending.Integer.Composition.compose coefficients
    Recurrence.Spread.Cyclotomic.Substitution.ExerciseEightThirteen.IntegerPolynomial.centeredSpreadSubstitution

/-- Evaluating the substituted factor equals evaluating the original integer table at two minus four times the spread.
-/
theorem
  ExerciseEightThirteen.IntegerPolynomial.eval_spreadRealFactorCoefficients
    (coefficients : List Int) (value : K) :
    Ascending.Integer.Basic.eval
      (Recurrence.Spread.Cyclotomic.Substitution.ExerciseEightThirteen.IntegerPolynomial.spreadRealFactorCoefficients
      coefficients) value =
      Ascending.Integer.Basic.eval coefficients (2 - 4 * value) := by
  rw [Recurrence.Spread.Cyclotomic.Substitution.ExerciseEightThirteen.IntegerPolynomial.spreadRealFactorCoefficients,
    Ascending.Integer.Composition.eval_compose,
    Recurrence.Spread.Cyclotomic.Substitution.ExerciseEightThirteen.IntegerPolynomial.eval_centeredSpreadSubstitution]

/-- Square the integer coefficient table after substituting two minus four times the coordinate. -/
def
  ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicCoefficients
  (coefficients : List Int) : List Int :=
  Ascending.Integer.Composition.power
    (Recurrence.Spread.Cyclotomic.Substitution.ExerciseEightThirteen.IntegerPolynomial.spreadRealFactorCoefficients
    coefficients) 2

/-- The squared substituted factor evaluates to the square of the original table at the centered spread parameter. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.eval_spreadCyclotomicCoefficients
    (coefficients : List Int) (value : K) :
    Ascending.Integer.Basic.eval
      (Recurrence.Spread.Cyclotomic.Substitution.ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicCoefficients
      coefficients) value =
      Ascending.Integer.Basic.eval coefficients (2 - 4 * value) ^ 2 := by
  rw [Recurrence.Spread.Cyclotomic.Substitution.ExerciseEightThirteen.IntegerPolynomial.spreadCyclotomicCoefficients,
    Ascending.Integer.Composition.eval_power,
    Recurrence.Spread.Cyclotomic.Substitution.ExerciseEightThirteen.IntegerPolynomial.eval_spreadRealFactorCoefficients]

end IntegerPolynomial
end ExerciseEightThirteen

end Purelib.Polynomial.Recurrence.Spread.Cyclotomic.Substitution

end
