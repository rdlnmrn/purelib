module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quadratic.TracePair.Basic
import Purelib.Algebra.Quadratic.TracePair.Norm
public import Purelib.NumberTheory.Cyclotomic.Integer
import Purelib.Polynomial.Ascending.Integer.Basic
import Purelib.Polynomial.Ascending.Integer.PowerMinusOne
import Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Evaluation
import Purelib.Polynomial.Ascending.Integer.QuadraticTrace.RationalIdentity
public import Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Reduction

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs

open Purelib.Algebra.Field

open Purelib.NumberTheory

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

namespace Purelib.NumberTheory.Cyclotomic.QuadraticTrace

variable {K : Type*} [ExplicitField K]

section ExerciseEightThirteen
section IntegerPolynomial

/-- The ordinary coefficient factorization remains valid after applying the
finite quadratic norm. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.eval_norm_cyclotomic_factorization
    (number : Nat) (positive : 0 < number) (trace : K) :
    Ascending.Integer.Basic.eval
        (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
          (Ascending.Integer.PowerMinusOne.IntegerPolynomial.powerMinusOneCoefficients
            number)) trace =
      Ascending.Integer.Basic.eval
          (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
            (Cyclotomic.Integer.properCyclotomicProductCoefficients
              number)) trace *
        Ascending.Integer.Basic.eval
          (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
            (Cyclotomic.Integer.cyclotomicCoefficients number))
          trace := open Purelib in by
  have pairIdentity :=
    Algebra.Quadratic.TracePair.eval_eq_of_ofAscending_eq
      (Cyclotomic.Integer.cyclotomic_factorization_coefficients
        number positive) trace
  rw [Algebra.Quadratic.TracePair.eval_mul] at pairIdentity
  calc
    Ascending.Integer.Basic.eval
        (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
          (Ascending.Integer.PowerMinusOne.IntegerPolynomial.powerMinusOneCoefficients
            number)) trace =
      Algebra.Quadratic.TracePair.norm trace
        (Algebra.Quadratic.TracePair.eval
          (Ascending.Integer.PowerMinusOne.IntegerPolynomial.powerMinusOneCoefficients
            number) trace) :=
        Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.eval_normCoefficients _ _
    _ = Algebra.Quadratic.TracePair.norm trace
        (Algebra.Quadratic.TracePair.mul trace
          (Algebra.Quadratic.TracePair.eval
            (Cyclotomic.Integer.properCyclotomicProductCoefficients
              number) trace)
          (Algebra.Quadratic.TracePair.eval
            (Cyclotomic.Integer.cyclotomicCoefficients number)
            trace)) := by rw [pairIdentity]
    _ = Algebra.Quadratic.TracePair.norm trace
          (Algebra.Quadratic.TracePair.eval
            (Cyclotomic.Integer.properCyclotomicProductCoefficients
              number) trace) *
        Algebra.Quadratic.TracePair.norm trace
          (Algebra.Quadratic.TracePair.eval
            (Cyclotomic.Integer.cyclotomicCoefficients number)
            trace) :=
      Algebra.Quadratic.TracePair.norm_mul _ _ _
    _ = Ascending.Integer.Basic.eval
          (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
            (Cyclotomic.Integer.properCyclotomicProductCoefficients
              number)) trace *
        Ascending.Integer.Basic.eval
          (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
            (Cyclotomic.Integer.cyclotomicCoefficients number))
          trace := by
      rw [Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.eval_normCoefficients,
        Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.eval_normCoefficients]
end IntegerPolynomial
end ExerciseEightThirteen
end Purelib.NumberTheory.Cyclotomic.QuadraticTrace

end
