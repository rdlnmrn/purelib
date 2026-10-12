module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quadratic.TracePair.Basic
public import Purelib.Algebra.Quadratic.TracePair.Power
public import Purelib.Polynomial.Ascending.Integer.PowerMinusOne
public import Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Evaluation

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
import Mathlib.Data.Int.Cast.Basic

open Purelib.Algebra.Field

open Purelib.Algebra.Quadratic (TracePair)

open Purelib

open Purelib.Polynomial

section
public section

/-!
# Formal generator realization of integer power-minus-one tables

The original finite monomial coefficient table evaluates to the generator
power with the same natural degree. Subtracting the constant unit table
therefore evaluates to that complete power pair minus the unit pair.
The coefficient programs and formal evaluation retain their original owners.
-/

namespace Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Evaluation.PowerMinusOne.IntegerPolynomial

/-- Formal quadratic evaluation of the unit monomial gives the retained generator power. -/
theorem eval_monomialCoefficients_pair {K : Type*} [ExplicitField K] :
    ∀ degree : Nat, ∀ trace : K,
    Algebra.Quadratic.TracePair.eval (Ascending.Integer.PowerMinusOne.IntegerPolynomial.monomialCoefficients degree)
      trace =
      Algebra.Quadratic.TracePair.alphaPower degree trace
  | 0, trace => by
      apply Algebra.Quadratic.TracePair.ext <;>
        simp only [Ascending.Integer.PowerMinusOne.IntegerPolynomial.monomialCoefficients,
          Algebra.Quadratic.TracePair.eval,
          Algebra.Quadratic.TracePair.alphaPower,
          Algebra.Quadratic.TracePair.one, Algebra.Quadratic.TracePair.zero, -eq_self, -iff_self] <;> ring0
  | degree + 1, trace => by
      rw [Ascending.Integer.PowerMinusOne.IntegerPolynomial.monomialCoefficients,
        Algebra.Quadratic.TracePair.eval_shift,

          eval_monomialCoefficients_pair
          degree trace,
        Algebra.Quadratic.TracePair.alphaPower_succ]

/-- Formal quadratic evaluation of the power-minus-one table gives the generator power minus one. -/
theorem eval_powerMinusOneCoefficients_pair
    {K : Type*} [ExplicitField K] (degree : Nat) (trace : K) :
    Algebra.Quadratic.TracePair.eval (Ascending.Integer.PowerMinusOne.IntegerPolynomial.powerMinusOneCoefficients
      degree) trace =
      Algebra.Quadratic.TracePair.sub (Algebra.Quadratic.TracePair.alphaPower degree trace)
        Algebra.Quadratic.TracePair.one := by
  rw [Ascending.Integer.PowerMinusOne.IntegerPolynomial.powerMinusOneCoefficients, Algebra.Quadratic.TracePair.eval_sub,
    eval_monomialCoefficients_pair]
  apply Algebra.Quadratic.TracePair.ext <;>
    simp only [Algebra.Quadratic.TracePair.eval, Algebra.Quadratic.TracePair.one, Algebra.Quadratic.TracePair.zero,
      Algebra.Quadratic.TracePair.sub, -eq_self, -iff_self] <;> ring0
end Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Evaluation.PowerMinusOne.IntegerPolynomial

end
