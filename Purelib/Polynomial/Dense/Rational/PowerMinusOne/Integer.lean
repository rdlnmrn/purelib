module
import Purelib.Data.Rat.Fraction.Integer
public import Purelib.Polynomial.Ascending.Integer.PowerMinusOne
import Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic
import Purelib.Polynomial.Dense.Rational.Extensionality
public import Purelib.Polynomial.Dense.Rational.IntegerCoefficients.Basic
public import Purelib.Polynomial.Dense.Rational.PowerMinusOne

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial

section
@[expose] public section

/-!
# Monic integer coefficients for the finite cyclotomic construction

The rational long-division factors constructed in `Cyclotomic` are
shown here to be monic and to carry executable ascending integer coefficient
lists.  The proof is a second primitive recursion over the already verified
factorization; it uses the finite monic-division theorem rather than a UFD or
root factorization.
-/

namespace Purelib.Polynomial.Dense.Rational.PowerMinusOne.Integer

open Purelib.Polynomial.Dense.Basic.DensePolynomial

namespace IntegerBridge

/-- The rational monomial `X^degree` has executable integer coefficients. -/
theorem monomialOne_integral : ∀ degree :
  Nat,
    Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial (Dense.Rational.PowerMinusOne.monomialOne degree)
  | 0 => by
      rw [Dense.Rational.PowerMinusOne.monomialOne_zero]
      exact Dense.Rational.IntegerCoefficients.Basic.integral_constant
        (Purelib.Data.Rat.Fraction.Integer.integral_of_integer 1)
  | degree + 1 => by
      rw [Dense.Rational.PowerMinusOne.monomialOne_succ]
      exact Dense.Rational.IntegerCoefficients.Basic.integral_shift 1
        (monomialOne_integral degree)

/-- The rational polynomial `X^degree - 1` has executable integer coefficients. -/
theorem powerMinusOne_integral (degree :
  Nat) :
    Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial (Dense.Rational.PowerMinusOne.powerMinusOne degree) :=
      open Purelib.Data.Rat in by
  rw [Dense.Rational.PowerMinusOne.powerMinusOne]
  exact Dense.Rational.IntegerCoefficients.Basic.integral_sub
    (monomialOne_integral degree)
    (Dense.Rational.IntegerCoefficients.Basic.integral_constant (Fraction.Integer.integral_of_integer 1))
end IntegerBridge

/-- Convert the explicit ascending integer coefficients of `X^number - 1` to their rational dense polynomial. -/
theorem ofAscending_powerMinusOneCoefficients (number :
  Nat) :
    Dense.Rational.AscendingInteger.Basic.ofAscending
        (Ascending.Integer.PowerMinusOne.IntegerPolynomial.powerMinusOneCoefficients
          number) =
      Dense.Rational.PowerMinusOne.powerMinusOne number := by
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (Dense.Rational.AscendingInteger.Basic.ofAscending_normalized _)
    (Dense.Rational.PowerMinusOne.powerMinusOne_normalized number)
  intro point
  rw [Dense.Rational.AscendingInteger.Basic.eval_ofAscending,
    Ascending.Integer.PowerMinusOne.IntegerPolynomial.eval_powerMinusOneCoefficients,
    Dense.Rational.PowerMinusOne.eval_powerMinusOne]
end Purelib.Polynomial.Dense.Rational.PowerMinusOne.Integer

end
