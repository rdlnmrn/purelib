module
import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Ascending.Rational.Antiderivative
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Coefficientwise
import Purelib.Polynomial.Ascending.Rational.Derivative
public import Purelib.Polynomial.Ascending.Rational.Evaluation

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Ascending.Rational.Basic (CoefficientPolynomial)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite integration, an algebraic FTC, and polynomial ODE certificates

Integration here is coefficient arithmetic on a displayed finite polynomial.
The antiderivative divides each coefficient by its positive natural degree.
The fundamental theorem is the pair of exact finite statements that
differentiating this table returns the original table and that an interval
increment factors through the antiderivative's secant kernel.

The final section packages elementary initial-value problems with polynomial
forcing and records the exact finite defect of the exponential polynomial for
`y' = y`.  No measure, completed interval, limiting partition, or
function-as-an-infinite-set is used.
-/

namespace Purelib.Polynomial.Ascending.Rational.ODE.Forcing

/-! ## Elementary polynomial initial-value problems -/

/-- Exact finite solution table for `y' = forcing`, with displayed rational
initial time and value. -/
def polynomialIVPSolution (forcing :
  CoefficientPolynomial)
    (initialTime initialValue : Fraction.Rational) : CoefficientPolynomial :=
  let primitive := Antiderivative.antiderivative 0 forcing
  Basic.add
    (Basic.constant (initialValue - Evaluation.scalarEval initialTime primitive))
    primitive

/-- The polynomial forcing solution takes the prescribed value at its rational initial time. -/
theorem polynomialIVPSolution_initial (forcing :
  CoefficientPolynomial)
    (initialTime initialValue : Fraction.Rational) :
    Evaluation.scalarEval initialTime
      (polynomialIVPSolution forcing initialTime initialValue) =
        initialValue := by
  simp only [polynomialIVPSolution, Evaluation.scalarEval_add,
    Evaluation.scalarEval_constant]
  ring1

/-- The returned finite table satisfies its polynomial forcing equation
coefficient by coefficient. -/
theorem polynomialIVPSolution_derivative (forcing :
  CoefficientPolynomial)
    (initialTime initialValue : Fraction.Rational) :
    Coefficientwise.CoefficientwiseEqual
      (Derivative.derivative
        (polynomialIVPSolution forcing initialTime initialValue))
      forcing := by
  let primitive := Antiderivative.antiderivative 0 forcing
  let offset := initialValue - Evaluation.scalarEval initialTime primitive
  exact Coefficientwise.coefficientwise_trans
    (Derivative.derivative_add (Basic.constant offset) primitive)
    (Coefficientwise.coefficientwise_trans
      (Coefficientwise.coefficientwise_add (Derivative.derivative_constant offset)
        (by
          rw [show Derivative.derivative primitive = forcing by
            exact Antiderivative.derivative_antiderivative 0 forcing]
          exact Coefficientwise.coefficientwise_refl forcing))
      (Coefficientwise.coefficientwise_zero_add forcing))
end Purelib.Polynomial.Ascending.Rational.ODE.Forcing

end
