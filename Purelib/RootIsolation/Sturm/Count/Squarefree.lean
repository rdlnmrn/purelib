module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
public import Purelib.Polynomial.Dense.Rational.Pair.Reduction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

namespace Purelib.RootIsolation.Sturm.Count.Squarefree

/-- For an explicitly coprime polynomial/derivative pair, the reduced Sturm
denominator has exactly the same displayed zeros as the original
polynomial.  The reverse implication uses only the two finite factor
identities and the supplied Bézout identity. -/
theorem denominator_eval_ne_zero_of_reduced_of_coprime
    {polynomial : Dense.Rational.Basic.CoordinatePolynomial} {parameter : Fraction.Rational}
    (coprime : Dense.Rational.Bezout.Basic.CoprimeCertificate polynomial
      (Dense.Derivative.derivative polynomial))
    (reducedNonzero :
      (Dense.Rational.Pair.Reduction.reducedDenominator
        (Dense.Derivative.derivative polynomial) polynomial).eval
          parameter ≠ 0) :
    polynomial.eval parameter ≠ 0 := by
  intro polynomialZero
  have derivativeNonzero :
      (Dense.Derivative.derivative polynomial).eval parameter ≠ 0 := by
    intro derivativeZero
    have identity := coprime.identity parameter
    rw [polynomialZero, derivativeZero,
      Fraction.Field.mul_zero_direct,
      Fraction.Field.mul_zero_direct,
      Fraction.Field.zero_add] at identity
    exact Fraction.Field.zero_ne_one identity.symm
  have gcdNonzero :
      (Dense.GCD.gcd
        (Dense.Derivative.derivative polynomial) polynomial).eval
          parameter ≠ 0 := by
    intro gcdZero
    have derivativeIdentity := Dense.GCD.leftFactor_eval_identity
      (Dense.Derivative.derivative polynomial) polynomial parameter
    rw [gcdZero, Fraction.Field.zero_mul_direct]
      at derivativeIdentity
    exact derivativeNonzero derivativeIdentity
  have polynomialIdentity := Dense.GCD.rightFactor_eval_identity
    (Dense.Derivative.derivative polynomial) polynomial parameter
  change polynomial.eval parameter =
    (Dense.GCD.gcd
      (Dense.Derivative.derivative polynomial) polynomial).eval
        parameter *
      (Dense.Rational.Pair.Reduction.reducedDenominator
        (Dense.Derivative.derivative polynomial) polynomial).eval
          parameter at polynomialIdentity
  have productNonzero := Fraction.Field.mul_ne_zero_direct
    gcdNonzero reducedNonzero
  exact productNonzero (polynomialIdentity.symm.trans polynomialZero)
end Purelib.RootIsolation.Sturm.Count.Squarefree

end
