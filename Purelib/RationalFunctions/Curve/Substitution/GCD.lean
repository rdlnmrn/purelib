module
public import Purelib.Polynomial.Dense.GCD
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RationalFunctions.Curve.Substitution

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

section
@[expose] public section

/-!
# Finite global clearance for a rationally parameterized curve

The real and imaginary denominator-cleared substitutions are ordinary finite
dense coordinate polynomials.  Their executable extended gcd therefore
decides an important easy case: a nonzero constant gcd certifies that the
displayed polynomial has no root at any finite parameter of the curve.

Local root counts for a nonconstant gcd are left to the subsequent Sturm
layer; this module supplies the algebraic reduction and its proof.
-/

namespace Purelib.RationalFunctions.Curve.Substitution

open Purelib.Data
open Purelib.Polynomial
open Purelib.RationalFunctions
/-- Read the real coordinate polynomial of denominator-cleared substitution. -/
def realPolynomial
    (p : CoefficientPolynomial) (curve : Curve.RationalCurve) :
      (DensePolynomial
      Rational) :=
  Curve.clearedReal p curve

/-- Read the imaginary coordinate polynomial of denominator-cleared substitution. -/
def imaginaryPolynomial
    (p : CoefficientPolynomial) (curve : Curve.RationalCurve) :
      (DensePolynomial
      Rational) :=
  Curve.clearedImag p curve

/-- Compute the finite polynomial gcd of the two denominator-cleared coordinate polynomials. -/
def gcdPolynomial
    (p : CoefficientPolynomial) (curve : Curve.RationalCurve) :
      (DensePolynomial
      Rational) :=
  Dense.GCD.gcd (realPolynomial p curve)
    (imaginaryPolynomial p curve)
end Purelib.RationalFunctions.Curve.Substitution

end
