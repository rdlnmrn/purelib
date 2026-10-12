module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
public import Purelib.Polynomial.Dense.Rational.Pair.Reduction

open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

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

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Reduced

/-- Gcd-reduced doubled Cauchy index. -/
def reducedCauchyIndex2
    (numerator denominator : CoordinatePolynomial) (lower upper : Fraction.Rational) : Int :=
  Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 (Dense.Rational.Pair.Reduction.reducedNumerator numerator
    denominator)
    (Dense.Rational.Pair.Reduction.reducedDenominator numerator denominator) lower upper

/-- The gcd-reduced doubled Cauchy index splits additively at any displayed intermediate endpoint. -/
theorem reducedCauchyIndex2_add
    (numerator denominator : CoordinatePolynomial) (lower middle upper : Fraction.Rational) :
    reducedCauchyIndex2 numerator denominator lower upper =
      reducedCauchyIndex2 numerator denominator lower middle +
        reducedCauchyIndex2 numerator denominator middle upper :=
  Dense.Rational.CauchyIndex.Basic.cauchyIndex2_add _ _ _ _ _

/-- Reversing the endpoints negates the gcd-reduced doubled Cauchy index. -/
theorem reducedCauchyIndex2_reverse
    (numerator denominator : CoordinatePolynomial) (lower upper : Fraction.Rational) :
    reducedCauchyIndex2 numerator denominator upper lower =
      -reducedCauchyIndex2 numerator denominator lower upper :=
  Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse _ _ _ _
end Purelib.Polynomial.Dense.Rational.CauchyIndex.Reduced

end
