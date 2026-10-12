module
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn
public import Purelib.Polynomial.Elimination.Separated.Scalar

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

namespace Purelib.Polynomial.Elimination.Axis.Separated.Eliminant

/-- Construct the horizontal rational eliminant by applying the separated scalar construction to the quarter-turned
polynomial. -/
def horizontalEliminant (p :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) : Dense.Rational.Basic.CoordinatePolynomial
  :=
  Elimination.Separated.Scalar.scalarEliminant (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p)

/-- The horizontal eliminant is nonzero whenever the original Gaussian polynomial is nonzero. -/
theorem horizontalEliminant_nonzero (p :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) :
    (horizontalEliminant p).isZero = false :=
  Elimination.Separated.Scalar.scalarEliminant_nonzero (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p)
    (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn_nonzero p nonzero)
end Purelib.Polynomial.Elimination.Axis.Separated.Eliminant

end
