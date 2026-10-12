module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field

open Purelib.Data.Gaussian.Basic (Canonical)

section
@[expose] public section

/-!
# Two-way residual and chordal bounds for rational functions

For a reduced coprime pair, a protectedState source track has a uniform positive
margin for the opposite polynomial.  This converts the polynomial
box-to-residual and residual-to-box theorems into corresponding theorems for
the quotient.  Swapping source and opposite gives the pole statements.
-/

namespace Purelib.RationalFunctions.Residual.Basic

open Purelib.Data in
open Purelib.Polynomial in
/-- Compute the quadrance of the displayed source evaluation divided by the opposite evaluation.

The field quotient is total. Quantitative cancellation results separately require the opposite evaluation to be nonzero.
-/
def quotientResidualSq
    (source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (sample :
      Canonical) : Rat.Fraction.Rational
      :=
  Canonical.normSq (source.eval sample / opposite.eval sample)

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- The squared quotient residual is nonnegative. -/
theorem quotientResidualSq_nonneg
    (source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (sample :
      Canonical) :
    0 ≤ quotientResidualSq source opposite sample :=
  Canonical.normSq_nonneg _

end Purelib.RationalFunctions.Residual.Basic

end
