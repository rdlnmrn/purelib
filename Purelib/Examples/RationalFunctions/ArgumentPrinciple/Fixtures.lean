module

public import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Executable RFAP examples

These small displayed dense polynomials exercise both public branches.  The
first quotient has two coprime squarefree numerator zeros and one coprime
squarefree denominator pole.  The second has one repeated numerator factor;
its finite rational box has ordinary winding two rather than one.
-/

namespace Purelib.Examples.RationalFunctions.ArgumentPrinciple.Fixtures

open Purelib.Examples

/-- The monic linear Gaussian polynomial with its zero at zero. -/
def squarefreeNumerator :
  (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Gaussian.Linear.Translated.translatedCoordinate 0

/-- The monic linear Gaussian polynomial with its zero at one. -/
def squarefreeDenominator :
  (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Gaussian.Linear.Translated.translatedCoordinate 1

/-- The displayed numerator polynomial is nonzero. -/
theorem squarefreeNumerator_nonzero :
    squarefreeNumerator.isZero = false := by decide

/-- The displayed denominator polynomial is nonzero. -/
theorem squarefreeDenominator_nonzero :
    squarefreeDenominator.isZero = false := by decide
end Purelib.Examples.RationalFunctions.ArgumentPrinciple.Fixtures

end
