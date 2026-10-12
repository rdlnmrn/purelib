module
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.GCD

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite coprimality and squarefree certificates

A certificate records that the output of executable extended Euclid is one
displayed nonzero constant.  Rescaling its returned Bézout coefficients gives
an identity equal to `1` at every queried point.  No root set, coefficient
extensionality over an infinite carrier, or sparse polynomial is used.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.Decision

/-- The corresponding complete finite squarefreeness decision. -/
abbrev SquarefreeOutcome (p :
  CoefficientPolynomial) :=
  Dense.Gaussian.Coprime.Decision.CoprimeOutcome p (Dense.Gaussian.GCD.derivative p)

/-- Run executable Euclidean coprimality on the nonzero polynomial and its derivative, returning the complete
squarefreeness outcome. -/
def squarefreeOutcome
    (p : CoefficientPolynomial) (nonzero : p.isZero = false) :
    SquarefreeOutcome p :=
  Dense.Gaussian.Coprime.Decision.coprimeOutcome p (Dense.Gaussian.GCD.derivative p) (Or.inl nonzero)

/-- Executable Boolean view of the same finite squarefreeness decision. -/
def squarefreeCheck (p :
  CoefficientPolynomial) : Bool :=
  let result := Dense.Gaussian.GCD.extendedGCD p
    (Dense.Gaussian.GCD.derivative p)
  !result.gcd.isZero && decide (result.gcd.natDegree = 0)
end Purelib.Polynomial.Dense.Gaussian.Squarefree.Decision

end
