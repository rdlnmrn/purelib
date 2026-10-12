module

import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite constructive rational-function argument principle

This paper-facing addendum combines executable gcd cancellation, the
polynomial box theorem, quantitative coprime separation, and the quotient
winding law.  The first public result below is the higher-degree squarefree
core.  It returns the numerator and denominator track families without
copying the polynomial isolation algorithm.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide

/-! ## Total squarefree specialization -/

set_option genInjectivity false in
/-- One orientation of a nonzero squarefree reduced cofactor against its
coprime opposite cofactor. -/
structure SquarefreeSideInput
    (source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The executable squarefree certificate for the original oriented source polynomial. -/ sourceSquarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate source
  /-- The original source polynomial has a nonzero normalized coefficient table. -/ sourceNonzero : source.isZero =
    false
  /-- The retained opposite polynomial has a nonzero normalized coefficient table. -/ oppositeNonzero : opposite.isZero
    = false
  /-- The executable coprimality certificate relates these exact source and opposite polynomials. -/
    sourceOppositeCoprime :
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate source opposite

constructive_injectivity SquarefreeSideInput

end Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide

end
