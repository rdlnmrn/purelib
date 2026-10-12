module

import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

/-!
# Choice-free box-only finite constructive FTA

This is the paper-facing numerical layer over the explicit constructive
fraction and Gaussian representations.  The squarefree certificate is finite
dense extended-Euclid data.  Both axis eliminants are computed internally by
the fraction-free separated Sylvester construction.
-/

namespace Purelib.RootIsolation.FTA.Positive.Input

open Purelib.Polynomial

set_option genInjectivity false in
/-- A positive-degree polynomial input retains its finite squarefree certificate.

The degree witness and squarefree data belong to the same displayed polynomial.
The higher-degree constructor consumes that certificate, while the linear case
retains the exact degree-one equation. -/
structure PositiveInput (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The polynomial's explicit finite squarefree certificate. -/ squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p
  /-- The displayed polynomial has strictly positive natural degree. -/ degreePositive : 0 < p.natDegree

constructive_injectivity PositiveInput

end Purelib.RootIsolation.FTA.Positive.Input

end
