module

import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
public import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free box-only finite constructive FTA

This is the paper-facing numerical layer over the explicit constructive
fraction and Gaussian representations.  The squarefree certificate is finite
dense extended-Euclid data.  Both axis eliminants are computed internally by
the fraction-free separated Sylvester construction.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Roots.Certificate

set_option genInjectivity false in
/-- The exact Gaussian-rational root returned for a degree-one polynomial. -/
structure ExactRoot (p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  where
  /-- The retained exact Gaussian rational root. -/ point : Gaussian.Basic.Canonical
  /-- The original polynomial evaluates to zero at the retained point. -/ root : p.eval point = 0

constructive_injectivity ExactRoot

end Purelib.Polynomial.Dense.Gaussian.Roots.Certificate

end
