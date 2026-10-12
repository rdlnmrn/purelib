module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

section
public section

/-!
# Choice-free box-only finite constructive FTA

This is the paper-facing numerical layer over the explicit constructive
fraction and Gaussian representations.  The squarefree certificate is finite
dense extended-Euclid data.  Both axis eliminants are computed internally by
the fraction-free separated Sylvester construction.
-/

namespace Purelib.RootIsolation.FTA.Positive.Basic

open Purelib.Polynomial
open Purelib.RootIsolation

set_option genInjectivity false in
/-- A positive-degree box result retains an exact linear root or a higher-degree box family.

The linear constructor stores the displayed polynomial's exact Gaussian-rational
root and degree equation. The higher constructor retains its complete degree-many
shrinking-box isolation and the corresponding degree bound. -/
inductive PositiveResult (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- A retained exact Gaussian root of the original degree-one polynomial. -/ | linear (root :
    Dense.Gaussian.Roots.Certificate.ExactRoot p) (degree : p.natDegree = 1)
  /-- The original complete degree-sized box isolation for a polynomial of degree at least two. -/ | higher (boxes :
    FTA.Squarefree.BoxResult p) (degree : 2 ≤ p.natDegree)

constructive_injectivity PositiveResult

end Purelib.RootIsolation.FTA.Positive.Basic

end
