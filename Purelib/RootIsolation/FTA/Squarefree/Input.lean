module

import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Degree
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial

public section

/-!
# Choice-free box-only finite constructive FTA

This is the paper-facing numerical layer over the explicit constructive
fraction and Gaussian representations.  The squarefree certificate is finite
dense extended-Euclid data.  Both axis eliminants are computed internally by
the fraction-free separated Sylvester construction.
-/

namespace Purelib.RootIsolation.FTA.Squarefree

set_option genInjectivity false in
/-- A finite squarefree input and degree bound for the original nonlinear polynomial.

The squarefree certificate and degree-at-least-two witness concern exactly the
supplied dense Gaussian polynomial, retaining its coefficients and finite Euclid
witnesses. -/
structure Input (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The polynomial's explicit finite squarefree certificate. -/ squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p
  /-- The displayed polynomial has natural degree at least two. -/ degreeAtLeastTwo : 2 ≤ p.natDegree

constructive_injectivity Input

namespace Input.mk

end Input.mk

namespace Input

open Purelib.RootIsolation
/-- The higher-degree isolation input has strictly positive degree. -/
theorem degreePositive {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input : Input
  p) :
    0 < p.natDegree :=
  (by decide : (0 : Nat) < 2).trans_le input.degreeAtLeastTwo

/-- The higher-degree isolation input is a nonzero polynomial. -/
theorem nonzero {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input : Input p) :
    p.isZero = false :=
  Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos
    input.degreePositive
end Input
end Purelib.RootIsolation.FTA.Squarefree

end
