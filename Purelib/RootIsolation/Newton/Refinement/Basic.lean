module

import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.RootIsolation.State.Raw
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Bezout
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Certified Newton raw-state refinements

The original polynomial, ambient box and squarefree certificate index the retained raw-winding state and the
Newton-center certificate for that exact state box.
-/

public section

namespace Purelib.RootIsolation.Newton.Refinement.Basic

set_option genInjectivity false in
/-- The complete output at the first certified Newton scale.

The original polynomial, ambient box and squarefree certificate index the retained raw-winding state and the
Newton-center certificate for that exact state box. -/
structure Output
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) where
  /-- The retained nonzero-winding state at the certified Newton scale. -/ state : State.Raw.RawWindingState p ambient
  /-- A Newton-center certificate for that exact state box and the supplied squarefree certificate. -/ newton :
    Dense.Gaussian.Newton.Box.Squarefree.NewtonCenterCertificate p ambient state.box squarefree

constructive_injectivity Output

end Purelib.RootIsolation.Newton.Refinement.Basic

end
