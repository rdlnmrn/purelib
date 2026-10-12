module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Bezout
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free local residual extraction

A fixed rational corner of a shrinking box supplies the local sample.  Finite
Horner bounds and the box diagonal bound its residual variation.  If that
sample value were larger than the variation, a finite Rouché contraction to
the nonzero constant path would force raw winding zero.  Thus every proper
nonzero-winding box has an explicitly small rational residual.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree

/-- A Newton-center certificate with separation supplied by a squarefree Bézout identity.

The certificate retains the same polynomial, ambient box and source box as the underlying separated construction. -/
abbrev NewtonCenterCertificate
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient small : Box)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) :=
  Dense.Gaussian.Newton.Box.Certificate.SeparatedNewtonCenterCertificate p ambient small
    (Dense.Gaussian.Derivative.Separation.Bezout.ofSquarefree squarefree ambient)
end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree

end

section
@[expose] public section

/-!
# Choice-free local Newton-square extraction

A finite raw-winding subdivision first crosses explicit residual, protected
boundary, displacement, and Taylor thresholds.  The exact rational Newton
point then centers a strictly nested winding-one square.  No root is selected
and no completed or infinite carrier is used.
-/

namespace Purelib.RootIsolation.Newton.Extraction
end Purelib.RootIsolation.Newton.Extraction

end

section
@[expose] public section

/-!
# Choice-free refinement to a certified Newton point

The raw nonzero-winding subdivision is iterated to a coefficient-computed
positive diagonal threshold.  Its explicit contraction bound then supplies
the small residual required by the finite Bézout derivative argument.
-/

namespace Purelib.RootIsolation.Newton.Raw
end Purelib.RootIsolation.Newton.Raw

end

section
@[expose] public section

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
-/

namespace Purelib.RootIsolation.Newton.Winding
end Purelib.RootIsolation.Newton.Winding

end
