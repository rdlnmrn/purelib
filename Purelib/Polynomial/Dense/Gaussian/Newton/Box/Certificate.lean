module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

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

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate

set_option genInjectivity false in
/-- Proof-bearing finite output of the small raw-winding Newton step, using
only the displayed derivative-separation resource actually consumed by the
calculation. -/
structure SeparatedNewtonCenterCertificate
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient small : Box)
    (separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient)
      where
  /-- The retained exact Gaussian Newton center. -/ point : Gaussian.Basic.Canonical
  /-- The retained point is exactly the Newton center computed from the original small-box anchor. -/ point_eq : point =
    Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p small
  /-- The anchor residual quadrance fits the computed ambient-to-small-box variation budget. -/ residual :
    Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) ≤
    Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small
  /-- The polynomial derivative at the original anchor is nonzero. -/ derivativeNonzero :
    (Dense.Gaussian.GCD.derivative p).eval small.anchor ≠ 0
  /-- The derivative quadrance at the original anchor is bounded below by the retained separation margin. -/
    derivativeLower : separation.margin ≤
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative p).eval small.anchor)
  /-- The center displacement is bounded by the residual budget times inverse derivative quadrance. -/ displacement :
    Data.Gaussian.Norm.Basic.normSq (point - small.anchor) ≤
    Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small *
      (Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative p).eval small.anchor))⁻¹
  /-- The center displacement is bounded by the residual budget divided by the retained derivative margin. -/
    displacementMargin : Data.Gaussian.Norm.Basic.normSq (point - small.anchor) ≤
    Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small / separation.margin

constructive_injectivity SeparatedNewtonCenterCertificate

end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate

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
