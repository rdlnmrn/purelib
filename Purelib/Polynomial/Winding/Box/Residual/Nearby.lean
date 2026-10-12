module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual.Nearby
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Residual
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic

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

namespace Purelib.Polynomial.Winding.Box.Residual.Nearby

/-- A nearby clear point contradicts nonzero raw winding by the finite
constant-dominance homotopy. -/
theorem quadrupledBoxWinding_eq_zero_of_nearby_clear_point
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) {ambient small : Box}
    (degreePositive : 0 < p.natDegree)
    (refines : small.Refines ambient) (proper : small.Proper)
    (certificate : Dense.Gaussian.Bounds.Box.Residual.Nearby.NearbyClearPointCertificate p ambient small) :
    Winding.Box.Basic.quadrupledBoxWinding p small = 0 :=
  Winding.Box.Residual.quadrupledBoxWinding_eq_zero_of_anchorResidualBound_lt p degreePositive
    refines proper
      (Dense.Gaussian.Bounds.Box.Residual.Nearby.anchorResidualBound_lt_of_nearby_clear_point p refines certificate)
end Purelib.Polynomial.Winding.Box.Residual.Nearby

end
