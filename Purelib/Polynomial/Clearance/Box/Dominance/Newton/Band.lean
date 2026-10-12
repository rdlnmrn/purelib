module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Bounds
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free eliminant-safe Newton bands

Four bounded eliminant searches choose axis-parallel sides at distances
between `r` and `2r` from an extracted Newton center.  The sides carry
full-line Bézout clearances, while finite Taylor estimates transfer affine
winding four to the original polynomial on the selected rectangle.
-/

namespace Purelib.Polynomial.Clearance.Box.Dominance.Newton.Band

/-- Finite Taylor dominance on every side of a selected Newton band. -/
def newtonBandBoundaryNormDominance
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient source : Box}
    {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
    (newton : Dense.Gaussian.Newton.Box.Squarefree.NewtonCenterCertificate
      p ambient source squarefree)
    (sourceRefines : source.Refines ambient) {r : Fraction.Rational}
    (positive : 0 < r)
    (band : Box.Band.Basic.BandBox (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) r)
    (targetRefines : band.box.Refines ambient)
    (displacementSmall : Data.Gaussian.Norm.Basic.normSq
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    (taylorSmall :
      2 * (Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
        Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2) ≤
          Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree ambient) :
    Clearance.Box.Dominance.Basic.BoundaryNormDominance
      (Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p source)
        (Dense.Gaussian.Newton.Box.Linearization.newtonError p source) band.box where
  margin := Dense.Gaussian.Newton.Box.Band.Bounds.bandDominanceMargin squarefree ambient r
  positive := Dense.Gaussian.Newton.Box.Band.Bounds.bandDominanceMargin_pos squarefree positive taylorSmall
  lower := by
    intro z boundary
    have errorBound := Dense.Gaussian.Newton.Box.Band.Bounds.newtonError_le_bandBudget newton sourceRefines band
      targetRefines
      displacementSmall boundary
    have linearBound := Dense.Gaussian.Newton.Box.Band.Bounds.newtonLinearization_band_boundary_lower newton band
      positive.le boundary
    have estimate := Purelib.Data.Rat.Fraction.Order.Arithmetic.sub_le_sub_direct linearBound errorBound
    simpa only [Dense.Gaussian.Newton.Box.Band.Bounds.bandDominanceMargin, Gaussian.Norm.Basic.normSq_eq_canonical]
      using estimate
end Purelib.Polynomial.Clearance.Box.Dominance.Newton.Band

end
