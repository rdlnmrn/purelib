module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Separated
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Gaussian.Newton.Box

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

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

namespace Purelib.Polynomial.Clearance.Box.Dominance.Newton.Square.Separated

/-- Taylor dominance on the Newton square from a generic separation
certificate. -/
def separatedNewtonBoundaryNormDominance
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient source : Box}
    {separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient}
    (newton : Certificate.SeparatedNewtonCenterCertificate
      p ambient source separation)
    (sourceRefines : source.Refines ambient)
    {r : Fraction.Rational} (positive : 0 < r)
    (targetRefines :
      (Box.Square.Centered.Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
        positive.le).Refines ambient)
    (displacementSmall :
      Gaussian.Norm.Basic.normSq (Anchor.anchorNewtonCenter p source - source.anchor)
        ≤ r ^ 2)
    (taylorSmall :
      2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2) ≤
        separation.margin) :
    Basic.BoundaryNormDominance
      (Linearization.newtonLinearization p source)
        (Linearization.newtonError p source)
      (Box.Square.Centered.Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
        positive.le) where
  margin := Square.Separated.separatedNewtonDominanceMargin separation r
  positive := Square.Separated.separatedNewtonDominanceMargin_pos separation positive
    taylorSmall
  lower := by
    intro z boundary
    have estimate := Square.Separated.separatedNewtonDominanceMargin_le newton
      sourceRefines positive targetRefines displacementSmall boundary
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using estimate
end Purelib.Polynomial.Clearance.Box.Dominance.Newton.Square.Separated

end
