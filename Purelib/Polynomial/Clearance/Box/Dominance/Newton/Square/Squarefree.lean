module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
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

namespace Purelib.Polynomial.Clearance.Box.Dominance.Newton.Square.Squarefree

/-- Taylor dominance on the complete Newton-centered square boundary. -/
def newtonBoundaryNormDominance
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient source : Box}
    {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
    (newton : Dense.Gaussian.Newton.Box.Squarefree.NewtonCenterCertificate p ambient source squarefree)
    (sourceRefines : source.Refines ambient)
    {r : Fraction.Rational} (positive : 0 < r)
    (targetRefines :
      (Box.Square.Centered.Affine.centeredSquare (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) r
        positive.le).Refines ambient)
    (displacementSmall :
      Data.Gaussian.Norm.Basic.normSq (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor)
        ≤ r ^ 2)
    (taylorSmall :
      2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2) ≤
        Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree ambient) :
    Clearance.Box.Dominance.Basic.BoundaryNormDominance
      (Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p source)
        (Dense.Gaussian.Newton.Box.Linearization.newtonError p source)
      (Box.Square.Centered.Affine.centeredSquare (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) r
        positive.le) where
  margin := Dense.Gaussian.Newton.Box.Square.Squarefree.newtonDominanceMargin squarefree ambient r
  positive := Dense.Gaussian.Newton.Box.Square.Squarefree.newtonDominanceMargin_pos squarefree positive taylorSmall
  lower := by
    intro z boundary
    have lower := Dense.Gaussian.Newton.Box.Square.Squarefree.newtonDominanceMargin_le
      (p := p) (ambient := ambient) (source := source) (squarefree := squarefree)
      newton sourceRefines positive targetRefines displacementSmall boundary
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using lower
end Purelib.Polynomial.Clearance.Box.Dominance.Newton.Square.Squarefree

end
