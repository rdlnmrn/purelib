module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Operations
public import Purelib.Polynomial.Clearance.Box.Dominance.Newton.Square.Squarefree
public import Purelib.Polynomial.Clearance.Box.Dominance.Sum
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic

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

namespace Purelib.Polynomial.Clearance.Box.Boundary.Newton.Square.Squarefree

/-- Coefficient-computed boundary clearance carried by the extracted Newton
square. -/
def newtonSquareBoundaryClearance
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient source : Box}
    {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
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
    Clearance.Box.Boundary.Basic.BoundaryClearance p
      (Box.Square.Centered.Affine.centeredSquare (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) r
        positive.le) := by
  let target := Box.Square.Centered.Affine.centeredSquare (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source)
    r positive.le
  let dominance := Clearance.Box.Dominance.Newton.Square.Squarefree.newtonBoundaryNormDominance newton sourceRefines
    positive
    targetRefines displacementSmall taylorSmall
  have sumClearance :=
    Clearance.Box.Dominance.Sum.boundaryClearance_add_of_boundaryNormDominance
      (Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p source)
        (Dense.Gaussian.Newton.Box.Linearization.newtonError p source) target
      (Box.Square.Centered.centeredSquare_proper (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source)
        positive) dominance
  have sumIdentity := Dense.Gaussian.Newton.Box.Linearization.newtonLinearization_add_error_eq_normalize
    degreeAtLeastTwo source newton.derivativeNonzero
  rw [sumIdentity] at sumClearance
  exact Clearance.Box.Boundary.Basic.BoundaryClearance.ofNormalize sumClearance
end Purelib.Polynomial.Clearance.Box.Boundary.Newton.Square.Squarefree

end
