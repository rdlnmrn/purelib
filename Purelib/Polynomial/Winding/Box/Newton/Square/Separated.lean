module
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Clearance.Box.Boundary.Affine
import Purelib.Polynomial.Clearance.Box.Dominance.Newton.Square.Separated
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
import Purelib.Polynomial.Winding.Box.Affine
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Rouche
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
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

namespace Purelib.Polynomial.Winding.Box.Newton.Square.Separated

/-- Complete Newton-square winding transfer from explicit derivative
separation. -/
theorem
  quadrupledBoxWinding_eq_four_of_separatedNewtonSquare
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient source : Box}
    {separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (newton : Dense.Gaussian.Newton.Box.Certificate.SeparatedNewtonCenterCertificate
      p ambient source separation)
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
        separation.margin) :
    Winding.Box.Basic.quadrupledBoxWinding p
      (Box.Square.Centered.Affine.centeredSquare (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) r
        positive.le) = 4 := by
  let target := Box.Square.Centered.Affine.centeredSquare (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source)
    r positive.le
  have transfer := Winding.Box.Rouche.quadrupledBoxWinding_add_of_boundaryNormDominance
    (Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p source)
      (Dense.Gaussian.Newton.Box.Linearization.newtonError p source) target
    (Box.Square.Centered.centeredSquare_proper (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) positive)
    (Clearance.Box.Boundary.Affine.affineCoordinate_boundaryClearance newton.derivativeNonzero
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) positive)
    (Clearance.Box.Dominance.Newton.Square.Separated.separatedNewtonBoundaryNormDominance newton sourceRefines positive
      targetRefines displacementSmall taylorSmall)
  have sumIdentity := Dense.Gaussian.Newton.Box.Linearization.newtonLinearization_add_error_eq_normalize
    degreeAtLeastTwo source newton.derivativeNonzero
  rw [sumIdentity] at transfer
  calc
    Winding.Box.Basic.quadrupledBoxWinding p target =
        Winding.Box.Basic.quadrupledBoxWinding p.normalize target :=
      (Winding.Box.Basic.quadrupledBoxWinding_normalize p target).symm
    _ = Winding.Box.Basic.quadrupledBoxWinding (Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p source)
      target := transfer
    _ = 4 := Winding.Box.Affine.quadrupledBoxWinding_affineCoordinate_centeredSquare
      newton.derivativeNonzero (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) positive
end Purelib.Polynomial.Winding.Box.Newton.Square.Separated

end
