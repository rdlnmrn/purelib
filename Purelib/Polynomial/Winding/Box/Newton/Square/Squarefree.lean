module
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Clearance.Box.Boundary.Affine
import Purelib.Polynomial.Clearance.Box.Dominance.Newton.Square.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
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
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic

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

namespace Purelib.Polynomial.Winding.Box.Newton.Square.Squarefree

/-- The complete finite Rouché step, separated from the purely coefficient
identity that adds the Newton error back to the normalized polynomial. -/
theorem
  quadrupledBoxWinding_eq_four_of_newtonSquare_of_sumIdentity
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient source : Box}
    {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
    (newton : Squarefree.NewtonCenterCertificate p ambient source squarefree)
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
        Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree ambient)
    (sumIdentity : Linearization.newtonLinearization p source +
      Linearization.newtonError p source =
      p.normalize) :
    Basic.quadrupledBoxWinding p
      (Box.Square.Centered.Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
        positive.le) = 4 := by
  let target := Box.Square.Centered.Affine.centeredSquare (Anchor.anchorNewtonCenter p source)
    r positive.le
  have transfer := Rouche.quadrupledBoxWinding_add_of_boundaryNormDominance
    (Linearization.newtonLinearization p source)
      (Linearization.newtonError p source) target
    (Box.Square.Centered.centeredSquare_proper (Anchor.anchorNewtonCenter p source) positive)
    (Clearance.Box.Boundary.Affine.affineCoordinate_boundaryClearance newton.derivativeNonzero
      (Anchor.anchorNewtonCenter p source) positive)
    (Clearance.Box.Dominance.Newton.Square.Squarefree.newtonBoundaryNormDominance newton sourceRefines positive
      targetRefines
      displacementSmall taylorSmall)
  rw [sumIdentity] at transfer
  calc
    Basic.quadrupledBoxWinding p target =
        Basic.quadrupledBoxWinding p.normalize target :=
      (Basic.quadrupledBoxWinding_normalize p target).symm
    _ = Basic.quadrupledBoxWinding (Linearization.newtonLinearization p source)
      target := transfer
    _ = 4 := Affine.quadrupledBoxWinding_affineCoordinate_centeredSquare
      newton.derivativeNonzero (Anchor.anchorNewtonCenter p source) positive

/-- Complete choice-free Newton-square winding theorem in degree at least
two. -/
theorem quadrupledBoxWinding_eq_four_of_newtonSquare
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient source : Box}
    {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (newton : Squarefree.NewtonCenterCertificate p ambient source squarefree)
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
        Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree ambient) :
    Basic.quadrupledBoxWinding p
      (Box.Square.Centered.Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
        positive.le) = 4 :=
  quadrupledBoxWinding_eq_four_of_newtonSquare_of_sumIdentity newton
    sourceRefines positive targetRefines displacementSmall taylorSmall
    (Linearization.newtonLinearization_add_error_eq_normalize degreeAtLeastTwo source
      newton.derivativeNonzero)
end Purelib.Polynomial.Winding.Box.Newton.Square.Squarefree

end
