module
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Affine
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Dominance.Newton.Band
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Winding.Box.Affine
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Rouche
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Geometry.Rational.Box.Band.Bounds

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

namespace Purelib.Polynomial.Winding.Box.Newton.Band

/-- The eliminant-safe Newton band has raw winding four. -/
theorem quadrupledBoxWinding_eq_four_of_newtonBand
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient source : Box}
    {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
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
    Winding.Box.Basic.quadrupledBoxWinding p band.box = 4 := by
  have centerInside := band.center_strictly_inside positive
  have proper := band.proper positive
  let affineClearance : Clearance.Box.Boundary.Basic.BoundaryClearance
      (Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p source) band.box := by
    simpa only [Dense.Gaussian.Newton.Box.Linearization.newtonLinearization] using
      Clearance.Box.Boundary.Affine.affineCoordinate_boundaryClearanceBox newton.derivativeNonzero
        (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) centerInside.1 centerInside.2.1
        centerInside.2.2.1 centerInside.2.2.2
  let dominance := Clearance.Box.Dominance.Newton.Band.newtonBandBoundaryNormDominance newton sourceRefines
    positive band targetRefines displacementSmall taylorSmall
  have transfer := Winding.Box.Rouche.quadrupledBoxWinding_add_of_boundaryNormDominance
    (Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p source)
      (Dense.Gaussian.Newton.Box.Linearization.newtonError p source) band.box proper
    affineClearance dominance
  have sumIdentity := Dense.Gaussian.Newton.Box.Linearization.newtonLinearization_add_error_eq_normalize
    degreeAtLeastTwo source newton.derivativeNonzero
  rw [sumIdentity] at transfer
  calc
    Winding.Box.Basic.quadrupledBoxWinding p band.box =
        Winding.Box.Basic.quadrupledBoxWinding p.normalize band.box :=
      (Winding.Box.Basic.quadrupledBoxWinding_normalize p band.box).symm
    _ = Winding.Box.Basic.quadrupledBoxWinding (Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p source)
      band.box :=
      transfer
    _ = 4 := by
      simpa only [Dense.Gaussian.Newton.Box.Linearization.newtonLinearization] using
        Winding.Box.Affine.quadrupledBoxWinding_affineCoordinate newton.derivativeNonzero
          (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) centerInside.1 centerInside.2.1
          centerInside.2.2.1 centerInside.2.2.2
end Purelib.Polynomial.Winding.Box.Newton.Band

end
