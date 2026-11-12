module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Dominance.Majorant
public import Purelib.Polynomial.Clearance.Box.Dominance.Newton.Square.Separated
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Bounds
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Separated
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Dense.Gaussian.Newton.Box
open Purelib.Geometry.Rational.Box.Square.Centered

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

namespace Purelib.Polynomial.Clearance.Box.Boundary.Newton.Square.Separated

/-- Boundary clearance carried by a separated Newton square when the caller
supplies any positive upper bound for the Newton linearization on the square
boundary. -/
def
  separatedNewtonSquareBoundaryClearanceWithMajorant
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient source : Box}
    {separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (newton : Certificate.SeparatedNewtonCenterCertificate
      p ambient source separation)
    (sourceRefines : source.Refines ambient)
    {r : Fraction.Rational} (positive : 0 < r)
    (targetRefines :
      (Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
        positive.le).Refines ambient)
    (displacementSmall :
      Gaussian.Norm.Basic.normSq (Anchor.anchorNewtonCenter p source - source.anchor)
        ≤ r ^ 2)
    (taylorSmall :
      2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2) ≤
        separation.margin)
    (linearizationMajorant : Fraction.Rational)
    (linearizationMajorantPositive : 0 < linearizationMajorant)
    (linearizationUpper : ∀ z : Gaussian.Basic.Canonical,
      Box.Boundary.OnBoxBoundary
        (Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
          positive.le) z →
      Gaussian.Norm.Basic.normSq ((Linearization.newtonLinearization p source).eval
        z) ≤
        linearizationMajorant) :
    Basic.BoundaryClearance p
      (Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
        positive.le) := by
  let target := Affine.centeredSquare (Anchor.anchorNewtonCenter p source)
    r positive.le
  let dominance := Dominance.Newton.Square.Separated.separatedNewtonBoundaryNormDominance newton
    sourceRefines
    positive targetRefines displacementSmall taylorSmall
  have canonicalUpper : ∀ z : Gaussian.Basic.Canonical,
      Box.Boundary.OnBoxBoundary target z →
      Gaussian.Basic.Canonical.normSq
        ((Linearization.newtonLinearization p source).eval z) ≤ linearizationMajorant := by
    intro z boundary
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using linearizationUpper z boundary
  let sumClearance : Basic.BoundaryClearance
      (Linearization.newtonLinearization p source +
        Linearization.newtonError p source) target :=
          Dominance.Majorant.boundaryClearance_add_of_dominance_with_majorant
    (Linearization.newtonLinearization p source)
      (Linearization.newtonError p source) target dominance
    linearizationMajorant linearizationMajorantPositive canonicalUpper
  have sumIdentity := Linearization.newtonLinearization_add_error_eq_normalize
    degreeAtLeastTwo source newton.derivativeNonzero
  have sumBound : sumClearance.bound =
      Square.Separated.separatedNewtonDominanceMargin separation r ^ 2 /
        (4 * linearizationMajorant) := by
    change sumClearance.bound = dominance.margin ^ 2 /
      (4 * linearizationMajorant)
    exact Dominance.Majorant.boundaryClearance_add_of_dominance_with_majorant_bound
      (Linearization.newtonLinearization p source)
        (Linearization.newtonError p source) target dominance
      linearizationMajorant linearizationMajorantPositive canonicalUpper
  exact
    { bound := Square.Separated.separatedNewtonDominanceMargin separation r ^ 2 /
        (4 * linearizationMajorant)
      positive := by
        rw [← sumBound]
        exact sumClearance.positive
      lower := by
        intro z boundary
        rw [← sumBound]
        rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
        calc
          sumClearance.bound ≤
              Gaussian.Norm.Basic.normSq
                ((Linearization.newtonLinearization p source +
                  Linearization.newtonError p source).eval z) :=
            by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
              sumClearance.lower z boundary
          _ = Gaussian.Norm.Basic.normSq (p.eval z) := by
            rw [sumIdentity,
              Dense.Basic.DensePolynomial.eval_normalize] }

/-- The retained boundary-clearance bound is the squared dominance margin divided by four times the supplied positive
linearization majorant. -/
theorem
  separatedNewtonSquareBoundaryClearanceWithMajorant_bound
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient source : Box}
    {separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (newton : Certificate.SeparatedNewtonCenterCertificate
      p ambient source separation)
    (sourceRefines : source.Refines ambient)
    {r : Fraction.Rational} (positive : 0 < r)
    (targetRefines :
      (Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
        positive.le).Refines ambient)
    (displacementSmall :
      Gaussian.Norm.Basic.normSq (Anchor.anchorNewtonCenter p source - source.anchor)
        ≤ r ^ 2)
    (taylorSmall :
      2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2) ≤
        separation.margin)
    (linearizationMajorant : Fraction.Rational)
    (linearizationMajorantPositive : 0 < linearizationMajorant)
    (linearizationUpper : ∀ z : Gaussian.Basic.Canonical,
      Box.Boundary.OnBoxBoundary
        (Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
          positive.le) z →
      Gaussian.Norm.Basic.normSq ((Linearization.newtonLinearization p source).eval
        z) ≤
        linearizationMajorant) :
    (separatedNewtonSquareBoundaryClearanceWithMajorant degreeAtLeastTwo
      newton sourceRefines positive targetRefines displacementSmall
      taylorSmall linearizationMajorant linearizationMajorantPositive
      linearizationUpper).bound =
        Square.Separated.separatedNewtonDominanceMargin separation r ^ 2 /
          (4 * linearizationMajorant) := by
  unfold separatedNewtonSquareBoundaryClearanceWithMajorant
  rfl

/-- Coefficient-computed specialization using the ordinary dense derivative
majorant. -/
def separatedNewtonSquareBoundaryClearance
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient source : Box}
    {separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (newton : Certificate.SeparatedNewtonCenterCertificate
      p ambient source separation)
    (sourceRefines : source.Refines ambient)
    {r : Fraction.Rational} (positive : 0 < r)
    (targetRefines :
      (Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
        positive.le).Refines ambient)
    (displacementSmall :
      Gaussian.Norm.Basic.normSq (Anchor.anchorNewtonCenter p source - source.anchor)
        ≤ r ^ 2)
    (taylorSmall :
      2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2) ≤
        separation.margin) :
    Basic.BoundaryClearance p
      (Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
        positive.le) :=
  separatedNewtonSquareBoundaryClearanceWithMajorant degreeAtLeastTwo
    newton
    sourceRefines positive targetRefines displacementSmall taylorSmall
    (Square.Bounds.separatedNewtonLinearizationMajorant p ambient r)
    (Square.Bounds.separatedNewtonLinearizationMajorant_pos p ambient positive)
    (fun _z boundary => Square.Bounds.newtonLinearization_boundary_le_majorant
      sourceRefines positive boundary)

end Purelib.Polynomial.Clearance.Box.Boundary.Newton.Square.Separated

end
