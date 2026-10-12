module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Value
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootOwners
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootJoins
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples
import Init.ByCases
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels

public section

/-!
# Common cap primitives at the actual inverse outer boundary

The scaled affine root is divided by the retained cap model's regular root
at its actual inverse point. This gives the same intrinsic coordinate and
polynomial primitive as the inner cap. The disk certificate supplies that
point's model validity; no collar endpoint or inverse endpoint chord is
substituted for it.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates

open Purelib

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners

open Purelib.Curves.Hyperelliptic.Differentials

open Purelib.Geometry

open Purelib.Geometry.Rational.Box

open Purelib.Polynomial.Approximation.Gaussian.Evaluation

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Topology

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Name

open Purelib.Riemann.RootContinuation
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames (CoherentNamed NamedEquivalent ScaledRoot
  factor)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates (RootCoordinate)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner (polynomialEval)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {point :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval point)}

set_option genInjectivity false in
/-- The actual reciprocal disk occurrence and its retained regular cap root, quotient coordinate and attached winding
owner.

The indexed fields retain the supplied owners, channels and exact cached
data. Their identities bind each displayed field to those same inputs. -/
structure Overlap (cap : ReciprocalInnerInverse.Data curve collar) (point : InverseRootPolynomial.Gaussian)
    (owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point)) where
  /-- The retained original cap-model root channel at this exact reciprocal disk point. -/ regular : Owners.DiskPoint
    cap point
  /-- The retained certificate of the original supplied reciprocal winding owner. -/ reciprocal :
    CertifiedSquareRoot.Certificate ((HyperellipticReciprocal.polynomial curve).eval point)
  /-- The retained reciprocal root certificate is exactly the original owner's certificate. -/ reciprocal_eq :
    reciprocal = owner.certificate owner.parameterNonzero
  /-- The prepared quotient of the original reciprocal and regular root channels with its exact parity radicand. -/
    coordinate : RootCoordinate reciprocal regular.certificate (point ^ HyperellipticReciprocal.originOrder curve)
  /-- The retained winding-owner attachment to the exact original prepared quotient coordinate channel. -/ attached :
    SquareRootChannelOwnership.Attachment coordinate.prepared.denominator (point ^ HyperellipticReciprocal.originOrder
    curve)

constructive_injectivity Overlap

namespace Overlap

/-- Consume a previously retained disk root and the actual reciprocal owner. -/
@[expose] def ofPoint (regular : Owners.DiskPoint cap point)
    (owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point)) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap cap point owner := by
  let reciprocal := owner.certificate owner.parameterNonzero
  have identity : cap.polynomial.eval point * point ^ HyperellipticReciprocal.originOrder curve =
      (HyperellipticReciprocal.polynomial curve).eval point := by
    rw [cap.polynomial_eq, HyperellipticReciprocal.polynomial_eval]
  have nonzero : point ^ HyperellipticReciprocal.originOrder curve ≠ 0 := by
    intro zero
    apply owner.parameterNonzero
    exact identity.symm.trans (by rw [zero, Data.Gaussian.Basic.mul_zero])
  let coordinate := RootCoordinate.build reciprocal regular.certificate _ nonzero identity
  exact ⟨regular, reciprocal, rfl, coordinate, SquareRootChannelOwnership.attach coordinate.certificate⟩

/-- Build the retained original regular disk channel and quotient coordinates for the supplied reciprocal owner. -/
@[expose] def build (cap : ReciprocalInnerInverse.Data curve collar) (point : InverseRootPolynomial.Gaussian)
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point)
    (owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point)) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap cap point owner :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.ofPoint (DiskPoint.build cap point inside) owner

/-- The quotient coordinate reconstructs the very scaled root supplied at this point, including its operational
presentation and sheet. -/
@[expose] def reconstruct (overlap : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap cap point owner) :
    NamedEquivalent (Coherent.CoherentNamed.mul overlap.coordinate.prepared.denominator
      overlap.regular.certificate.value).name
      overlap.reciprocal.value.name := overlap.coordinate.reconstruct

/-- The same retained polynomial primitive used by the inner cap, evaluated at this disk point's operational coordinate.
-/
@[expose] def chartPrimitive (overlap : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap cap point owner)
  {differential : Differentials.Basic.Differential genus} {index : Nat} {box : Rational.Box}
    (sample : Primitives.Sample cap differential index box) : CoherentNamed :=
  if HyperellipticReciprocal.originOrder curve = 0 then
    Coherent.CoherentNamed.mul overlap.coordinate.prepared.denominator (Horner.polynomialEval sample.primitive.value
      (Coherent.CoherentNamed.Coherence.exact point))
  else Horner.polynomialEval sample.primitive.value overlap.coordinate.prepared.denominator

/-- At an inner-cap point the disk view preserves the existing coordinate channel. Both presentations use the same
supplied reciprocal occurrence. -/
@[expose] def innerCoordinate (outer : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap cap point owner)
  (inner : RootCoordinates.Overlap cap point owner) :
    NamedEquivalent outer.coordinate.prepared.denominator.name inner.coordinate.prepared.denominator.name :=
  outer.coordinate.equivalent inner.coordinate (by
    rw [outer.reciprocal_eq, inner.reciprocal_eq]
    exact Equivalence.NamedEquivalent.refl _) (by
      rw [inner.regularRoot_eq]
      exact outer.regular.innerEquivalent inner.regular)

/-- The exterior and inner-cap evaluators name the same primitive wherever both domain certificates apply.

Both evaluators share the retained finite polynomial sample. The regular or
ramified origin branch transports the same operational coordinate comparison. -/
@[expose] def innerPrimitive (outer : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap cap point owner)
  (inner : RootCoordinates.Overlap cap point owner)
    {differential : Differentials.Basic.Differential genus} {index : Nat} {box : Rational.Box}
    (sample : Primitives.Sample cap differential index box) :
    NamedEquivalent (outer.chartPrimitive sample).name (inner.chartPrimitive sample).name := by
  by_cases regular : HyperellipticReciprocal.originOrder curve = 0
  · rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.chartPrimitive,
      RootCoordinates.Overlap.chartPrimitive, if_pos regular, if_pos regular]
    exact Coherent.Arithmetic.Product.Congruence.coherentMul_respects _ _ _ _ (outer.innerCoordinate inner)
      (Equivalence.NamedEquivalent.refl _)
  · rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.chartPrimitive,
      RootCoordinates.Overlap.chartPrimitive, if_neg regular, if_neg regular]
    exact Horner.horner_respects _ _ (Coherent.CoherentNamed.Coherence.exact 0) (Coherent.CoherentNamed.Coherence.exact
      0) (outer.innerCoordinate inner)
      (Equivalence.NamedEquivalent.refl _) sample.primitive.value.coeffs

end Overlap

variable {source : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}

set_option genInjectivity false in
/-- The retained affine owner, its scaled root, its attached reciprocal owner, and its common cap coordinate all refer
to the actual inverse boundary point.

The indexed fields retain the supplied owners, channels and exact cached
data. Their identities bind each displayed field to those same inputs. -/
structure BoundaryData {parameter : InverseRootPolynomial.Gaussian} (original : CertifiedSquareRoot.Certificate
  parameter)
    (multiplier target : InverseRootPolynomial.Gaussian) (onBoundary : Prop)
    (Coordinates : SquareRootContinuationChain.Owner target → Type 1) where
  /-- The original affine source point satisfies its retained ambient-boundary condition. -/ boundary : onBoundary
  /-- The retained exact reciprocal scaling of the original affine root certificate. -/ scaled : ScaledRoot original
    multiplier target
  /-- The retained winding owner attached to the exact original scaled affine root channel. -/ attached :
    SquareRootChannelOwnership.Attachment scaled.prepared.denominator target
  /-- The original reciprocal disk coordinates built on this exact retained attached owner. -/ coordinates : Coordinates
    attached.owner

constructive_injectivity BoundaryData

/-- The original affine boundary owner with its retained reciprocal scaling and cap-coordinate occurrence at the actual
inverse point. -/
abbrev BoundaryPoint (cap : ReciprocalInnerInverse.Data curve collar) (source : InverseRootPolynomial.Gaussian)
    (original : SquareRootContinuationChain.Owner (curve.polynomial.eval source)) :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.BoundaryData (original.certificate original.parameterNonzero)
    (factor genus source)
    ((HyperellipticReciprocal.polynomial curve).eval source⁻¹)
    (Boundary.OnBoxBoundary (Cuts.Ambient curve) source)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap cap source⁻¹)

namespace BoundaryPoint

/-- Retain the original affine boundary owner, its reciprocal root scaling and actual inverse-point disk coordinates. -/
@[expose] def build (cap : ReciprocalInnerInverse.Data curve collar) {source : InverseRootPolynomial.Gaussian}
    (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve) source)
    (original : SquareRootContinuationChain.Owner (curve.polynomial.eval source)) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.BoundaryPoint cap source original :=
  let scaled := ReciprocalRootNames.ofBoundaryOwner curve source boundary original
  let attached := ReciprocalRootOwners.attach scaled
  ⟨boundary, scaled, attached, Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.ofPoint
    (Owners.atInverseBoundary cap boundary) attached.owner⟩

/-- The differential coefficient retains the reciprocal Jacobian sign and is operationally tied to the original affine
root, at its actual point. -/
@[expose] def coefficient_transport {original : SquareRootContinuationChain.Owner (curve.polynomial.eval source)}
    (point : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.BoundaryPoint cap source original) (differential :
      Differentials.Basic.Differential genus) :
    NamedEquivalent (ReciprocalRootOwners.coefficient differential source point.attached.owner).name
      (Coherent.CoherentNamed.mul (Coherent.CoherentNamed.Coherence.exact (-(source ^ 2))) (Value.differentialValue
        differential source
        (original.certificate original.parameterNonzero).value (original.certificate
          original.parameterNonzero).apart)).name :=
  ReciprocalRootOwners.coefficient_transport differential source
    (PreparedExteriorReciprocal.boundary_nonzero point.boundary) point.scaled point.attached

end BoundaryPoint

namespace Overlap

/-- Consume the reciprocal owner already retained by a source-boundary reading. The source point is the prepared cell's
actual inverse centre. -/
@[expose] def ofPrepared (cap : ReciprocalInnerInverse.Data curve collar)
    {differential : Differentials.Basic.Differential genus} {parent : PreparedSubdivisionModelCore.CenteredEdge curve
      differential}
    {boundary : PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)}
    (attached : PreparedReciprocalSamples.Attachment parent boundary) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap cap (parent.edge.point 0)⁻¹ attached.owner :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.ofPoint (Owners.atInverseBoundary cap (boundary.point
    parent.edge.baseInside)) attached.owner

end Overlap
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
