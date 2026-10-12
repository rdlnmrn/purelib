module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
public import Purelib.Riemann.Meshes.UniformPrimitiveMesh
public import Purelib.Riemann.RootContinuation.IntersectedRootContinuation
public import Purelib.Riemann.Integration.CheckedPrimitiveNeighborhoods
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Newton.Restart.Separated.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.AlignedInverseRootSeed
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.Polynomial.Power.Gaussian
import Mathlib.Order.Basic

/-!
# Uniform primitive patches on the actual prepared sheet

Uniform reconditioning need not refine the inherited box.  The common source
bridge and intersection continuation nevertheless identify every patch-point
owner with the actual prepared query.  No additional radius restriction is
introduced beyond the proved patch containment and the prepared edge's own
continuation contract.
-/

public section

namespace Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility

open Purelib.Polynomial.Dense.Gaussian
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.SquareRoot.Clearance

open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods.Bounds (PreparedSeed)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (Mesh)
open Purelib.Riemann.Integration.CheckedPrimitiveNeighborhoods (grow grow_base grow_radius_ge grow_box_refines)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
/-- The original dense Gaussian polynomial carrier. -/
private abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The rational Gaussian box carrier. -/
private abbrev Box := Purelib.Geometry.Rational.Box
/-- The exact rational Gaussian carrier. -/
private abbrev Gaussian := Purelib.Data.Gaussian.Basic.Canonical
/-- The exact rational coordinate carrier. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)

/-- The retained equivalence relation between original coherent Gaussian names. -/
abbrev NamedEquivalent := Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent

namespace Bounds.PreparedSeed

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment polynomial ambient start finish} {bounds : Bounds
    segment}
  {parameter : Purelib.Data.Rat.Fraction.Rational} {inside : 0 ≤ parameter ∧ parameter ≤ 1}
  {owner : Owner (polynomial.eval (segment.pointAt parameter))}

/-- Compare original reading and sample owners through the retained common bridge of a uniform seed.

Each owner refines its own original starting box and satisfies its own movement allowance; their bridge retains strict
containment in both original boxes. -/
@[expose] def ownerEquivalent (seed : PreparedSeed bounds parameter inside owner)
    {point : Basic.Canonical}
    (reading : Owner (polynomial.eval point))
    (readingRefines : reading.track.initial.box.Refines owner.track.initial.box)
    (readingSmall : normSq (polynomial.eval (segment.pointAt parameter) - polynomial.eval point) <
      owner.track.initial.clearance.bound)
    (sample : Owner (polynomial.eval point))
    (sampleRefines : sample.track.initial.box.Refines seed.aligned.seed.owner.track.initial.box)
    (seedSmall : normSq (polynomial.eval (segment.pointAt parameter) - polynomial.eval point) <
      seed.aligned.seed.owner.track.initial.clearance.bound) :
    NamedEquivalent (SquareRootTrackEquivalence.ownerRootName reading.parameterNonzero reading)
      (SquareRootTrackEquivalence.ownerRootName sample.parameterNonzero sample) := by
  let common : Owner (polynomial.eval (segment.pointAt parameter)) :=
    ⟨owner.parameterNonzero, _, UniformSquareRootPreparation.bridgeTrack segment parameter inside owner
      bounds.rootDiameter bounds.rootDiameter_positive⟩
  have strictOriginal : common.track.initial.box.StrictInterior owner.track.initial.box :=
    UniformSquareRootPreparation.bridgeTrack_initial_strict_owner segment parameter inside owner
      bounds.rootDiameter_positive
  have strictSeed : common.track.initial.box.StrictInterior seed.aligned.seed.owner.track.initial.box := by
    rw [seed.owner_eq]
    exact UniformSquareRootPreparation.bridgeTrack_initial_strict_prepared segment parameter inside owner
      bounds.rootDiameter_positive
  exact IntersectedRootContinuation.ownersEquivalent reading.parameterNonzero
    owner seed.aligned.seed.owner common strictOriginal strictSeed readingSmall
    seedSmall reading sample readingRefines sampleRefines

/-- Identify a uniform patch-point certificate with an original target-owner reading.

The retained point belongs to the exact neighborhood, whose movement and sample refinement certificates supply the seed
comparison. -/
@[expose] def pointEquivalent (seed : PreparedSeed bounds parameter inside owner) (count : Nat)
    {point : Basic.Canonical} (pointInside : (seed.neighborhood count).box.Contains point)
    (reading : Owner (polynomial.eval point))
    (readingRefines : reading.track.initial.box.Refines owner.track.initial.box)
    (readingSmall : normSq (polynomial.eval (segment.pointAt parameter) - polynomial.eval point) <
      owner.track.initial.clearance.bound)
    (sample : ContinuedNeighborhood.Point (seed.neighborhood count) point) :
    NamedEquivalent (SquareRootTrackEquivalence.ownerRootName reading.parameterNonzero reading)
      sample.certificate.value.name :=
  ownerEquivalent seed reading readingRefines readingSmall sample.owner sample.refines
    ((seed.neighborhood count).parameter_movement pointInside)

end Bounds.PreparedSeed

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- An original centered parent's shared segment bounds and exact uniformly prepared seed.

The seed retains the same parameter, containment evidence and cached prepared owner, so changing the differential count
reuses that owner. -/
structure PreparedPatch (parent : CenteredEdge curve differential) where
  /-- The retained original prepared segment's uniform bounds. -/ bounds : Bounds parent.edge.segment
  /-- The exact uniform seed at the original parent's parameter and cached prepared owner. -/ seed : Bounds.PreparedSeed
    bounds parent.edge.left.parameter parent.edge.left.inside parent.edge.cached.preparedOwner

constructive_injectivity PreparedPatch

namespace PreparedPatch

variable {parent : CenteredEdge curve differential}

/-- Acquire the original parent's uniform seed using the supplied exact shared segment bounds. -/
@[expose] def ofBounds (parent : CenteredEdge curve differential) (bounds : Bounds parent.edge.segment) : PreparedPatch
  parent where
  bounds := bounds
  seed := Bounds.PreparedSeed.acquire bounds parent.edge.left.parameter parent.edge.left.inside
    parent.edge.cached.preparedOwner

/-- Compute the original parent's segment bounds and acquire its retained uniform patch. -/
@[expose] def acquire (parent : CenteredEdge curve differential) : PreparedPatch parent :=
  ofBounds parent (Bounds.build parent.edge.segment)

/-- Grow the retained uniform seed's exact continued neighborhood at the requested differential count. -/
@[expose] def neighborhood (patch : PreparedPatch parent) (count : Nat) : ContinuedNeighborhood curve.polynomial count
  :=
  grow (patch.seed.neighborhood count)

/-- The retained patch neighborhood is centered at the original parent's starting point. -/
theorem center_eq (patch : PreparedPatch parent) (count : Nat) :
    (patch.neighborhood count).base.site.center = parent.edge.point 0 := by
  change (grow (patch.seed.neighborhood count)).base.site.center = _
  rw [grow_base]
  exact parent.edge.point_zero.symm

/-- The original parent's starting point belongs to the retained patch neighborhood. -/
theorem start_inside (patch : PreparedPatch parent) (count : Nat) :
    (patch.neighborhood count).box.Contains (parent.edge.point 0) :=
  patch.center_eq count ▸ (patch.neighborhood count).center_inside

/-- The retained original segment radius is a lower bound for the grown neighborhood radius. -/
theorem radius_lower (patch : PreparedPatch parent) (count : Nat) :
    patch.bounds.radius ≤ (patch.neighborhood count).radius :=
  (patch.seed.radius_lower count).trans (grow_radius_ge _)

/-- Original uniform-mesh membership places the parent finish point in the retained neighborhood. -/
theorem finish_inside_of_mesh (patch : PreparedPatch parent) (count : Nat)
    (mesh : Mesh patch.bounds) (member : parent.parameterEdge ∈ mesh.edges) :
    (patch.neighborhood count).box.Contains (parent.edge.point 1) := by
  rw [parent.edge.point_one]
  exact (grow_box_refines _).contains
    (mesh.point_inside member patch.seed count ⟨parent.edge.ordered, le_rfl⟩)

/-- Identify a contained patch sample with the original prepared edge's exact query-root name.

The original parameter equation, reserved transport and retained common seed bridge preserve the actual query owner
while comparing its name with the sample certificate. -/
@[expose] def queryEquivalent (patch : PreparedPatch parent) (count : Nat)
    (fraction : Fraction.Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) {point : Basic.Canonical}
    (pointEq : point = parent.edge.segment.pointAt
      (PreparedSheetContinuation.parameterAt parent.edge.left parent.edge.request fraction))
    (pointInside : (patch.neighborhood count).box.Contains point)
    (sample : ContinuedNeighborhood.Point (patch.neighborhood count) point) :
    NamedEquivalent (parent.edge.rootName fraction inside) sample.certificate.value.name := by
  subst point
  let nonzero := parent.edge.segment.pointAt_eval_ne_zero
    (PreparedSheetContinuation.parameterAt parent.edge.left parent.edge.request fraction)
    (PreparedSheetContinuation.parameterAt_inside parent.edge.left parent.edge.request parent.edge.ordered fraction
      inside)
  have small : normSq (curve.polynomial.eval (parent.edge.segment.pointAt parent.edge.left.parameter) -
      curve.polynomial.eval (parent.edge.segment.pointAt
        (PreparedSheetContinuation.parameterAt parent.edge.left parent.edge.request fraction))) <
          parent.edge.cached.preparedOwner.track.initial.clearance.bound := by
    rw [parent.edge.cached.preparedOwner_eq]
    simpa only [Norm.Basic.normSq_eq_canonical] using PreparedSheetContinuation.pointNormSmall parent.edge.segment
      parent.edge.within parent.edge.left
      parent.edge.owner parent.edge.request parent.edge.ordered parent.edge.small fraction inside
  have refines : (parent.edge.directQueryOwner fraction inside).track.initial.box.Refines
      parent.edge.cached.preparedOwner.track.initial.box :=
    ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines parent.edge.cached.preparedOwner nonzero (by
      simpa only [Norm.Basic.normSq_eq_canonical] using small)
      (PreparedSheetContinuation.transportReserve parent.edge.segment parent.edge.left parent.edge.request)
  rw [parent.edge.rootName_eq_directQueryOwnerRootName fraction inside]
  have sampleRefines := sample.refines
  change sample.owner.track.initial.box.Refines
    (grow (patch.seed.neighborhood count)).base.seed.owner.track.initial.box at sampleRefines
  rw [grow_base] at sampleRefines
  have movement := (patch.neighborhood count).parameter_movement pointInside
  change normSq (curve.polynomial.eval (grow (patch.seed.neighborhood count)).base.site.center - _) <
    (grow (patch.seed.neighborhood count)).base.seed.owner.track.initial.clearance.bound at movement
  rw [grow_base] at movement
  exact Bounds.PreparedSeed.ownerEquivalent patch.seed (parent.edge.directQueryOwner fraction inside) refines small
    sample.owner sampleRefines movement

/-- Identify the retained patch sample with the original parent's root name at the given equal point. -/
@[expose] def point_equivalent_at (patch : PreparedPatch parent) (count : Nat)
    (fraction : Fraction.Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) {point : Basic.Canonical}
    (pointEq : parent.edge.point fraction = point)
    (pointInside : (patch.neighborhood count).box.Contains point)
    (sample : ContinuedNeighborhood.Point (patch.neighborhood count) point) :
    NamedEquivalent (parent.edge.rootName fraction inside) sample.certificate.value.name :=
  queryEquivalent patch count fraction inside
    (pointEq.symm.trans (PreparedSheetContinuation.pointAt_parameterAt parent.edge.segment parent.edge.within
      parent.edge.left parent.edge.request fraction).symm) pointInside sample

/-- Identify a patch sample at the original parent's query point with its exact root name. -/
@[expose] def point_equivalent (patch : PreparedPatch parent) (count : Nat)
    (fraction : Fraction.Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (pointInside : (patch.neighborhood count).box.Contains (parent.edge.point fraction))
    (sample : ContinuedNeighborhood.Point (patch.neighborhood count) (parent.edge.point fraction)) :
    NamedEquivalent (parent.edge.rootName fraction inside) sample.certificate.value.name :=
  patch.point_equivalent_at count fraction inside rfl pointInside sample

end PreparedPatch

end Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility

end
