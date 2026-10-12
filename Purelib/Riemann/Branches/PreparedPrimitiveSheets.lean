module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Track.Basic

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
public import Purelib.Riemann.Normalization.ContinuedInverseRoot
public import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent

@[expose] public section

/-!
# Primitive patches in an existing prepared sheet occurrence

Non-strict containment of two winding-one owners suffices to identify their
operational roots: one explicit inner refinement is strictly inside both.
At a queried point, the transported parent box is a common outer owner for
the primitive patch and the parent's actual reserve-aware query.  Thus sheet
compatibility does not require recentered child boxes to fit a fixed seed box.
-/

namespace Purelib.Riemann.Branches.PreparedPrimitiveSheets

open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier of retained primitive sheets. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier of original point and root readings. -/
abbrev Gaussian := Basic.Canonical
/-- The original rational Gaussian box carrier with retained coordinate bounds. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original winding-one quadratic root owner indexed by its exact parameter. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- The original operational equivalence certificate between two retained Gaussian names. -/
abbrev NamedEquivalent := Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent

open Purelib.Approximation.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation in
/-- Construct root-name equivalence from refinement between the original quadratic tracks' initial boxes.

A positive-index refinement of the inner track provides a common strict interior witness. The two original names are
compared through that retained tail without replacing their owners. -/
def rootEquivalent_of_initial_refines {parameter : Gaussian} (nonzero : parameter ≠ 0)
    {outerAmbient innerAmbient : Box}
    (outer : Track.Basic.WindingOneTrack (SquareRootReconditioning.rootPolynomial parameter) outerAmbient)
    (inner : Track.Basic.WindingOneTrack (SquareRootReconditioning.rootPolynomial parameter) innerAmbient)
    (refines : inner.initial.box.Refines outer.initial.box) :
    NamedEquivalent (CertifiedSquareRoot.root nonzero outer).name (CertifiedSquareRoot.root nonzero inner).name := by
  let owner : Owner parameter := ⟨nonzero, innerAmbient, inner⟩
  let tail := owner.refineAt 1
  have strict : tail.track.initial.box.StrictInterior inner.initial.box :=
    SquareRootTrackEquivalence.state_strict_initial_of_pos inner (by decide)
  have outerToTail := SquareRootTrackEquivalence.rootEquivalent_of_initial_strict nonzero outer tail.track
    (Geometry.Rational.Box.Refinement.StrictInterior.Boxes.trans_refines strict refines)
  have innerToTail := SquareRootTrackEquivalence.rootEquivalent_of_initial_strict nonzero inner tail.track strict
  exact Equivalence.NamedEquivalent.trans outerToTail innerToTail.symm

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- Compare two original root owners refining the same transported source box at the exact target parameter.

The source-to-target movement is strictly below the original contour clearance; both owner names are related through the
retained transported outer track. -/
public def ownersEquivalent_in_transportedBox {source target : Gaussian}
    (sourceOwner : Owner source) (nonzero : target ≠ 0)
    (small : normSq (source - target) < sourceOwner.track.initial.clearance.bound)
    (first second : Owner target)
    (firstRefines : first.track.initial.box.Refines sourceOwner.track.initial.box)
    (secondRefines : second.track.initial.box.Refines sourceOwner.track.initial.box) :
    NamedEquivalent (SquareRootTrackEquivalence.ownerRootName nonzero first)
      (SquareRootTrackEquivalence.ownerRootName nonzero second) := by
  let outer := SquareRootTrackEquivalence.transportedTrack nonzero sourceOwner.track (by
      simpa only [Norm.Basic.normSq_eq_canonical]
        using small)
  have firstEquivalent := rootEquivalent_of_initial_refines nonzero outer first.track firstRefines
  have secondEquivalent := rootEquivalent_of_initial_refines nonzero outer second.track secondRefines
  exact Equivalence.NamedEquivalent.trans firstEquivalent.symm secondEquivalent

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- An original continued primitive neighborhood aligned with a retained prepared edge's start and root owner.

Its center equals the original edge start, and its seed-owner box refines the exact cached prepared-owner box, retaining
the sheet correspondence. -/
structure CompatiblePatch (parent : CenteredEdge curve differential) (count : Nat) where
  /-- The retained continued inverse-root neighborhood for this original curve polynomial. -/ neighborhood :
    ContinuedNeighborhood curve.polynomial count
  /-- Its original observation center equals the exact prepared edge start. -/ center_eq : neighborhood.base.site.center
    = parent.edge.point 0
  /-- Its original seed-owner box refines the exact cached prepared-owner box of the parent edge. -/ root_refines :
    neighborhood.base.seed.owner.track.initial.box.Refines parent.edge.cached.preparedOwner.track.initial.box

constructive_injectivity CompatiblePatch

namespace CompatiblePatch

section
open Purelib.Riemann.Readings
/-- The continued neighborhood built from an original observation owner keeps the exact site center. -/
public theorem ofOwner_center (site : PreparedObservationNeighborhoods.ObservationNeighborhood curve.polynomial count)
    (owner : Owner (curve.polynomial.eval site.center)) :
    (ContinuedNeighborhood.ofOwner site owner).base.site.center = site.center := rfl

/-- The continued neighborhood built from an original owner keeps its seed box refining that owner's initial box. -/
public theorem ofOwner_refines (site : PreparedObservationNeighborhoods.ObservationNeighborhood curve.polynomial count)
    (owner : Owner (curve.polynomial.eval site.center)) :
    (ContinuedNeighborhood.ofOwner site owner).base.seed.owner.track.initial.box.Refines owner.track.initial.box :=
  (ContinuedNeighborhood.ofOwner site owner).owner_refines

/-- Construct a compatible patch from an original observation site, start equality and refining root owner.

The continued neighborhood is built from that same owner; its center and root-box refinement compose with the supplied
original parent evidence. -/
public def fromOwner (parent : CenteredEdge curve differential)
    (site : PreparedObservationNeighborhoods.ObservationNeighborhood curve.polynomial count)
    (center : site.center = parent.edge.point 0)
    (owner : Owner (curve.polynomial.eval site.center))
    (refines : owner.track.initial.box.Refines parent.edge.cached.preparedOwner.track.initial.box) :
    CompatiblePatch parent count where
  neighborhood := ContinuedNeighborhood.ofOwner site owner
  center_eq := (ofOwner_center (curve := curve) site owner).trans center
  root_refines := (ofOwner_refines (curve := curve) site owner).trans refines

end

open Purelib.Geometry.Rational in
open Purelib.Riemann.Readings in
/-- Acquire a compatible continued neighborhood at the original prepared edge start using its exact cached prepared root
owner. -/
def acquire (parent : CenteredEdge curve differential) (count : Nat) : CompatiblePatch parent count := by
  let site := PreparedObservationNeighborhoods.ObservationNeighborhood.ofPoint curve.polynomial count
    (parent.edge.segment.pointAt parent.edge.left.parameter)
    (parent.edge.segment.pointAt_eval_ne_zero parent.edge.left.parameter parent.edge.left.inside)
  exact fromOwner parent site parent.edge.point_zero.symm parent.edge.cached.preparedOwner
    (Box.refines_refl _)

/-- The original prepared edge start belongs to the retained compatible neighborhood box. -/
theorem start_inside {parent : CenteredEdge curve differential} (patch : CompatiblePatch parent count) :
    patch.neighborhood.box.Contains (parent.edge.point 0) :=
  patch.center_eq ▸ patch.neighborhood.center_inside

open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Compare the original prepared edge root query with a supplied root owner at the same exact parameter point.

The supplied box refines the cached prepared-owner box. The original reserved transport request and its retained
movement certificate compare both names through that common outer box. -/
public def queryOwnerEquivalent (parent : CenteredEdge curve differential)
    (fraction : Coordinate) (inside : 0 ≤ fraction ∧ fraction ≤ 1) {point : Gaussian}
    (pointEq : point = parent.edge.segment.pointAt
      (PreparedSheetContinuation.parameterAt parent.edge.left parent.edge.request fraction))
    (owner : Owner (curve.polynomial.eval point))
    (refines : owner.track.initial.box.Refines parent.edge.cached.preparedOwner.track.initial.box) :
    NamedEquivalent (parent.edge.rootName fraction inside)
      (SquareRootTrackEquivalence.ownerRootName owner.parameterNonzero owner) := by
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
  have actualRefines : (parent.edge.directQueryOwner fraction inside).track.initial.box.Refines
    parent.edge.cached.preparedOwner.track.initial.box :=
    ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines parent.edge.cached.preparedOwner nonzero (by
      simpa only [Norm.Basic.normSq_eq_canonical] using small)
      (PreparedSheetContinuation.transportReserve parent.edge.segment parent.edge.left parent.edge.request)
  rw [parent.edge.rootName_eq_directQueryOwnerRootName fraction inside]
  exact ownersEquivalent_in_transportedBox parent.edge.cached.preparedOwner nonzero small
    (parent.edge.directQueryOwner fraction inside) owner actualRefines refines

/-- Compare the original edge root name with a retained continued-neighborhood point certificate at an explicitly equal
edge point.

The exact point equality and both original root-box refinements preserve the prepared edge's sheet assignment and the
point owner's identity. -/
def point_equivalent_at {parent : CenteredEdge curve differential} (patch : CompatiblePatch parent count)
    (fraction : Coordinate) (inside : 0 ≤ fraction ∧ fraction ≤ 1) {point : Gaussian}
    (pointEq : parent.edge.point fraction = point)
    (sample : ContinuedNeighborhood.Point patch.neighborhood point) :
    NamedEquivalent (parent.edge.rootName fraction inside) sample.certificate.value.name :=
  queryOwnerEquivalent parent fraction inside
    (pointEq.symm.trans (PreparedSheetContinuation.pointAt_parameterAt parent.edge.segment parent.edge.within
      parent.edge.left
      parent.edge.request fraction).symm) sample.owner (sample.refines.trans patch.root_refines)

/-- Compare the original edge root query with the retained continued-neighborhood point certificate at that same edge
point. -/
def point_equivalent {parent : CenteredEdge curve differential} (patch : CompatiblePatch parent count)
    (fraction : Coordinate) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (sample : ContinuedNeighborhood.Point patch.neighborhood (parent.edge.point fraction)) :
    NamedEquivalent (parent.edge.rootName fraction inside) sample.certificate.value.name :=
  patch.point_equivalent_at fraction inside rfl sample

end CompatiblePatch

end Purelib.Riemann.Branches.PreparedPrimitiveSheets
