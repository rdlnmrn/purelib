module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Chain
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Shifted
public import Purelib.Polynomial.Geometry.ClearPath.Region
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents
import Purelib.Approximation.AccuracyRequest
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Data.Gaussian.Norm.Basic

/-! # Whole shifted physical parents from the original total acquisition chain

The same original affine parent is re-cleared under the changed polynomial
on its identical physical box. The original total width-paid acquisition
constructs its whole continued subdivision and finish owner. Canonical
centers and complete coverage consume that exact paid result once. The
count allocations and six-channel sources consume that actual connected path.
No second mesh walker, independent shifted sheet or returning owner is
introduced, and parameter derivative/integral comparisons remain separate.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Paths.PreparedClearPathModels (ownerAtStart)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    (range : Variation.Point.Range (patch.neighborhood count)) (target : Paths.Frame (parameter + increment))
    (admitted : Norm.Basic.normSq increment ≤ range.shiftedBound)
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    (firstStep : Variation.Point.Step firstSample increment) (width : AccuracyRequest)

/-- Stored actual shifted clearance, same physical segment, total acquisition and its complete covered parents.

Each original factory executes once. Its whole defining equation remains
attached to the resulting cache, including the real paid subdivision,
terminal owner, width requests, chosen mesh and canonical centers.
-/
@[expose] def ShiftedAcquisition :=
  (clearance : { value : RegionClearance (Fibre.frameCurve target).polynomial (patch.neighborhood count).box //
    value = range.shiftedClearance increment admitted }) ×
  (segment : { value : ClearSegment (Fibre.frameCurve target).polynomial (patch.neighborhood count).box
      (startPoint parent).coordinate (finishPoint parent).coordinate //
    value = parent.edge.localSegment.reclear clearance.val
      (start_inside patch count) (finish_inside patch count covered) ∧ value.WithinAmbient }) ×
  (acquired : { value : Acquisition.Segment (segment := segment.val) (within := segment.property.2)
      (owner := firstStep.owner) width // value = Acquisition.Segment.build width }) ×
  { parents : Acquisition.Segment.Parents (curve := Fibre.frameCurve target)
      basis parent.edge.sheet count acquired.val //
    parents = Acquisition.Segment.Parents.build basis parent.edge.sheet count acquired.val }

namespace ShiftedAcquisition

variable {range target admitted firstStep width}

/-- Acquire and cover the entire identical physical parent using the original total width-paid procedure.

The retained target Step owner is the acquisition's literal source owner.
The original procedure supplies its internal endpoint-index transport,
actual sufficient depth and all continued finish-owner handoffs. Coverage
consumes the same result, without a second acquisition or mesh search.
-/
def build (range : Variation.Point.Range (patch.neighborhood count)) (target : Paths.Frame (parameter + increment))
    (admitted : Norm.Basic.normSq increment ≤ range.shiftedBound)
    (firstStep : Variation.Point.Step firstSample increment) (width : AccuracyRequest) :
    ShiftedAcquisition (covered := covered) range target admitted firstStep width := by
  let clearance : RegionClearance (Fibre.frameCurve target).polynomial (patch.neighborhood count).box :=
    range.shiftedClearance increment admitted
  let segment := parent.edge.localSegment.reclear clearance
    (start_inside patch count) (finish_inside patch count covered)
  have within := parent.edge.localSegment.reclear_withinAmbient clearance
    (start_inside patch count) (finish_inside patch count covered)
  let acquired := Acquisition.Segment.build (segment := segment) (within := within) (owner := firstStep.owner) width
  let parents := Acquisition.Segment.Parents.build (curve := Fibre.frameCurve target)
    basis parent.edge.sheet count acquired
  exact ⟨⟨clearance, rfl⟩, ⟨segment, rfl, within⟩, ⟨acquired, rfl⟩, ⟨parents, rfl⟩⟩

variable (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)

/-- Read the same shifted-polynomial region certificate on the original physical box. -/
@[expose] def clearance : RegionClearance (Fibre.frameCurve target).polynomial (patch.neighborhood count).box :=
  retained.1.val

/-- The complete stored clearance is the retained Range's exact changed-parameter factory result. -/
theorem clearance_eq : retained.clearance = range.shiftedClearance increment admitted := retained.1.property

/-- Read the literal original affine parent endpoints and orientation under the actual shifted polynomial. -/
@[expose] def segment : ClearSegment (Fibre.frameCurve target).polynomial (patch.neighborhood count).box
    (startPoint parent).coordinate (finishPoint parent).coordinate := retained.2.1.val

/-- The whole stored shifted segment is the region-backed reclearance of the exact old local segment. -/
theorem segment_eq : retained.segment = parent.edge.localSegment.reclear retained.clearance
    (start_inside patch count) (finish_inside patch count covered) := retained.2.1.property.1

/-- Read the retained all-point ambient containment of that same shifted segment. -/
theorem within : retained.segment.WithinAmbient := retained.2.1.property.2

/-- Every original affine parent point remains the identical physical point after the parameter changes. -/
theorem point_eq (fraction : Paths.Coordinate) : retained.segment.pointAt fraction = parent.edge.point fraction := by
  rewrite [retained.segment_eq]
  exact parent.edge.localSegment.reclear_pointAt retained.clearance
    (start_inside patch count) (finish_inside patch count covered) fraction

/-- Read the complete original total acquisition, including its exact continued source/finish owners and paid mesh. -/
@[expose] def acquired : Acquisition.Segment (segment := retained.segment) (within := retained.within)
    (owner := firstStep.owner) width := retained.2.2.1.val

/-- The entire acquisition is the original total factory on this exact segment, owner and actual width request. -/
theorem acquired_eq : retained.acquired = Acquisition.Segment.build
    (segment := retained.segment) (within := retained.within) (owner := firstStep.owner) width :=
  retained.2.2.1.property

/-- Read the canonical centers and complete covered-parent family built on that same actual acquisition. -/
@[expose] def parents : Acquisition.Segment.Parents (curve := Fibre.frameCurve target)
    basis parent.edge.sheet count retained.acquired := retained.2.2.2.val

/-- The whole parent cover is the original factory on the same stored paid subdivision and terminal cache. -/
theorem parents_eq : retained.parents = Acquisition.Segment.Parents.build (curve := Fibre.frameCurve target)
    basis parent.edge.sheet count retained.acquired := retained.2.2.2.property

/-- The original internal pointAt-zero owner transport preserves the exact retained target Step's initial root name. -/
theorem initial_name_eq : ownerRootName (ownerAtStart retained.segment firstStep.owner).parameterNonzero
    (ownerAtStart retained.segment firstStep.owner) = firstStep.root.value.name := by
  have original := Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName_castOwnerParameter
    (congrArg (Fibre.frameCurve target).polynomial.eval retained.segment.pointAt_zero.symm) firstStep.owner
  change ownerRootName (ownerAtStart retained.segment firstStep.owner).parameterNonzero
    (ownerAtStart retained.segment firstStep.owner) = ownerRootName firstStep.owner.parameterNonzero firstStep.owner
    at original
  exact original.trans (congrArg (fun certificate => certificate.value.name) firstStep.root_eq.symm)

/-- The actual acquisition trace finish agrees with the SAME retained covered subdivision's terminal root name. -/
theorem finish_name_eq : ownerRootName retained.acquired.traced.finishOwner.parameterNonzero
    retained.acquired.traced.finishOwner =
      ownerRootName retained.parents.covered.subdivision.terminalOwner.parameterNonzero
        retained.parents.covered.subdivision.terminalOwner :=
  retained.parents.finishName_eq

/-- Actual connected-chain, count allocations and six-channel source caches on the complete shifted parent cover.

All allocations use this NEW actual covered chain's own finite cell count.
The original prepared source product is materialized once, then its literal
cells are joined along the same stored chain. No root/bank admission or
independent same-point agreement is assumed by this local source producer.
-/
@[expose] def Prepared (floor stage : Nat) :=
  (chain : { value : CenteredPathChain retained.parents.covered.parents
      (start := startPoint parent) (finish := finishPoint parent) //
    value = retained.parents.covered.chain }) ×
  (targets : { value : CellEndpoints.Targets chain.val.path stage //
    value = CellEndpoints.Targets.build chain.val.path stage }) ×
  (prepared : { value : PreparedParents retained.parents.coveredParents floor targets.val //
    value = prepareCovered retained.parents.coveredParents floor targets.val }) ×
  { path : Path (parameter + increment) chain.val.path //
    path = PreparedParents.sources retained.parents.coveredParents prepared.val chain.val }

namespace Prepared

variable {retained} {floor stage : Nat}

/-- Materialize all genuine count-paid shifted source cells on the identical actual covered subdivision once. -/
def build (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)
    (floor stage : Nat) : Prepared retained floor stage := by
  let chain := retained.parents.covered.chain
  let targets := CellEndpoints.Targets.build chain.path stage
  let prepared := prepareCovered (frame := target) retained.parents.coveredParents floor targets
  let path := PreparedParents.sources retained.parents.coveredParents prepared chain
  exact ⟨⟨chain, rfl⟩, ⟨targets, rfl⟩, ⟨prepared, rfl⟩, ⟨path, rfl⟩⟩

variable (prepared : Prepared retained floor stage)

/-- Read the same connected shifted parent spine with its exact original lifted endpoints and sheet. -/
@[expose] def chain : CenteredPathChain retained.parents.covered.parents
    (start := startPoint parent) (finish := finishPoint parent) := prepared.1.val

/-- The whole retained chain is the existing original connected-cover construction on the same stored parents. -/
theorem chain_eq : prepared.chain = retained.parents.covered.chain := prepared.1.property

/-- Read the retained count allocations computed from this exact actual shifted lifted chain. -/
@[expose] def targets : CellEndpoints.Targets prepared.chain.path stage := prepared.2.1.val

/-- The complete target cache is the original finite-count allocation factory on the identical new chain. -/
theorem targets_eq : prepared.targets = CellEndpoints.Targets.build prepared.chain.path stage := prepared.2.1.property

/-- Read every retained original endpoint/query/model source cache at its actual new parent occurrence. -/
@[expose] def sources : PreparedParents retained.parents.coveredParents floor prepared.targets := prepared.2.2.1.val

/-- The whole stored source product is the existing once-materialized cover factory on the same target cache. -/
theorem sources_eq : prepared.sources = prepareCovered retained.parents.coveredParents floor prepared.targets :=
  prepared.2.2.1.property

/-- Read the literal ordered six-channel spatial source path without rejoining or resampling its entries. -/
@[expose] def path : Path (parameter + increment) prepared.chain.path := prepared.2.2.2.val

/-- The stored ordered source path joins the SAME actual parent preparations and retained tail caches. -/
theorem path_eq : prepared.path = PreparedParents.sources retained.parents.coveredParents
    prepared.sources prepared.chain := prepared.2.2.2.property

end Prepared

end ShiftedAcquisition

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
