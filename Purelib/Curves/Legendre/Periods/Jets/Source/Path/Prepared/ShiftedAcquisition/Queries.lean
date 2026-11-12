module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Alignment
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Alignment.Queries
public import Purelib.Riemann.Paths.PreparedSegmentSources
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.List.Membership

/-! # Actual shifted child queries attached to original fixed-point parameter Steps

The original local acquisition and materialized alignment remain retained.
An exact original-child occurrence identifies the global prepared source's
edge. Its actual query sample is compared to that same edge root; the local
RootPath then compares to the independently retained original Point.Step.
All source/target allocations, owners and old readings remain distinct.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge centeredEdges)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedClearPathModels (ownerAtStart)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_initial_box)

attribute [local irreducible] CertifiedSquareRoot.rawRoot

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + increment)}
    {admitted : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample increment} {width : AccuracyRequest}
    (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)
    {child : CenteredEdge (Fibre.frameCurve target) basis}
    (index : Fin retained.parents.covered.parents.length)
    (child_eq : child = retained.parents.covered.parents[index.val]'index.isLt)

include retained index child_eq in
/-- Every actual located child fraction is the SAME old physical parent fraction of the original affine segment.

The original Parents.parents_eq and actual centered-edge point law identify
its retained request fraction. ShiftedAcquisition.point_eq then reads the
old parent at that identical fraction; no new parameterization is selected.
-/
theorem originalPoint_eq (input : Rational) :
    child.edge.point input = parent.edge.point
      (PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input) := by
  have bound : index.val <
      (centeredEdges (Fibre.frameCurve target) basis parent.edge.sheet
        retained.acquired.traced.prepared.subdivision retained.parents.centers).length :=
    Eq.mp (congrArg (fun length => index.val < length) (congrArg List.length retained.parents.parents_eq)) index.isLt
  have selected : child =
      (centeredEdges (Fibre.frameCurve target) basis parent.edge.sheet
        retained.acquired.traced.prepared.subdivision retained.parents.centers)[index.val]'bound :=
    child_eq.trans (getElem_congr retained.parents.parents_eq rfl index.isLt)
  have member : child ∈ centeredEdges (Fibre.frameCurve target) basis parent.edge.sheet
      retained.acquired.traced.prepared.subdivision retained.parents.centers :=
    selected.symm ▸ List.getElem_mem bound
  exact (Riemann.Integration.PreparedSubdivisionModelCore.centeredEdges_point
    (Fibre.frameCurve target) basis parent.edge.sheet retained.acquired.traced.prepared.subdivision
    retained.parents.centers child member input).trans (retained.point_eq _)

include retained index child_eq in
/-- The actual child has its original ordered endpoint fractions on the SAME shifted physical segment.

The retained child left/request endpoints give the two unit-interval
fractions. The original all-query point law and exact reclearance point
law retain this segment's own ambient, including stationary intervals.
-/
theorem segmentSource : Riemann.Paths.PreparedSegmentSources.SegmentSource retained.segment child := by
  refine ⟨child.edge.left.parameter, child.edge.request.endpoint.parameter,
    child.edge.left.inside.1, child.edge.ordered, child.edge.request.endpoint.inside.2, ?_, ?_⟩
  · exact ((retained.originalPoint_eq index child_eq 0).trans
      (congrArg parent.edge.point
        (PreparedSheetContinuation.parameterAt_zero child.edge.left child.edge.request))).trans
      (retained.point_eq child.edge.left.parameter).symm
  · exact ((retained.originalPoint_eq index child_eq 1).trans
      (congrArg parent.edge.point
        (PreparedSheetContinuation.parameterAt_one child.edge.left child.edge.request))).trans
      (retained.point_eq child.edge.request.endpoint.parameter).symm

namespace RootComparison

variable {retained index child_eq}
    {strip : Norm.Basic.normSq increment ≤ range.stripBound}
    {actual : OwnerPath (Fibre.frameCurve target).polynomial (startPoint parent).coordinate firstStep.owner
      (finishPoint parent).coordinate retained.acquired.traced.finishOwner}
    {actual_eq : actual = retained.acquired.traced.trace.get}
    (comparison : RootComparison retained strip actual actual_eq)
    (aligned : Acquisition.Segment.RootComparisons.Alignment comparison.paths comparison.firstReference)
    {oldFloor : Nat} {oldStart oldFinish : LiftedPoint 2} {oldPath : LiftedPath 2 oldStart oldFinish}
    {oldStage : Nat} {oldTargets : CellEndpoints.Targets oldPath oldStage}
    (oldPrepared : PreparedParent patch count oldFloor covered oldTargets)
    {newPatch : PreparedPatch child} {newCount newFloor : Nat}
    {newCovered : (newPatch.neighborhood newCount).box.Contains (child.edge.point 1)}
    {newStart newFinish : LiftedPoint 2} {newPath : LiftedPath 2 newStart newFinish}
    {newStage : Nat} {newTargets : CellEndpoints.Targets newPath newStage}
    (newPrepared : PreparedParent newPatch newCount newFloor newCovered newTargets)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    {sourceSample : ContinuedNeighborhood.Point oldPrepared.preparation.cell.patch
      (oldPrepared.preparation.cell.models.coordinate.point
        (PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input))}
    (step : Variation.Point.Step sourceSample increment)
    (targetSample : ContinuedNeighborhood.Point newPrepared.preparation.cell.patch
      (newPrepared.preparation.cell.models.coordinate.point input))

/-- Derive signed agreement of an actual global query sample with the independently retained original parameter Step.

The exact child occurrence is supplied by the original global occurrence
map. Both preparations keep their OWN original Targets and retained Cell
queries. Their sample owners are inputs; the original Cell factory,
physical fraction readbacks, source-box refinement and SAME aligned local
RootPath derive every signed comparison internally.
-/
def queryEquivalent
    (index : Fin retained.parents.covered.parents.length)
    (child_eq : child = retained.parents.covered.parents[index.val]'index.isLt)
    (direct : Riemann.Integration.PreparedConstantModels.PreparedEdge.Query child.edge input inside) :
    NamedEquivalent targetSample.certificate.value.name step.root.value.name := by
  let oldInput := PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input
  have point_eq : oldPrepared.preparation.cell.models.coordinate.point oldInput = child.edge.point input :=
    (oldPrepared.queryPoint_eq oldInput).trans (retained.originalPoint_eq index child_eq input).symm
  have originalRefines := step.refines.trans (oldPrepared.querySample_refines oldInput sourceSample)
  have referenceRefines : (ownerAtStart retained.segment comparison.firstReference).track.initial.box.Refines
      (patch.neighborhood count).base.seed.owner.track.initial.box := by
    unfold ownerAtStart
    rewrite [castOwnerParameter_initial_box, comparison.firstReference_box]
    exact Geometry.Rational.Box.refines_refl _
  have bound : index.val <
      (centeredEdges (Fibre.frameCurve target) basis parent.edge.sheet
        retained.acquired.traced.prepared.subdivision retained.parents.centers).length :=
    Eq.mp (congrArg (fun length => index.val < length) (congrArg List.length retained.parents.parents_eq)) index.isLt
  have selected : child =
      (centeredEdges (Fibre.frameCurve target) basis parent.edge.sheet
        retained.acquired.traced.prepared.subdivision retained.parents.centers)[index.val]'bound :=
    child_eq.trans (getElem_congr retained.parents.parents_eq rfl index.isLt)
  have compared := Comparison.Cache.Alignment.queryPointEquivalent comparison.paths
    (ownerAtStart retained.segment comparison.firstReference) aligned referenceRefines retained.parents.centers
    ⟨index.val, bound⟩ selected input inside direct point_eq step.owner originalRefines
  have originalName : ownerRootName step.owner.parameterNonzero step.owner = step.root.value.name := by
    rewrite [step.root_eq]
    rfl
  have toStep := NamedEquivalent.transport rfl originalName compared
  exact (newPrepared.querySampleEquivalent input inside targetSample direct).symm.trans toStep

/-- Retain one genuinely new direct-query cache and its derived actual global sample-to-Step comparison.

The existing Query.build executes once on the SAME located child. Its
whole Owner/factory equation stays in that original Query cache. Both
already retained sample owners and the original alignment are reused;
no acquisition, advancement, source observation or Targets is recreated.
-/
def compareQuery
    (index : Fin retained.parents.covered.parents.length)
    (child_eq : child = retained.parents.covered.parents[index.val]'index.isLt) :
    Riemann.Integration.PreparedConstantModels.PreparedEdge.Query child.edge input inside ×
      NamedEquivalent targetSample.certificate.value.name step.root.value.name :=
  let direct := Riemann.Integration.PreparedConstantModels.PreparedEdge.Query.build child.edge input inside
  let compared := comparison.queryEquivalent aligned oldPrepared newPrepared input inside step targetSample
    index child_eq direct
  ⟨direct, compared⟩

end RootComparison

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
