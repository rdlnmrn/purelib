module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Queries
import Purelib.Curves.Legendre.Periods.Jets.Source.Observations

/-! # Actual globally allocated shifted queries at their original block occurrences

The stored global occurrence reads the SAME global prepared source and its
original block's comparison cache. Actual old/new observation bundles and
the independently retained parameter Step stay inputs. One retained direct
edge query links the original signed RootPath to these exact query owners.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint liftedCell)
open Purelib.Riemann.Branches
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (firstParent :: remaining)}
    {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Data.Gaussian.Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {oldGeometry : CenteredPathChain (firstParent :: remaining)
      (start := startPoint firstParent) (finish := startPoint firstParent)}
    {oldRoot : Named} {oldRoots : RootChain (firstParent :: remaining) oldRoot oldRoot}
    {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
    {requestIndex globalFloor rootStage : Nat}
    {request : Request whole requestIndex globalFloor rootStage}
    {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}

variable (located : Occurrence blocks request sourceIndex)

/-- Read the original physical parent fraction at the SAME globally located accepted child request.

Only the original request endpoints and supplied local fraction are read.
The occurrence's parent equality proves this is the identical retained
local acquisition fraction; no mesh or parameterization is constructed.
-/
@[expose] def sourceInput (_located : Occurrence blocks request sourceIndex) (input : Rational) : Rational :=
  let child := (request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt
  PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input

/-- The original child request maps each admitted local input into the SAME old parent's unit interval. -/
theorem sourceInput_inside (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1) :
    0 ≤ located.sourceInput input ∧ located.sourceInput input ≤ 1 :=
  let child := (request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt
  PreparedSheetContinuation.parameterAt_inside child.edge.left child.edge.request child.edge.ordered input inside

/-- The exact original source-query answer and parameter Step at the SAME retained occurrence and mapped input.

The original prepared source, six requests, mapped physical fraction,
continued point and increment remain indices. This named result type
constructs no observation or continuation and copies none of their caches.
-/
@[expose] def SourceStep (input : Rational) :=
  (observed : CellModels.Observations frame
    (liftedCell ((firstParent :: remaining)[located.block.val]'located.block.isLt))
    (prepared.entry located.block).preparation.cell.models
    (prepared.entry located.block).preparation.query.requests (located.sourceInput input)) ×
  Variation.Point.Step observed.retained.sample increment

/-- Answer the original raw source query once and advance its SAME Point at the computed common allocation.

The stored occurrence selects the original block's prepared source and
already cached physical-patch Range. The common strip allocation pays that
Range internally. Only the exact Cell factory equality transports its
index; the original query answer and resulting Step are retained together.
-/
def sourceStep (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1) : SourceStep located input :=
  let old := prepared.entry located.block
  let localInside := located.sourceInput_inside input inside
  old.advanceQuery (ranges.entry located.block) (located.sourceInput input) localInside.1 localInside.2 increment
    (admitted.trans (allocation.bound_le_bound.trans (ranges.bound_le_entry located.block)))

/-- The actual original raw query bundle is unchanged in its occurrence-indexed parameter continuation cache. -/
theorem sourceStep_observation (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1) :
    (located.sourceStep (admitted := admitted) input inside).1 =
      (prepared.entry located.block).preparation.query.observe frame (located.sourceInput input)
        (located.sourceInput_inside input inside).1 (located.sourceInput_inside input inside).2 := by
  unfold sourceStep
  exact (prepared.entry located.block).advanceQuery_observation (ranges.entry located.block)
    (located.sourceInput input) _ _ increment _

/-- Derive signed agreement on the actual global source Query's already retained observation bundle.

The supplied Alignment is the finite derived cache for the SAME original
block comparison. Both actual observation bundles remain untouched, and the
Step advances precisely the old bundle's original selected Point. The exact
occurrence equality and original global preparation determine the target
query owner; no desired signed comparison is supplied.
-/
def queryEquivalent
    (aligned : Acquisition.Segment.RootComparisons.Alignment
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (oldObserved : CellModels.Observations frame
      (liftedCell ((firstParent :: remaining)[located.block.val]'located.block.isLt))
      (prepared.entry located.block).preparation.cell.models
      (prepared.entry located.block).preparation.query.requests (located.sourceInput input))
    (step : Variation.Point.Step oldObserved.retained.sample increment)
    (newObserved : request.Observation sourceIndex input)
    (direct : PreparedEdge.Query
      ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge input inside) :
    NamedEquivalent newObserved.retained.sample.certificate.value.name step.root.value.name :=
  (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.queryEquivalent
    aligned (prepared.entry located.block) (request.attempt.2.1.entry sourceIndex)
    input inside step newObserved.retained.sample located.child located.parent_eq direct

/-- Cache one genuine direct-edge query and derive the actual global observation-to-Step relation at this occurrence.

Both original observation bundles and the old parameter Step are consumed
unchanged. The original edge Query factory executes once and retains its
whole Owner equality. There is no source, advance, acquisition, allocation,
Alignment or independent observation callback execution in this operation.
-/
def compareQuery
    (aligned : Acquisition.Segment.RootComparisons.Alignment
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (oldObserved : CellModels.Observations frame
      (liftedCell ((firstParent :: remaining)[located.block.val]'located.block.isLt))
      (prepared.entry located.block).preparation.cell.models
      (prepared.entry located.block).preparation.query.requests (located.sourceInput input))
    (step : Variation.Point.Step oldObserved.retained.sample increment)
    (newObserved : request.Observation sourceIndex input) :
    PreparedEdge.Query
      ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge input inside ×
      NamedEquivalent newObserved.retained.sample.certificate.value.name step.root.value.name :=
  let direct := PreparedEdge.Query.build
    ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge input inside
  let compared := located.queryEquivalent aligned input inside oldObserved step newObserved direct
  ⟨direct, compared⟩

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

end
