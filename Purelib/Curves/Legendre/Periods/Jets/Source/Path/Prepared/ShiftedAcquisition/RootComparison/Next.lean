module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.RootComparison
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Comparison
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Data.Gaussian.Norm.Basic

/-! # Actual retained shifted-parent finish-to-next-start handoff

The same original source preparation pair and root/geometric chain derive
agreement of two independently retained parameter Steps. The actual first
shifted acquisition's cached local fold supplies its finishing comparison;
the existing next acquisition supplies its exact initial Owner readback.
Their composition preserves both real acquisitions and all endpoint caches.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition.RootComparison

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedClearPathModels (ownerAtStart)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent next : CenteredEdge (Fibre.frameCurve frame) basis}
    {firstPatch : PreparedPatch parent} {nextPatch : PreparedPatch next} {count floor : Nat}
    {firstCovered : (firstPatch.neighborhood count).box.Contains (parent.edge.point 1)}
    {nextCovered : (nextPatch.neighborhood count).box.Contains (next.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {firstPrepared : PreparedParent firstPatch count floor firstCovered targets}
    {nextPrepared : PreparedParent nextPatch count floor nextCovered targets}
    {firstRange : Variation.Point.Range (firstPatch.neighborhood count)}
    {nextRange : Variation.Point.Range (nextPatch.neighborhood count)}
    {target : Paths.Frame (parameter + increment)}
    {firstAdmitted : Norm.Basic.normSq increment ≤ firstRange.shiftedBound}
    {nextAdmitted : Norm.Basic.normSq increment ≤ nextRange.shiftedBound}
    {firstStep : Variation.Point.Step firstPrepared.firstSample increment} {firstWidth nextWidth : AccuracyRequest}
    {firstRetained : ShiftedAcquisition (covered := firstCovered) firstRange target firstAdmitted firstStep firstWidth}
    {strip : Norm.Basic.normSq increment ≤ firstRange.stripBound}
    {actual : OwnerPath (Fibre.frameCurve target).polynomial (startPoint parent).coordinate firstStep.owner
      (finishPoint parent).coordinate firstRetained.acquired.traced.finishOwner}
    {actual_eq : actual = firstRetained.acquired.traced.trace.get}
    (comparison : RootComparison firstRetained strip actual actual_eq)
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {start finish : LiftedPoint 2}
    (geometry : CenteredPathChain (parent :: next :: remaining) (start := start) (finish := finish))
    {incoming returning : Named} (roots : RootChain (parent :: next :: remaining) incoming returning)
    (lastStep : Variation.Point.Step firstPrepared.lastSample increment)
    (nextStep : Variation.Point.Step nextPrepared.firstSample increment)
    (nextRetained : ShiftedAcquisition (covered := nextCovered) nextRange target nextAdmitted nextStep nextWidth)

/-- Derive the actual covered shifted finish-to-next-internal-source comparison from the original signed spine.

The first local acquisition's real terminal Owner compares with lastStep.
The original same-parameter RootChain derives lastStep-to-nextStep
agreement after both retained contour payments. The next acquisition's
exact source readback identifies its literal internal source Owner with
nextStep's cached certificate. No next-parent or returning-sheet
comparison is assumed, and neither acquisition nor Step is run again.
-/
def nextStartEquivalent : NamedEquivalent
    (ownerRootName firstRetained.parents.covered.subdivision.terminalOwner.parameterNonzero
      firstRetained.parents.covered.subdivision.terminalOwner)
    (ownerRootName (ownerAtStart nextRetained.segment nextStep.owner).parameterNonzero
      (ownerAtStart nextRetained.segment nextStep.owner)) :=
  let endpoint := firstPrepared.shiftedNextEquivalent nextPrepared geometry roots lastStep nextStep
  let finish := comparison.coveredFinishEquivalent lastStep
  NamedEquivalent.transport rfl nextRetained.initial_name_eq.symm (finish.trans endpoint)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition.RootComparison

end
