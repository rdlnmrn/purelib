module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.RootComparison
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Closing
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Data.Gaussian.Norm.Basic

/-! # Actual shifted acquisition return from the original closed root chain

The retained last acquisition supplies its actual covered terminal Owner.
The original closed root/geometric spines derive agreement of the original
last and first retained parameter Steps. The SAME original first shifted
acquisition identifies its actual internal source. Composition derives a
signed return, without a desired changed-parameter closing field or a new
continuation execution. Global source-stage assembly remains separate.
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
    {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
    {firstPatch : PreparedPatch firstParent} {count floor : Nat}
    {firstCovered : (firstPatch.neighborhood count).box.Contains (firstParent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {firstPrepared : PreparedParent firstPatch count floor firstCovered targets}
    {firstRange : Variation.Point.Range (firstPatch.neighborhood count)}
    {target : Paths.Frame (parameter + increment)}
    {firstAdmitted : Norm.Basic.normSq increment ≤ firstRange.shiftedBound}
    {firstStep : Variation.Point.Step firstPrepared.firstSample increment} {firstWidth : AccuracyRequest}
    (firstRetained : ShiftedAcquisition (covered := firstCovered) firstRange target firstAdmitted firstStep firstWidth)

section Multiple

variable {lastParent : CenteredEdge (Fibre.frameCurve frame) basis}
    {lastPatch : PreparedPatch lastParent}
    {lastCovered : (lastPatch.neighborhood count).box.Contains (lastParent.edge.point 1)}
    {lastPrepared : PreparedParent lastPatch count floor lastCovered targets}
    {lastRange : Variation.Point.Range (lastPatch.neighborhood count)}
    {lastAdmitted : Norm.Basic.normSq increment ≤ lastRange.shiftedBound}
    {lastFirstStep : Variation.Point.Step lastPrepared.firstSample increment} {lastWidth : AccuracyRequest}
    {lastRetained : ShiftedAcquisition (covered := lastCovered) lastRange target lastAdmitted lastFirstStep lastWidth}
    {lastStrip : Norm.Basic.normSq increment ≤ lastRange.stripBound}
    {actual : OwnerPath (Fibre.frameCurve target).polynomial (startPoint lastParent).coordinate lastFirstStep.owner
      (finishPoint lastParent).coordinate lastRetained.acquired.traced.finishOwner}
    {actual_eq : actual = lastRetained.acquired.traced.trace.get}

/-- Derive the actual last covered terminal-to-first-internal-source return from the original closed root spine.

The original geometric return and closed RootChain derive lastStep-to-firstStep
agreement with both Steps' own contour/refinement payments. The retained last
comparison cache supplies its actual terminal-to-lastStep comparison. The
SAME first acquisition supplies its exact original internal source readback.
No shifted closing comparison is assumed and neither acquisition nor Step is
executed again.
-/
def returnStartEquivalent
    (comparison : RootComparison lastRetained lastStrip actual actual_eq)
    {middle : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (geometry : CenteredPathChain (firstParent :: middle ++ [lastParent])
      (start := startPoint firstParent) (finish := startPoint firstParent))
    {root : Named} (roots : RootChain (firstParent :: middle ++ [lastParent]) root root)
    (lastStep : Variation.Point.Step lastPrepared.lastSample increment) :
    NamedEquivalent
      (ownerRootName lastRetained.parents.covered.subdivision.terminalOwner.parameterNonzero
        lastRetained.parents.covered.subdivision.terminalOwner)
      (ownerRootName (ownerAtStart firstRetained.segment firstStep.owner).parameterNonzero
        (ownerAtStart firstRetained.segment firstStep.owner)) :=
  let endpoint := firstPrepared.shiftedReturnEquivalent lastPrepared geometry roots firstStep lastStep
  let finish := comparison.coveredFinishEquivalent lastStep
  NamedEquivalent.transport rfl firstRetained.initial_name_eq.symm (finish.trans endpoint)

end Multiple

section Singleton

variable {strip : Norm.Basic.normSq increment ≤ firstRange.stripBound}
    {actual : OwnerPath (Fibre.frameCurve target).polynomial (startPoint firstParent).coordinate firstStep.owner
      (finishPoint firstParent).coordinate firstRetained.acquired.traced.finishOwner}
    {actual_eq : actual = firstRetained.acquired.traced.trace.get}

/-- Derive the same actual signed return for an original singleton closed parent and its independent endpoint Steps. -/
def selfStartEquivalent
    (comparison : RootComparison firstRetained strip actual actual_eq)
    (geometry : CenteredPathChain [firstParent]
      (start := startPoint firstParent) (finish := startPoint firstParent))
    {root : Named} (roots : RootChain [firstParent] root root)
    (lastStep : Variation.Point.Step firstPrepared.lastSample increment) :
    NamedEquivalent
      (ownerRootName firstRetained.parents.covered.subdivision.terminalOwner.parameterNonzero
        firstRetained.parents.covered.subdivision.terminalOwner)
      (ownerRootName (ownerAtStart firstRetained.segment firstStep.owner).parameterNonzero
        (ownerAtStart firstRetained.segment firstStep.owner)) :=
  let endpoint := firstPrepared.shiftedSelfEquivalent geometry roots firstStep lastStep
  let finish := comparison.coveredFinishEquivalent lastStep
  NamedEquivalent.transport rfl firstRetained.initial_name_eq.symm (finish.trans endpoint)

end Singleton

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition.RootComparison

end
