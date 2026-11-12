module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Requested.Cache
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Whole factory laws for retained two-target request caches

The stored pair vector, restriction banks, sample families and row integrals
read back their original factories on the same target requests.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents (ShiftedGeometry)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

variable {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (sourcePrepared : PreparedParent patch count floor covered targets)
    {range : Variation.Point.Range (patch.neighborhood count)}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ range.shiftedBound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ range.shiftedBound}
    {firstStrip : Norm.Basic.normSq firstOffset ≤ range.stripBound}
    {lastStrip : Norm.Basic.normSq lastOffset ≤ range.stripBound} {firstWidth lastWidth : AccuracyRequest}
    (firstLinked : Linked sourcePrepared range firstFrame firstAdmitted firstStrip firstWidth)
    (lastLinked : Linked sourcePrepared range lastFrame lastAdmitted lastStrip lastWidth)
    (firstAligned : Acquisition.Segment.RootComparisons.Alignment
      firstLinked.comparison.paths firstLinked.comparison.firstReference)
    (lastAligned : Acquisition.Segment.RootComparisons.Alignment
      lastLinked.comparison.paths lastLinked.comparison.firstReference)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1) (nonzero : lastOffset - firstOffset ≠ 0)
    (spatial : AccuracyRequest)
    {firstPoint lastPoint : LiftedPoint 2} {firstRoot lastRoot : Named}
    {firstGeometry : ShiftedGeometry (parameter := parameter) (increment := firstOffset)
      (target := firstFrame) (basis := basis) (count := count) firstPoint firstPoint firstRoot firstRoot}
    {lastGeometry : ShiftedGeometry (parameter := parameter) (increment := lastOffset)
      (target := lastFrame) (basis := basis) (count := count) lastPoint lastPoint lastRoot lastRoot}
    {firstNonempty : firstGeometry.parents ≠ []} {lastNonempty : lastGeometry.parents ≠ []}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    (firstRequested : ShiftedGeometry.Requested firstGeometry firstNonempty firstCurrent firstFloor firstRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)))
    (lastRequested : ShiftedGeometry.Requested lastGeometry lastNonempty lastCurrent lastFloor lastRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)))
    (firstPositions : Fin firstLinked.shifted.parents.covered.parents.length →
      Fin (firstRequested.request.shape.val.1 :: firstRequested.request.shape.val.2).length)
    (lastPositions : Fin lastLinked.shifted.parents.covered.parents.length →
      Fin (lastRequested.request.shape.val.1 :: lastRequested.request.shape.val.2).length)
    (firstEntry_eq : ∀ index,
      (firstRequested.request.shape.val.1 ::
        firstRequested.request.shape.val.2)[(firstPositions index).val]'(firstPositions index).isLt =
        firstLinked.shifted.childAt index)
    (lastEntry_eq : ∀ index,
      (lastRequested.request.shape.val.1 ::
        lastRequested.request.shape.val.2)[(lastPositions index).val]'(lastPositions index).isLt =
        lastLinked.shifted.childAt index)

namespace BetweenRequested

variable {sourcePrepared firstLinked lastLinked firstAligned lastAligned unit nonzero spatial}
    {firstRequested lastRequested firstPositions lastPositions firstEntry_eq lastEntry_eq}
    (retained : BetweenRequested sourcePrepared firstLinked lastLinked firstAligned lastAligned
    unit nonzero spatial firstRequested lastRequested firstPositions lastPositions firstEntry_eq lastEntry_eq)

/-- The stored pair vector retains its complete original refinement-pair factory equation. -/
theorem pairs_eq : retained.pairs = refinementPairs
    firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint := retained.1.property

/-- The stored first restriction product retains its whole original six-bank factory equation. -/
theorem firstBanks_eq : retained.firstBanks =
    dyadicRestrictionBanks firstLinked.shifted firstRequested.prepared firstPositions
      lastLinked.shifted.acquired.mesh.depth :=
  retained.2.1.property

/-- The independent last product retains its whole original six-bank factory equation. -/
theorem lastBanks_eq : retained.lastBanks =
    dyadicRestrictionBanks lastLinked.shifted lastRequested.prepared lastPositions
      firstLinked.shifted.acquired.mesh.depth :=
  retained.2.2.1.property

/-- The shared query-family vector retains its complete original producer at these SAME actual preparations. -/
theorem families_eq : retained.families =
    betweenFamilies sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstRequested.prepared lastRequested.prepared firstPositions lastPositions firstEntry_eq lastEntry_eq
      unit nonzero spatial firstRequested.localBound_lt.le lastRequested.localBound_lt.le retained.pairs :=
  retained.2.2.2.1.property

/-- The selected whole integral row retains its original producer on these SAME shared caches. -/
theorem row_eq (order coordinate : Fin 2) : retained.row order coordinate =
    BetweenIntegral.build sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstRequested.prepared lastRequested.prepared firstPositions lastPositions firstEntry_eq lastEntry_eq
      unit nonzero spatial firstRequested.localBound_lt.le lastRequested.localBound_lt.le
      retained.pairs retained.families order coordinate
      (retained.firstBanks.get (Specification.Table.baseIndex order coordinate))
      (retained.lastBanks.get (Specification.Table.baseIndex order coordinate))
      (retained.firstBanks.get (Specification.Table.slopeIndex order coordinate)) :=
  ((retained.2.2.2.2.get order).get coordinate).property

end BetweenRequested

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
