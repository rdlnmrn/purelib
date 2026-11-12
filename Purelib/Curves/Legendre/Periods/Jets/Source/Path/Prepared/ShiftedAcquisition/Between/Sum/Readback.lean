module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Sum.Certificate

import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Child
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Calculus.Jet.Quadratic.Weighted.Widths
import Purelib.Data.Vector.Dependent
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Exact coefficient readbacks of retained whole-parent integral certificates -/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Algebra
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
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
    {firstNewParents : List (CenteredEdge (Fibre.frameCurve firstFrame) basis)}
    {lastNewParents : List (CenteredEdge (Fibre.frameCurve lastFrame) basis)}
    {firstNewCover : CoveredParents count firstNewParents} {lastNewCover : CoveredParents count lastNewParents}
    {firstNewFloor lastNewFloor : Nat} {firstNewStart firstNewFinish lastNewStart lastNewFinish : LiftedPoint 2}
    {firstNewOriginal : LiftedPath 2 firstNewStart firstNewFinish}
    {lastNewOriginal : LiftedPath 2 lastNewStart lastNewFinish}
    {firstNewStage lastNewStage : Nat}
    {firstNewTargets : CellEndpoints.Targets firstNewOriginal firstNewStage}
    {lastNewTargets : CellEndpoints.Targets lastNewOriginal lastNewStage}
    (firstPrepared : PreparedParents firstNewCover firstNewFloor firstNewTargets)
    (lastPrepared : PreparedParents lastNewCover lastNewFloor lastNewTargets)
    (firstPositions : Fin firstLinked.shifted.parents.covered.parents.length → Fin firstNewParents.length)
    (lastPositions : Fin lastLinked.shifted.parents.covered.parents.length → Fin lastNewParents.length)
    (firstEntry_eq : ∀ index, firstNewParents[(firstPositions index).val]'(firstPositions index).isLt =
      firstLinked.shifted.childAt index)
    (lastEntry_eq : ∀ index, lastNewParents[(lastPositions index).val]'(lastPositions index).isLt =
      lastLinked.shifted.childAt index)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1) (nonzero : lastOffset - firstOffset ≠ 0)
    (spatial : AccuracyRequest)
    (firstBudget : firstNewTargets.localBound ≤
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)).tolerance)
    (lastBudget : lastNewTargets.localBound ≤
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)).tolerance)
    (pairs : Data.Vector.DependentVector (fun index => RefinementPair
      firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
        UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint index))

variable (families : BetweenFamilies sourcePrepared firstLinked lastLinked firstAligned lastAligned
    firstPrepared lastPrepared firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial
      firstBudget lastBudget pairs)
    (order coordinate : Fin 2)
    (firstBase : RefinementRestrictions firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
        (firstLinked.shifted.dyadicCells firstPrepared firstPositions (Specification.Table.baseIndex order coordinate)))
    (lastBase : RefinementRestrictions lastLinked.shifted.acquired.mesh.depth firstLinked.shifted.acquired.mesh.depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
        (lastLinked.shifted.dyadicCells lastPrepared lastPositions (Specification.Table.baseIndex order coordinate)))
    (firstSlope : RefinementRestrictions firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
        (firstLinked.shifted.dyadicCells firstPrepared firstPositions
          (Specification.Table.slopeIndex order coordinate)))

namespace BetweenIntegral

variable {sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared}
    {firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs}
    {families order coordinate firstBase lastBase firstSlope}
    (retained : BetweenIntegral sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope)

/-- The actual retained base is the original first-target base global cell sum in exact child order. -/
theorem base : retained.certificate.base =
    sumFin (fun index => ((firstPrepared.entry (firstPositions index)).preparation.cell.models.cell
      (Specification.Table.baseIndex order coordinate)).integralSample) :=
  (congrArg (fun certificate : Quadratic.Basic.Certificate (lastOffset - firstOffset) => certificate.base)
    retained.certificate_eq).trans
      (betweenIntegral_base sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope retained.entries)

/-- The actual retained output is the original independent last-target base global cell sum in exact child order. -/
theorem output : retained.certificate.output =
    sumFin (fun index => ((lastPrepared.entry (lastPositions index)).preparation.cell.models.cell
      (Specification.Table.baseIndex order coordinate)).integralSample) :=
  (congrArg (fun certificate : Quadratic.Basic.Certificate (lastOffset - firstOffset) => certificate.output)
    retained.certificate_eq).trans
      (betweenIntegral_output sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope retained.entries)

/-- The retained slope is the original first-target independent derivative sum in exact child order. -/
theorem slope : retained.certificate.slope =
    sumFin (fun index => ((firstPrepared.entry (firstPositions index)).preparation.cell.models.cell
      (Specification.Table.slopeIndex order coordinate)).integralSample) :=
  (congrArg (fun certificate : Quadratic.Basic.Certificate (lastOffset - firstOffset) => certificate.slope)
    retained.certificate_eq).trans
      (betweenIntegral_slope sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope retained.entries)

/-- The SAME retained sum has its exact computed original-patch density, independent of both mesh counts. -/
theorem factor : retained.certificate.factor = betweenDensity patch count order coordinate :=
  (congrArg (fun certificate : Quadratic.Basic.Certificate (lastOffset - firstOffset) => certificate.factor)
    retained.certificate_eq).trans
      (betweenIntegral_factor sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope retained.entries)

end BetweenIntegral

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
