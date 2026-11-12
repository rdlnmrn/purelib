module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Sum.Entries

import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Child
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Calculus.Jet.Quadratic.Weighted.Widths
import Purelib.Data.Vector.Dependent
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Width-paid ordered sums of retained child integral certificates -/

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

section Entries

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


variable {index}
    (entries : BetweenIntegralEntries sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstPrepared lastPrepared firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial
        firstBudget lastBudget pairs families order coordinate firstBase lastBase firstSlope)

/-- Construct the original width-paid ordered integral sum from those SAME stored child certificates.

Actual common dyadic widths are nonnegative and sum to one. Every factor
is internally read from its retained original child factory, so the original
sumWithWidths computes the fixed-parent bound without a fine-count factor.
The two independent target allocations and all original models remain intact.
-/
def betweenIntegral : Quadratic.Basic.Certificate (lastOffset - firstOffset) :=
  Quadratic.Basic.Certificate.sumWithWidths (fun index => (entries.get index).val)
    (betweenWidth firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth)
    (betweenDensity patch count order coordinate) (betweenDensity_nonnegative patch count order coordinate)
    (fun index => dyadicEdges_width_nonnegative
      (firstLinked.shifted.acquired.mesh.depth + lastLinked.shifted.acquired.mesh.depth)
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint (show (0 : Rational) ≤ 1 by decide +kernel)
      index)
    (fun index => ((congrArg (fun certificate : Quadratic.Basic.Certificate (lastOffset - firstOffset) =>
      certificate.factor) (entries.get index).property).trans
        (betweenEntry_factor sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
          firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
            families order coordinate firstBase lastBase firstSlope index)).le)

/-- The assembled base is the SAME first-target global cell sum in its original retained child order. -/
theorem betweenIntegral_base :
    (betweenIntegral sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope entries).base =
      sumFin (fun index => ((firstPrepared.entry (firstPositions index)).preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).integralSample) := by
  have fields := FiniteSum.Fin.sumFin_congr (fun index =>
    (congrArg (fun certificate : Quadratic.Basic.Certificate (lastOffset - firstOffset) => certificate.base)
      (entries.get index).property).trans
        (betweenEntry_base sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
          firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
            families order coordinate firstBase lastBase firstSlope index))
  exact fields.trans ((firstBase.sample_sum (fun index => (pairs.get index).1)
    (show (0 : Rational) < 1 by decide +kernel)).trans
      (firstLinked.shifted.dyadicCells_sum firstPrepared firstPositions
        (Specification.Table.baseIndex order coordinate)))

/-- The assembled output is the SAME independent last-target global cell sum in its original retained child order. -/
theorem betweenIntegral_output :
    (betweenIntegral sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope entries).output =
      sumFin (fun index => ((lastPrepared.entry (lastPositions index)).preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).integralSample) := by
  have fields := FiniteSum.Fin.sumFin_congr (fun index =>
    (congrArg (fun certificate : Quadratic.Basic.Certificate (lastOffset - firstOffset) => certificate.output)
      (entries.get index).property).trans
        (betweenEntry_output sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
          firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
            families order coordinate firstBase lastBase firstSlope index))
  have sameCount : (dyadicEdges
      (firstLinked.shifted.acquired.mesh.depth + lastLinked.shifted.acquired.mesh.depth)
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint).length =
        (dyadicEdges (lastLinked.shifted.acquired.mesh.depth + firstLinked.shifted.acquired.mesh.depth)
          UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint).length :=
    congrArg (fun depth => (dyadicEdges depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint).length)
      (Nat.add_comm firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth)
  exact fields.trans ((lastBase.sample_sum_cast sameCount (fun index => (pairs.get index).2)
    (show (0 : Rational) < 1 by decide +kernel)).trans
      (lastLinked.shifted.dyadicCells_sum lastPrepared lastPositions (Specification.Table.baseIndex order coordinate)))

/-- The assembled slope is the SAME first-target derivative sum on its independent third restriction bank. -/
theorem betweenIntegral_slope :
    (betweenIntegral sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope entries).slope =
      sumFin (fun index => ((firstPrepared.entry (firstPositions index)).preparation.cell.models.cell
        (Specification.Table.slopeIndex order coordinate)).integralSample) := by
  have fields := FiniteSum.Fin.sumFin_congr (fun index =>
    (congrArg (fun certificate : Quadratic.Basic.Certificate (lastOffset - firstOffset) => certificate.slope)
      (entries.get index).property).trans
        (betweenEntry_slope sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
          firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
            families order coordinate firstBase lastBase firstSlope index))
  exact fields.trans ((firstSlope.sample_sum (fun index => (pairs.get index).1)
    (show (0 : Rational) < 1 by decide +kernel)).trans
      (firstLinked.shifted.dyadicCells_sum firstPrepared firstPositions
        (Specification.Table.slopeIndex order coordinate)))

/-- The actual ordered sum factor is exactly the original patch/physical-parent density.

The proof uses the actual widths of the original common refined word and
their exact total one. It does not bound or replace any old recorded factor,
and retains stationary physical parents and zero density.
-/
theorem betweenIntegral_factor :
    (betweenIntegral sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope entries).factor =
      betweenDensity patch count order coordinate := by
  change betweenDensity patch count order coordinate *
    (sumFin (betweenWidth firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth)) ^ 2 = _
  have widths : sumFin (betweenWidth firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth) =
      (1 : Rational) :=
    (dyadicEdges_sum_widths
      (firstLinked.shifted.acquired.mesh.depth + lastLinked.shifted.acquired.mesh.depth)
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint).trans (by decide +kernel)
  exact (congrArg (fun width : Rational => betweenDensity patch count order coordinate * width ^ 2) widths).trans
    ((congrArg (fun power : Rational => betweenDensity patch count order coordinate * power)
      (show (1 : Rational) ^ 2 = 1 by decide +kernel)).trans (Field.mul_one_direct _))

end Entries

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
