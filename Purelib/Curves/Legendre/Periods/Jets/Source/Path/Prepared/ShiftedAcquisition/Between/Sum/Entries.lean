module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Sum.Families

import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Child
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Calculus.Jet.Quadratic.Weighted.Widths
import Purelib.Data.Vector.Dependent
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Original cached child integrals on retained query families -/

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

/-- Construct one common-child integral from the SAME stored Sample family and three retained restriction banks. -/
def betweenEntry
    (index : Fin (dyadicEdges
      (firstLinked.shifted.acquired.mesh.depth + lastLinked.shifted.acquired.mesh.depth)
        UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint).length) :
    Quadratic.Basic.Certificate (lastOffset - firstOffset) :=
  let found := pairs.get index
  betweenDyadicCertificate sourcePrepared firstLinked lastLinked firstAligned lastAligned
    (firstLinked.shifted.dyadicPrepared firstPrepared firstPositions (refinementOccurrence.coarseIndex found.1))
    (lastLinked.shifted.dyadicPrepared lastPrepared lastPositions (refinementOccurrence.coarseIndex found.2))
    index found
    (firstEntry_eq (firstLinked.shifted.dyadicIndex (refinementOccurrence.coarseIndex found.1)))
    (lastEntry_eq (lastLinked.shifted.dyadicIndex (refinementOccurrence.coarseIndex found.2))) unit nonzero spatial
    (fun channel =>
      ((firstLinked.shifted.dyadicPrepared firstPrepared firstPositions
        (refinementOccurrence.coarseIndex found.1)).cell_allowance channel).trans_le firstBudget)
    (fun channel =>
      ((lastLinked.shifted.dyadicPrepared lastPrepared lastPositions
        (refinementOccurrence.coarseIndex found.2)).cell_allowance channel).trans_le lastBudget)
    (families.get index).val order coordinate
    (firstBase.bank (refinementOccurrence.coarseIndex found.1))
    (lastBase.bank (refinementOccurrence.coarseIndex found.2))
    (firstSlope.bank (refinementOccurrence.coarseIndex found.1))

variable
    (index : Fin (dyadicEdges
      (firstLinked.shifted.acquired.mesh.depth + lastLinked.shifted.acquired.mesh.depth)
        UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint).length)

/-- The original child entry reads its SAME retained first base restriction without any new restriction factory. -/
theorem betweenEntry_base :
    (betweenEntry sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope index).base =
      (firstBase.fineCell (pairs.get index).1).integralSample := by
  unfold betweenEntry
  apply betweenDyadicCertificate_base
    (sourcePrepared := sourcePrepared)
    (firstPrepared := firstLinked.shifted.dyadicPrepared firstPrepared firstPositions
      (refinementOccurrence.coarseIndex (pairs.get index).1))
    (lastPrepared := lastLinked.shifted.dyadicPrepared lastPrepared lastPositions
      (refinementOccurrence.coarseIndex (pairs.get index).2))

/-- The original child output reads the SAME independent last-target base restriction. -/
theorem betweenEntry_output :
    (betweenEntry sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope index).output =
      (lastBase.fineCell (pairs.get index).2).integralSample := by
  unfold betweenEntry
  apply betweenDyadicCertificate_output
    (sourcePrepared := sourcePrepared)
    (firstPrepared := firstLinked.shifted.dyadicPrepared firstPrepared firstPositions
      (refinementOccurrence.coarseIndex (pairs.get index).1))
    (lastPrepared := lastLinked.shifted.dyadicPrepared lastPrepared lastPositions
      (refinementOccurrence.coarseIndex (pairs.get index).2))

/-- The original child slope reads the SAME first-target independent derivative restriction. -/
theorem betweenEntry_slope :
    (betweenEntry sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope index).slope =
      (firstSlope.fineCell (pairs.get index).1).integralSample := by
  unfold betweenEntry
  apply betweenDyadicCertificate_slope
    (sourcePrepared := sourcePrepared)
    (firstPrepared := firstLinked.shifted.dyadicPrepared firstPrepared firstPositions
      (refinementOccurrence.coarseIndex (pairs.get index).1))
    (lastPrepared := lastLinked.shifted.dyadicPrepared lastPrepared lastPositions
      (refinementOccurrence.coarseIndex (pairs.get index).2))

/-- The actual child factor is the fixed original-parent density times its SAME common squared width. -/
theorem betweenEntry_factor :
    (betweenEntry sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope index).factor =
      betweenDensity patch count order coordinate *
        (betweenWidth firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth index) ^ 2 := by
  unfold betweenEntry
  apply betweenDyadicCertificate_factor
    (sourcePrepared := sourcePrepared)
    (firstPrepared := firstLinked.shifted.dyadicPrepared firstPrepared firstPositions
      (refinementOccurrence.coarseIndex (pairs.get index).1))
    (lastPrepared := lastLinked.shifted.dyadicPrepared lastPrepared lastPositions
      (refinementOccurrence.coarseIndex (pairs.get index).2))

/-- The original finite common-child integral caches, each with its whole actual constructor equation.

The query-family vector and three existing restriction banks remain indices.
The original DependentVector stores a single integral certificate per common
occurrence. No bound or integral identity is stored as an assumed field.
-/
@[expose] def BetweenIntegralEntries := Data.Vector.DependentVector (fun index =>
  { value : Quadratic.Basic.Certificate (lastOffset - firstOffset) //
    value = betweenEntry sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope index })

/-- Store each original common-child integral once on the SAME retained Sample family and restriction data. -/
def betweenIntegralEntries : BetweenIntegralEntries sourcePrepared firstLinked lastLinked firstAligned lastAligned
    firstPrepared lastPrepared firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial
      firstBudget lastBudget pairs families order coordinate firstBase lastBase firstSlope :=
  Data.Vector.DependentVector.ofFn (fun index =>
    let value := betweenEntry sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope index
    ⟨value, rfl⟩)

end Entries

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
