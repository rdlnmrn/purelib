module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Sum.Integral

import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Child
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Calculus.Jet.Quadratic.Weighted.Widths
import Purelib.Data.Vector.Dependent
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Retained whole-parent integral certificates and their readbacks -/

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

/-- The SAME stored common-child integral vector and its original width-paid whole-parent certificate.

The existing Sample-family vector and three restriction banks are nominal
inputs. Both cached outputs retain their whole original factory equations.
The Sample family is not rebuilt for another row; one supplied family can
serve every order and coordinate without duplicating its query work.
-/
@[expose] def BetweenIntegral :=
  (entries : { value : BetweenIntegralEntries sourcePrepared firstLinked lastLinked firstAligned lastAligned
    firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope //
    value = betweenIntegralEntries sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope }) ×
  { certificate : Quadratic.Basic.Certificate (lastOffset - firstOffset) //
    certificate = betweenIntegral sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope entries.val }

namespace BetweenIntegral

/-- Store every original common-child integral once, then its actual ordered width-paid sum once. -/
def build : BetweenIntegral sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope :=
  let entries := betweenIntegralEntries sourcePrepared firstLinked lastLinked firstAligned lastAligned
    firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope
  let certificate := betweenIntegral sourcePrepared firstLinked lastLinked firstAligned lastAligned
    firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope entries
  ⟨⟨entries, rfl⟩, ⟨certificate, rfl⟩⟩

variable {sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared}
    {firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs}
    {families order coordinate firstBase lastBase firstSlope}
    (retained : BetweenIntegral sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope)

/-- Read the SAME stored vector of actual integral entries and their complete constructor equations. -/
@[expose] def entries : BetweenIntegralEntries sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope := retained.1.val

/-- Read the SAME stored original whole-parent Taylor certificate. -/
@[expose] def certificate : Quadratic.Basic.Certificate (lastOffset - firstOffset) := retained.2.val

/-- The entire entry vector retains its original actual common-child producer without recomputation. -/
theorem entries_eq : retained.entries =
    betweenIntegralEntries sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope := retained.1.property

/-- The stored whole-parent certificate retains its original sumWithWidths factory on the SAME entry vector. -/
theorem certificate_eq : retained.certificate =
    betweenIntegral sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstPrepared lastPrepared
      firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs
        families order coordinate firstBase lastBase firstSlope retained.entries := retained.2.property

end BetweenIntegral

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
