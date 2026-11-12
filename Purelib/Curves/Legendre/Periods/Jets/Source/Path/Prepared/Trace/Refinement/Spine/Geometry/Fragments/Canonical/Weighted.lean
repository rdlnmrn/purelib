module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Fragments.Canonical.Periods
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningValues.Periods
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical.Polynomial
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Dependent

import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank.Clearance
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ClosedReduction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.GeometricBasis
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Chain
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Fragments
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Occurrences
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Annulus
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Periods
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Stems
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Coordinates
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Paired
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Paths.PreparedPathSources
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathTrace.Lineage
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Grid
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Primitive.Comparison
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

/-! # Actual signed-coordinate allocation before the joint fresh endpoint acquisition

Both retained integer-coordinate banks and the public tolerance select a
genuine positive component request before fresh primitive geometry or
points. The existing PeriodPoints acquisition then supplies one original
reference bank for the literal old+A+whole-B endpoint union.
-/

public section

-- The builtin check revisits shared dependent terms exponentially here.
-- Retain the original parameter telescope; check its compiled binder usage.
set_option linter.unusedSectionVars false

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Fragment.LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries renaming LiftedSources -> SourceSpine
open Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries.LiftedSources (Rooted)
open Fragment.RouteWords (RouteRequest canonicalRoute)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests (RouteChartRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSwitchedRefinements (SwitchedPathChain)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.PreparedPathSources (PathSources)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.LiftedPuncturedGrid (ClearanceRefinement)
open Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement (PeriodFaces)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

variable {parameter : Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
    {original : LiftedPuncturedGrid base} {patchCount : Nat}
    {patches : List (ContinuedNeighborhood (Fibre.frameCurve frame).polynomial patchCount)}
    {clearance : BranchCellBank.ClearancePreparation base.bank.toBranchCellBank patches}
    {refined : ClearanceRefinement original clearance}
    {vertex : Fin original.vertices.count}
    (period : PeriodWalk base.bank.grid (original.vertices.coordinate vertex)
      (original.vertices.owner original.frames vertex) (standardDifferential (0 : Fin 1)))
    (faces : PeriodFaces refined vertex period)
    (domains : FaceDomainBank refined.fine.frames refined.fineBase.faces.regulars)
    {count floor precision rootStage : Nat}
    {inputCenters : Centers (frame := frame) (basis := standardDifferential (0 : Fin 1))
      (sheet := 0) period.closed.traced.lineage}
    {materialized : OwnerPath (Paths.polynomial parameter) (original.vertices.coordinate vertex)
      (original.vertices.owner original.frames vertex) (original.vertices.coordinate vertex)
      (PreparedPathGluing.finishOwner period.closed.traced.prepared)}
    {factory : materialized = period.closed.traced.lineage.ownerPath} {diameter : Rational} {positive : 0 < diameter}
    (data : Materialized.Geometry (count := count)
      diameter positive period.closed.traced.lineage inputCenters materialized factory)
    (canonical : inputCenters = Centers.build period.closed.traced.lineage)
    (childChain : CenteredPathChain data.parents
      (start := (⟨original.vertices.coordinate vertex, 0⟩ : LiftedPoint 2))
      (finish := (⟨original.vertices.coordinate vertex, 0⟩ : LiftedPoint 2)))
    {targets : CellEndpoints.Targets childChain.path precision}
    {computed : targets = CellEndpoints.Targets.build childChain.path precision}
    {sourceBank : Sources (count := count) (floor := floor) (targets := targets) data}
    {walkPositive : 0 < period.closed.walk.edgeCount}
    (completed : Sources.Occurrences (count := count) (floor := floor)
      (original.vertices.owner original.frames vertex) period.closed data childChain
      precision rootStage targets computed sourceBank walkPositive)
    {requestTarget : Rational} (supplied : ControlledSumRequest data.parents count requestTarget)
    (pieces : Fragments (framed := refined.fineBase)
      (original.vertices.owner original.frames vertex) period data canonical
      (original.vertices.coordinate_onGrid vertex) refined.included supplied)
    (oldTolerance : Rational) (oldPositive : 0 < oldTolerance) (oldMinimum : Nat)
    (routeTarget chartTarget : Rational) (routePositive : 0 < routeTarget) (chartPositive : 0 < chartTarget)
    (extras : List Canonical)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (anchor)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk (PolynomialValues PrimitiveSelection)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk (PolynomialSpine)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine (GridFragments)

namespace GridWord

variable (targetCache : {value : CellEndpoints.Targets childChain.path precision // value = targets})
    (bankCache : {value : Sources (count := count) (floor := floor) (targets := targets) data // value = sourceBank})
    (primitiveTarget : Rational) (primitivePositive : 0 < primitiveTarget) (primitiveMinimum : Nat)

variable {freshBank : BasedBranchBank refined.fine} {freshSheet : Fin 2}
    {freshOrdered : BasedBranchBank.Ordered freshBank freshSheet}
    {freshPaired : OrderedBranchPairs.Ordered.Paired freshOrdered}
    (fresh : Paired.PeriodPrograms.Prepared freshPaired) {aFloor bFloor : Nat}
    (aValues : PolynomialValues (parameter := parameter) (frame := frame) (fresh.aWalk 0) aFloor)
    (bValues : PolynomialValues (parameter := parameter) (frame := frame) (fresh.bWalk 0) bFloor)
    (aSourceStart aPeriodStart bSourceStart bPeriodStart : Nat)

variable {period faces domains data canonical childChain completed oldTolerance oldPositive oldMinimum
  routeTarget chartTarget routePositive chartPositive extras targetCache bankCache primitiveTarget
  primitivePositive primitiveMinimum fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion
open Purelib.Data.Vector (DependentVector)
open Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement
open Purelib.Riemann.Periods
open Purelib.Topology.Polygon.Stokes (triangleEdgeOccurrences)
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes (BoundaryCycleDecomposition)

variable {oldBank : BasedBranchBank original} {oldSheet annulusSheet stripSheet : Fin 2}
    {ordered : BasedBranchBank.Ordered oldBank oldSheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    {periods : Paired.PeriodPrograms.Prepared paired}
    {annuli : DependentVector (fun index : BranchIsolation.Data.Index branches =>
      {value : refined.Annulus index annulusSheet // value = refined.annulus index annulusSheet})}
    {strips : DependentVector (fun index : BranchIsolation.Data.Index branches =>
      {value : refined.StemStrip oldBank freshBank (annuli.get index).val stripSheet //
        value = refined.stemStrip oldBank freshBank (annuli.get index).val stripSheet})}
    {source : refined.PairCompilation oldBank freshBank periods annuli strips (0 : Fin 1)}
    {freshBasis : fresh.GeometricBasis}
    {boundary : BoundaryCycleDecomposition (triangleEdgeOccurrences refined.fine.mesh.triangulation.faces)}
    {boundaryFactory : boundary = refined.fine.boundaryComponents}
    (coordinates : PairCoordinates source freshBasis boundary boundaryFactory)
    (requested : Rational) (positiveRequest : 0 < requested)

/-- Retain both actual original coefficient caches and the positive share they genuinely select before geometry. -/
@[expose] def WeightedPoints.Choices : Type _ :=
  (Σ first : {value : WeightedPeriods.Coefficients coordinates.a.coordinates.periodWeights //
      value = WeightedPeriods.Coefficients.build coordinates.a.coordinates.periodWeights},
  Σ last : {value : WeightedPeriods.Coefficients coordinates.b.coordinates.periodWeights //
      value = WeightedPeriods.Coefficients.build coordinates.b.coordinates.periodWeights},
  {value : Rational // value = PeriodCanonical.weightedPeriodShare first.val last.val requested ∧ 0 < value})

variable (period faces domains data canonical childChain completed oldTolerance oldPositive oldMinimum
  routeTarget chartTarget routePositive chartPositive extras targetCache bankCache primitiveTarget
  primitivePositive primitiveMinimum fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart)

/-- The actual coordinate owners/public tolerance and one original target-specific joint acquisition.

The two coefficient banks and their positive share precede every fresh
request and endpoint list. All old source/root/period owners and complete
reference factories remain those of the original PeriodPoints output.
-/
@[expose] def WeightedPoints : Type _ :=
  {value : PairCoordinates source freshBasis boundary boundaryFactory × Rational //
    value = (coordinates, requested) ∧ 0 < requested} ×
  (Σ chosen : WeightedPoints.Choices coordinates requested,
  {value : PeriodPoints period faces domains data canonical childChain completed
      oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
      targetCache bankCache primitiveTarget primitivePositive primitiveMinimum
      fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart chosen.2.2.val chosen.2.2.property.2 //
    value = acquireWithPeriods period faces domains data canonical childChain completed
      oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
      targetCache bankCache primitiveTarget primitivePositive primitiveMinimum
      fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart chosen.2.2.val chosen.2.2.property.2})

/-- Select target-specific requests/points using GIVEN original coefficient caches and whole factories.

Both complete coefficient caches are forwarded into the returned value.
Only h-dependent requests, geometry, endpoint lists and the one reference
acquisition are new work. Their original branches and order are unchanged.
-/
def acquireWeightedWithCoefficients
    (first : {value : WeightedPeriods.Coefficients coordinates.a.coordinates.periodWeights //
      value = WeightedPeriods.Coefficients.build coordinates.a.coordinates.periodWeights})
    (last : {value : WeightedPeriods.Coefficients coordinates.b.coordinates.periodWeights //
      value = WeightedPeriods.Coefficients.build coordinates.b.coordinates.periodWeights}) : WeightedPoints period
        faces domains data canonical childChain completed
    oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
    targetCache bankCache primitiveTarget primitivePositive primitiveMinimum
    fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart coordinates requested :=
  let share : {value : Rational // value = PeriodCanonical.weightedPeriodShare first.val last.val requested ∧
      0 < value} :=
    ⟨PeriodCanonical.weightedPeriodShare first.val last.val requested, rfl,
      PeriodCanonical.weightedPeriodShare_positive first.val last.val positiveRequest⟩
  let chosen : WeightedPoints.Choices coordinates requested := ⟨first, last, share⟩
  let points : {value : PeriodPoints period faces domains data canonical childChain completed
      oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
      targetCache bankCache primitiveTarget primitivePositive primitiveMinimum
      fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart chosen.2.2.val chosen.2.2.property.2 //
      value = acquireWithPeriods period faces domains data canonical childChain completed
        oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
        targetCache bankCache primitiveTarget primitivePositive primitiveMinimum
        fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart
        chosen.2.2.val chosen.2.2.property.2} :=
    ⟨acquireWithPeriods period faces domains data canonical childChain completed
      oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
      targetCache bankCache primitiveTarget primitivePositive primitiveMinimum
      fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart
      chosen.2.2.val chosen.2.2.property.2, rfl⟩
  ⟨⟨(coordinates, requested), rfl, positiveRequest⟩, chosen, points⟩

/-- Select the genuine signed-coordinate payment and then acquire fresh points/reference once at that exact target.

Only original coefficient and PeriodPoints producers execute. The two
numerator banks are later consumers of the same retained physical/root
acquisition; their independent requested word/cochain and stage floors
are not selected or overwritten by this geometry operation.
-/
def acquireWeightedPeriods : WeightedPoints period faces domains data canonical childChain completed
    oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
    targetCache bankCache primitiveTarget primitivePositive primitiveMinimum
    fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart coordinates requested :=
  let first : {value : WeightedPeriods.Coefficients coordinates.a.coordinates.periodWeights //
      value = WeightedPeriods.Coefficients.build coordinates.a.coordinates.periodWeights} :=
    coordinates.a.coordinates.periodCoefficients
  let last : {value : WeightedPeriods.Coefficients coordinates.b.coordinates.periodWeights //
      value = WeightedPeriods.Coefficients.build coordinates.b.coordinates.periodWeights} :=
    coordinates.b.coordinates.periodCoefficients
  acquireWeightedWithCoefficients
    (period := period) (faces := faces) (domains := domains) (data := data) (canonical := canonical)
    (childChain := childChain) (completed := completed) (oldTolerance := oldTolerance) (oldPositive := oldPositive)
    (oldMinimum := oldMinimum) (routeTarget := routeTarget) (chartTarget := chartTarget)
    (routePositive := routePositive) (chartPositive := chartPositive) (extras := extras)
    (targetCache := targetCache) (bankCache := bankCache) (primitiveTarget := primitiveTarget)
    (primitivePositive := primitivePositive) (primitiveMinimum := primitiveMinimum) (fresh := fresh)
    (aValues := aValues) (bValues := bValues) (aSourceStart := aSourceStart) (aPeriodStart := aPeriodStart)
    (bSourceStart := bSourceStart) (bPeriodStart := bPeriodStart) (coordinates := coordinates)
    (requested := requested) (positiveRequest := positiveRequest) (first := first) (last := last)

namespace WeightedPoints

variable {period faces domains data canonical childChain completed oldTolerance oldPositive oldMinimum
  routeTarget chartTarget routePositive chartPositive extras targetCache bankCache primitiveTarget
  primitivePositive primitiveMinimum fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart
  coordinates requested}
    (kept : WeightedPoints period faces domains data canonical childChain completed
      oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
      targetCache bankCache primitiveTarget primitivePositive primitiveMinimum
      fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart coordinates requested)

/-- Read the SAME full canonical coordinate owner retained before target selection. -/
@[expose] def coordinateData : PairCoordinates source freshBasis boundary boundaryFactory := kept.1.val.1

/-- The complete retained coordinate object is the actual original input. -/
theorem coordinateData_eq : kept.coordinateData = coordinates := congrArg Prod.fst kept.1.property.1

include kept in
/-- The original public tolerance remains positive in the retained input certificate. -/
theorem target_positive : 0 < requested := kept.1.property.2

/-- Read the actual signed original first-row coefficient cache without rebuilding conversions or norms. -/
@[expose] def firstCoefficients : WeightedPeriods.Coefficients coordinates.a.coordinates.periodWeights :=
  kept.2.1.1.val

/-- Read the actual signed whole second-row coefficient cache from the same pre-geometry selection. -/
@[expose] def lastCoefficients : WeightedPeriods.Coefficients coordinates.b.coordinates.periodWeights :=
  kept.2.1.2.1.val

/-- Read the actual selected fresh component share. -/
@[expose] def share : Rational := kept.2.1.2.2.val

/-- The complete share uses the retained true coefficient masses and original public tolerance. -/
theorem share_eq : kept.share =
    PeriodCanonical.weightedPeriodShare kept.firstCoefficients kept.lastCoefficients requested :=
  kept.2.1.2.2.property.1

/-- The actual share is positive even for empty or zero-weight coordinate rows. -/
theorem share_positive : 0 < kept.share := kept.2.1.2.2.property.2

/-- Read the actual original joint point/reference acquisition performed at that SAME selected share. -/
@[expose] def periodPoints : PeriodPoints period faces domains data canonical childChain completed
    oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
    targetCache bankCache primitiveTarget primitivePositive primitiveMinimum
    fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart kept.share kept.share_positive :=
  kept.2.2.val

/-- The complete joint acquisition has the literal original target-specific producer at the retained share. -/
theorem periodPoints_eq : kept.periodPoints =
    acquireWithPeriods period faces domains data canonical childChain completed
    oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
    targetCache bankCache primitiveTarget primitivePositive primitiveMinimum
    fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart kept.share kept.share_positive :=
  kept.2.2.property

/-- The first actual weighted row is paid by the retained fresh-programme component budget. -/
theorem first_cap : 52 * kept.share ≤ kept.firstCoefficients.perComponent (requested / 4) :=
  (congrArg (fun amount : Rational => 52 * amount) kept.share_eq).trans_le
    (PeriodCanonical.weightedPeriodShare_first kept.firstCoefficients kept.lastCoefficients requested)

/-- The full second actual weighted row is independently paid by that same component share. -/
theorem last_cap : 52 * kept.share ≤ kept.lastCoefficients.perComponent (requested / 4) :=
  (congrArg (fun amount : Rational => 52 * amount) kept.share_eq).trans_le
    (PeriodCanonical.weightedPeriodShare_last kept.firstCoefficients kept.lastCoefficients requested)

/-- The original source/cochain quarter target is also paid without retagging any selected request. -/
theorem source_cap : kept.share ≤ requested / 4 :=
  kept.share_eq.trans_le
    (PeriodCanonical.weightedPeriodShare_le_quarter
      kept.firstCoefficients kept.lastCoefficients kept.target_positive.le)

section GivenCoefficients

variable (first : {value : WeightedPeriods.Coefficients coordinates.a.coordinates.periodWeights //
      value = WeightedPeriods.Coefficients.build coordinates.a.coordinates.periodWeights}) (last : {value :
        WeightedPeriods.Coefficients coordinates.b.coordinates.periodWeights //
      value = WeightedPeriods.Coefficients.build coordinates.b.coordinates.periodWeights})
    (positiveRequest : 0 < requested)

/-- The target-specific acquisition forwards the literal GIVEN first coefficient cache. -/
theorem acquireWeightedWithCoefficients_first :
    (acquireWeightedWithCoefficients
      (period := period) (faces := faces) (domains := domains) (data := data) (canonical := canonical)
      (childChain := childChain) (completed := completed) (oldTolerance := oldTolerance)
      (oldPositive := oldPositive) (oldMinimum := oldMinimum) (routeTarget := routeTarget)
      (chartTarget := chartTarget) (routePositive := routePositive) (chartPositive := chartPositive)
      (extras := extras) (targetCache := targetCache) (bankCache := bankCache) (primitiveTarget := primitiveTarget)
      (primitivePositive := primitivePositive) (primitiveMinimum := primitiveMinimum) (fresh := fresh)
      (aValues := aValues) (bValues := bValues) (aSourceStart := aSourceStart) (aPeriodStart := aPeriodStart)
      (bSourceStart := bSourceStart) (bPeriodStart := bPeriodStart) (coordinates := coordinates)
      (requested := requested) (positiveRequest := positiveRequest) (first := first) (last := last)).firstCoefficients =
    first.val :=
  Eq.refl first.val

/-- Its second coefficient cache is the SAME full given value with the actual signed corrected-B weights. -/
theorem acquireWeightedWithCoefficients_last :
    (acquireWeightedWithCoefficients
      (period := period) (faces := faces) (domains := domains) (data := data) (canonical := canonical)
      (childChain := childChain) (completed := completed) (oldTolerance := oldTolerance)
      (oldPositive := oldPositive) (oldMinimum := oldMinimum) (routeTarget := routeTarget)
      (chartTarget := chartTarget) (routePositive := routePositive) (chartPositive := chartPositive)
      (extras := extras) (targetCache := targetCache) (bankCache := bankCache) (primitiveTarget := primitiveTarget)
      (primitivePositive := primitivePositive) (primitiveMinimum := primitiveMinimum) (fresh := fresh)
      (aValues := aValues) (bValues := bValues) (aSourceStart := aSourceStart) (aPeriodStart := aPeriodStart)
      (bSourceStart := bSourceStart) (bPeriodStart := bPeriodStart) (coordinates := coordinates)
      (requested := requested) (positiveRequest := positiveRequest) (first := first) (last := last)).lastCoefficients =
    last.val :=
  Eq.refl last.val

end GivenCoefficients

end WeightedPoints

end GridWord

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry

end
