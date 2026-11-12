module

meta import Purelib.Elab.ConstructiveInjectivity

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Fragments.Canonical
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Grid.Readings
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Grid.Comparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Data.List.Append
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewingRetraction

import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank.Clearance
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
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
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Periods
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
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Grid.Routes
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Primitive.Comparison
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

/-! # Target-specific fresh period points before one original reference acquisition

The actual fresh A and full corrected-B polynomial spines retain both
numerator programmes and the old holomorphic programmes. Their genuine
new primitive requests and physical fragment endpoints precede the one
old-source GridWord acquisition. Its literal point list contains both
fresh lists, so the two fresh reference words consume the SAME actual
reference execution without replacing roots or constructing another bank.
-/

public section

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

/-- The exact existing original acquireGridWord result, with its two complete original producer factories. -/
@[expose] def Acquired : Type _ :=
  (Σ acquired : {value : AcquiredFragments (framed := refined.fineBase)
      (original.vertices.owner original.frames vertex) period data canonical
      (original.vertices.coordinate_onGrid vertex) refined.included primitiveTarget
      primitivePositive primitiveMinimum //
    value = acquireFragments (framed := refined.fineBase)
      (original.vertices.owner original.frames vertex) period data canonical
      (original.vertices.coordinate_onGrid vertex) refined.included primitiveTarget primitivePositive primitiveMinimum},
  {value : GridWord period faces domains data canonical childChain completed acquired.val.request acquired.val.fragments
      oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras //
    value = fromFragments period faces domains data canonical childChain completed acquired.val.request
      acquired.val.fragments oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive
      extras targetCache bankCache})

variable {freshBank : BasedBranchBank refined.fine} {freshSheet : Fin 2}
    {freshOrdered : BasedBranchBank.Ordered freshBank freshSheet}
    {freshPaired : OrderedBranchPairs.Ordered.Paired freshOrdered}
    (fresh : Paired.PeriodPrograms.Prepared freshPaired) {aFloor bFloor : Nat}
    (aValues : PolynomialValues (parameter := parameter) (frame := frame) (fresh.aWalk 0) aFloor)
    (bValues : PolynomialValues (parameter := parameter) (frame := frame) (fresh.bWalk 0) bFloor)
    (aSourceStart aPeriodStart bSourceStart bPeriodStart : Nat)
    (freshTarget : Rational) (freshPositive : 0 < freshTarget)

/-- Actual fresh period/value owners and independent request floors chosen before reference observations. -/
@[expose] def PeriodPoints.Inputs : Type _ :=
  {inputs : Paired.PeriodPrograms.Prepared freshPaired ×
      PolynomialValues (parameter := parameter) (frame := frame) (fresh.aWalk 0) aFloor ×
      PolynomialValues (parameter := parameter) (frame := frame) (fresh.bWalk 0) bFloor ×
      (Nat × Nat × Nat × Nat × Rational) × List Canonical //
    inputs = (fresh, aValues, bValues, (aSourceStart, aPeriodStart, bSourceStart, bPeriodStart, freshTarget), extras)}

/-- The two actual original period-selection caches with their complete given-target factories. -/
@[expose] def PeriodPoints.Selections : Type _ :=
  {value : PrimitiveSelection (fresh.aWalk 0) aSourceStart aPeriodStart freshTarget freshPositive //
    value = (fresh.aWalk 0).primitiveSelection aSourceStart aPeriodStart freshTarget freshPositive} ×
  {value : PrimitiveSelection (fresh.bWalk 0) bSourceStart bPeriodStart freshTarget freshPositive //
    value = (fresh.bWalk 0).primitiveSelection bSourceStart bPeriodStart freshTarget freshPositive}

/-- Both exact physical initial-spine fragment caches depend on those same retained requests. -/
@[expose] def PeriodPoints.Physical
    (selected : PeriodPoints.Selections fresh aSourceStart aPeriodStart bSourceStart bPeriodStart
      freshTarget freshPositive) : Type _ :=
  {value : GridFragments refined.fine (anchor refined.fine freshSheet)
      (fresh.aWalk 0) aValues.1 selected.1.val domains //
    value = PolynomialSpine.gridFragments refined.fine (anchor refined.fine freshSheet)
      (fresh.aWalk 0) aValues.1 selected.1.val domains} ×
  {value : GridFragments refined.fine (anchor refined.fine freshSheet)
      (fresh.bWalk 0) bValues.1 selected.2.val domains //
    value = PolynomialSpine.gridFragments refined.fine (anchor refined.fine freshSheet)
      (fresh.bWalk 0) bValues.1 selected.2.val domains}

/-- The literal ordered fresh endpoint union selected before the original numerical acquisition. -/
@[expose] def PeriodPoints.PointUnion
    (selected : PeriodPoints.Selections fresh aSourceStart aPeriodStart bSourceStart bPeriodStart
      freshTarget freshPositive)
    (geometry : PeriodPoints.Physical domains fresh aValues bValues
      aSourceStart aPeriodStart bSourceStart bPeriodStart freshTarget freshPositive selected) : Type :=
  {value : List Canonical // value = geometry.1.val.points ++ (geometry.2.val.points ++ extras)}

/-- Read the retained literal endpoint union without unfolding its physical fragment indices. -/
@[expose] def PeriodPoints.PointUnion.points
    {selected : PeriodPoints.Selections fresh aSourceStart aPeriodStart bSourceStart bPeriodStart
      freshTarget freshPositive}
    {geometry : PeriodPoints.Physical domains fresh aValues bValues
      aSourceStart aPeriodStart bSourceStart bPeriodStart freshTarget freshPositive selected}
    (kept : PeriodPoints.PointUnion domains extras fresh aValues bValues
      aSourceStart aPeriodStart bSourceStart bPeriodStart freshTarget freshPositive selected geometry) :
    List Canonical := kept.val

/-- The SAME original source/reference acquisition on the actual supplied endpoint-union value. -/
@[expose] def PeriodPoints.Original (points : List Canonical) : Type _ :=
  {value : Acquired period faces domains data canonical childChain completed
      oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive points
      targetCache bankCache primitiveTarget primitivePositive primitiveMinimum //
    value = acquireGridWord period faces domains data canonical childChain completed oldTolerance oldPositive
      oldMinimum routeTarget chartTarget routePositive chartPositive points
      targetCache bankCache primitiveTarget primitivePositive primitiveMinimum}

/-- Both genuine fresh physical words consume the SAME actual reference bank and point-list ownership. -/
@[expose] def PeriodPoints.References
    (selected : PeriodPoints.Selections fresh aSourceStart aPeriodStart bSourceStart bPeriodStart
      freshTarget freshPositive)
    (geometry : PeriodPoints.Physical domains fresh aValues bValues
      aSourceStart aPeriodStart bSourceStart bPeriodStart freshTarget freshPositive selected)
    (points : List Canonical)
    (old : PeriodPoints.Original period faces domains data canonical childChain completed
      oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive
      targetCache bankCache primitiveTarget primitivePositive primitiveMinimum points) : Type _ :=
  PolynomialSpine.GridFragments.Reference geometry.1.val old.val.2.val.reference []
      old.val.2.val.childPoints (geometry.2.val.points ++ extras) ×
  PolynomialSpine.GridFragments.Reference geometry.2.val old.val.2.val.reference []
    (old.val.2.val.childPoints ++ geometry.1.val.points) extras

attribute [local irreducible] PeriodPoints.Inputs PeriodPoints.Selections PeriodPoints.Physical
  PeriodPoints.PointUnion PeriodPoints.PointUnion.points PeriodPoints.Original PeriodPoints.References in
set_option genInjectivity false in
/-- One actual reference execution covers the literal old+A+full-B point union and retains both fresh physical words.

The named fields retain original owners and complete producer factories.
Every fresh request and endpoint list precedes the old acquisition. The
same old reference is shared by both fresh words, preserving actual empty,
stationary, reversed and repeated roles. This is a joint execution cache,
not a replacement grid, bank, cycle, programme or root owner.
-/
structure PeriodPoints : Type _ where
  /-- The complete given fresh programme/cache and allocation input product. -/
  inputCache : PeriodPoints.Inputs (extras := extras) fresh aValues bValues
    aSourceStart aPeriodStart bSourceStart bPeriodStart freshTarget
  /-- The two actual target-specific primitive request selections. -/
  selectionCache : PeriodPoints.Selections fresh aSourceStart aPeriodStart bSourceStart bPeriodStart
    freshTarget freshPositive
  /-- Both physical fragment caches on those SAME selected requests. -/
  fragmentCache : PeriodPoints.Physical domains fresh aValues bValues
    aSourceStart aPeriodStart bSourceStart bPeriodStart freshTarget freshPositive selectionCache
  /-- The literal ordered fresh endpoint union and its complete factory. -/
  pointCache : PeriodPoints.PointUnion domains extras fresh aValues bValues
    aSourceStart aPeriodStart bSourceStart bPeriodStart freshTarget freshPositive selectionCache fragmentCache
  /-- The actual once-executed original source and reference acquisition. -/
  oldCache : PeriodPoints.Original period faces domains data canonical childChain completed
    oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive
    targetCache bankCache primitiveTarget primitivePositive primitiveMinimum pointCache.points
  /-- The actual two fresh words on that SAME retained reference bank. -/
  referenceCache : PeriodPoints.References period faces domains data canonical childChain completed
    oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
    targetCache bankCache primitiveTarget primitivePositive primitiveMinimum fresh aValues bValues
    aSourceStart aPeriodStart bSourceStart bPeriodStart freshTarget freshPositive
    selectionCache fragmentCache pointCache.points oldCache

attribute [local irreducible] PeriodPoints.Inputs PeriodPoints.Selections PeriodPoints.Physical
  PeriodPoints.PointUnion PeriodPoints.PointUnion.points PeriodPoints.Original PeriodPoints.References in
constructive_injectivity PeriodPoints

/-- Choose actual fresh requests/points before one original reference acquisition and close both fresh words. -/
def acquireWithPeriods : PeriodPoints period faces domains data canonical childChain completed
    oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
    targetCache bankCache primitiveTarget primitivePositive primitiveMinimum
    fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart freshTarget freshPositive :=
  let inputs : PeriodPoints.Inputs (extras := extras) fresh aValues bValues
      aSourceStart aPeriodStart bSourceStart bPeriodStart freshTarget :=
    ⟨(fresh, aValues, bValues, (aSourceStart, aPeriodStart, bSourceStart, bPeriodStart, freshTarget), extras), rfl⟩
  let aSelection : {value : PrimitiveSelection (fresh.aWalk 0) aSourceStart aPeriodStart freshTarget freshPositive //
      value = (fresh.aWalk 0).primitiveSelection aSourceStart aPeriodStart freshTarget freshPositive} :=
    ⟨(fresh.aWalk 0).primitiveSelection aSourceStart aPeriodStart freshTarget freshPositive, rfl⟩
  let bSelection : {value : PrimitiveSelection (fresh.bWalk 0) bSourceStart bPeriodStart freshTarget freshPositive //
      value = (fresh.bWalk 0).primitiveSelection bSourceStart bPeriodStart freshTarget freshPositive} :=
    ⟨(fresh.bWalk 0).primitiveSelection bSourceStart bPeriodStart freshTarget freshPositive, rfl⟩
  let selected : PeriodPoints.Selections fresh aSourceStart aPeriodStart bSourceStart bPeriodStart
      freshTarget freshPositive := (aSelection, bSelection)
  let aFragments : {value : GridFragments refined.fine (anchor refined.fine freshSheet)
      (fresh.aWalk 0) aValues.1 selected.1.val domains //
      value = PolynomialSpine.gridFragments refined.fine (anchor refined.fine freshSheet)
        (fresh.aWalk 0) aValues.1 selected.1.val domains} :=
    ⟨PolynomialSpine.gridFragments refined.fine (anchor refined.fine freshSheet)
      (fresh.aWalk 0) aValues.1 selected.1.val domains, rfl⟩
  let bFragments : {value : GridFragments refined.fine (anchor refined.fine freshSheet)
      (fresh.bWalk 0) bValues.1 selected.2.val domains //
      value = PolynomialSpine.gridFragments refined.fine (anchor refined.fine freshSheet)
        (fresh.bWalk 0) bValues.1 selected.2.val domains} :=
    ⟨PolynomialSpine.gridFragments refined.fine (anchor refined.fine freshSheet)
      (fresh.bWalk 0) bValues.1 selected.2.val domains, rfl⟩
  let geometry : PeriodPoints.Physical domains fresh aValues bValues
      aSourceStart aPeriodStart bSourceStart bPeriodStart freshTarget freshPositive selected :=
    (aFragments, bFragments)
  let union : PeriodPoints.PointUnion domains extras fresh aValues bValues
      aSourceStart aPeriodStart bSourceStart bPeriodStart freshTarget freshPositive selected geometry :=
    ⟨geometry.1.val.points ++ (geometry.2.val.points ++ extras), rfl⟩
  let old : PeriodPoints.Original period faces domains data canonical childChain completed
      oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive
      targetCache bankCache primitiveTarget primitivePositive primitiveMinimum union.val :=
    ⟨acquireGridWord period faces domains data canonical childChain completed oldTolerance oldPositive oldMinimum
      routeTarget chartTarget routePositive chartPositive union.val
      targetCache bankCache primitiveTarget primitivePositive primitiveMinimum, rfl⟩
  have cachedPoints : old.val.2.val.points = List.ofFn refined.fine.vertices.coordinate ++
      (old.val.2.val.childPoints ++ union.val) :=
    old.val.2.val.points_eq.trans (congrArg (fun actual : List Canonical =>
      List.ofFn refined.fine.vertices.coordinate ++ (actual ++ union.val)) old.val.2.val.childPoints_eq.symm)
  have allPoints : old.val.2.val.points = List.ofFn refined.fine.vertices.coordinate ++
      (old.val.2.val.childPoints ++ (geometry.1.val.points ++ (geometry.2.val.points ++ extras))) :=
    cachedPoints.trans (congrArg (fun actual : List Canonical =>
      List.ofFn refined.fine.vertices.coordinate ++ (old.val.2.val.childPoints ++ actual)) union.property)
  let aReference : PolynomialSpine.GridFragments.Reference geometry.1.val old.val.2.val.reference []
      old.val.2.val.childPoints (geometry.2.val.points ++ extras) :=
    PolynomialSpine.GridFragments.onReference geometry.1.val old.val.2.val.reference []
    old.val.2.val.childPoints (geometry.2.val.points ++ extras) allPoints
  have bPoints : old.val.2.val.points = List.ofFn refined.fine.vertices.coordinate ++
      ((old.val.2.val.childPoints ++ geometry.1.val.points) ++ (geometry.2.val.points ++ extras)) :=
    allPoints.trans (congrArg (fun actual : List Canonical =>
      List.ofFn refined.fine.vertices.coordinate ++ actual)
      (Data.List.Append.append_assoc old.val.2.val.childPoints geometry.1.val.points
        (geometry.2.val.points ++ extras)).symm)
  let bReference : PolynomialSpine.GridFragments.Reference geometry.2.val old.val.2.val.reference []
      (old.val.2.val.childPoints ++ geometry.1.val.points) extras :=
    PolynomialSpine.GridFragments.onReference geometry.2.val old.val.2.val.reference []
    (old.val.2.val.childPoints ++ geometry.1.val.points) extras bPoints
  let references : PeriodPoints.References period faces domains data canonical childChain completed
      oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
      targetCache bankCache primitiveTarget primitivePositive primitiveMinimum fresh aValues bValues
      aSourceStart aPeriodStart bSourceStart bPeriodStart freshTarget freshPositive selected geometry union.val old :=
    (aReference, bReference)
  ⟨inputs, selected, geometry, union, old, references⟩

namespace PeriodPoints

variable {period faces domains data canonical childChain completed oldTolerance oldPositive oldMinimum
  routeTarget chartTarget routePositive chartPositive extras targetCache bankCache primitiveTarget
  primitivePositive primitiveMinimum fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart
  freshTarget freshPositive}
    (kept : PeriodPoints period faces domains data canonical childChain completed
      oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
      targetCache bankCache primitiveTarget primitivePositive primitiveMinimum
      fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart freshTarget freshPositive)

/-- Read the SAME fresh original period/value owners and all pre-observation floor/target inputs. -/
@[expose] def inputs : Paired.PeriodPrograms.Prepared freshPaired ×
    PolynomialValues (parameter := parameter) (frame := frame) (fresh.aWalk 0) aFloor ×
    PolynomialValues (parameter := parameter) (frame := frame) (fresh.bWalk 0) bFloor ×
    (Nat × Nat × Nat × Nat × Rational) × List Canonical := kept.inputCache.val

/-- The complete original fresh period/value cache and allocation input product has its retained identity. -/
theorem inputs_eq : kept.inputs =
    (fresh, aValues, bValues, (aSourceStart, aPeriodStart, bSourceStart, bPeriodStart, freshTarget), extras) :=
  kept.inputCache.property

/-- Read the actual independently requested original A primitive-selection cache. -/
@[expose] def aSelection : PrimitiveSelection (fresh.aWalk 0) aSourceStart aPeriodStart freshTarget freshPositive :=
  kept.selectionCache.1.val

/-- The original A request was selected once before the point union and reference acquisition. -/
theorem aSelection_eq : kept.aSelection =
    (fresh.aWalk 0).primitiveSelection aSourceStart aPeriodStart freshTarget freshPositive :=
  kept.selectionCache.1.property

/-- Read the actual original A physical fragment/root/endpoint cache. -/
@[expose] def aFragments : GridFragments refined.fine (anchor refined.fine freshSheet)
    (fresh.aWalk 0) aValues.1 kept.aSelection domains := kept.fragmentCache.1.val

/-- The A geometry retains its complete original given-spine and selected-request factory. -/
theorem aFragments_eq : kept.aFragments = PolynomialSpine.gridFragments refined.fine
    (anchor refined.fine freshSheet) (fresh.aWalk 0) aValues.1 kept.aSelection domains := kept.fragmentCache.1.property

/-- Read the actual independently requested full corrected-B primitive-selection cache. -/
@[expose] def bSelection : PrimitiveSelection (fresh.bWalk 0) bSourceStart bPeriodStart freshTarget freshPositive :=
  kept.selectionCache.2.val

/-- The full B request was selected once before the point union and reference acquisition. -/
theorem bSelection_eq : kept.bSelection =
    (fresh.bWalk 0).primitiveSelection bSourceStart bPeriodStart freshTarget freshPositive :=
  kept.selectionCache.2.property

/-- Read the full original corrected-B physical fragment/root/endpoint cache. -/
@[expose] def bFragments : GridFragments refined.fine (anchor refined.fine freshSheet)
    (fresh.bWalk 0) bValues.1 kept.bSelection domains := kept.fragmentCache.2.val

/-- The full B geometry retains its exact original given-spine and selected-request factory. -/
theorem bFragments_eq : kept.bFragments = PolynomialSpine.gridFragments refined.fine
    (anchor refined.fine freshSheet) (fresh.bWalk 0) bValues.1 kept.bSelection domains := kept.fragmentCache.2.property

/-- Read the actual chosen fresh endpoint union, preserving every repeated slot and original order. -/
@[expose] def pointUnion : List Canonical := kept.pointCache.val

/-- The retained point union is the literal two fresh endpoint lists followed by the original extra list. -/
theorem pointUnion_eq : kept.pointUnion = kept.aFragments.points ++ (kept.bFragments.points ++ extras) :=
  kept.pointCache.property

/-- Read the same original source-fragment acquisition and reference word with both complete original factories. -/
@[expose] def oldAcquisition : Acquired period faces domains data canonical childChain completed
    oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive kept.pointUnion
    targetCache bankCache primitiveTarget primitivePositive primitiveMinimum := kept.oldCache.val

/-- The whole source/reference output is the single original acquireGridWord call on the stored point union. -/
theorem oldAcquisition_eq : kept.oldAcquisition = acquireGridWord period faces domains data canonical childChain
    completed oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive kept.pointUnion
    targetCache bankCache primitiveTarget primitivePositive primitiveMinimum := kept.oldCache.property

/-- Read the same original automatically acquired source fragments, not another controlled request. -/
@[expose] def sourceFragments : AcquiredFragments (framed := refined.fineBase)
    (original.vertices.owner original.frames vertex) period data canonical
    (original.vertices.coordinate_onGrid vertex) refined.included primitiveTarget primitivePositive primitiveMinimum :=
  kept.oldAcquisition.1.val

/-- Read the SAME old actual source/reference word on the union acquired before any P bank. -/
@[expose] def word : GridWord period faces domains data canonical childChain completed
    kept.sourceFragments.request kept.sourceFragments.fragments oldTolerance oldPositive oldMinimum
    routeTarget chartTarget routePositive chartPositive kept.pointUnion := kept.oldAcquisition.2.val

/-- Read the old numerical acquisition from that original word; both fresh words share this exact object. -/
@[expose] def reference : FaceSharedMeshes.Acquisition kept.word.budgets kept.word.primitives kept.word.later :=
  kept.word.reference

/-- Read the actual fresh A physical closed word on that SAME old bank and literal point list. -/
@[expose] def aReference : PolynomialSpine.GridFragments.Reference kept.aFragments kept.reference []
    kept.word.childPoints (kept.bFragments.points ++ extras) := kept.referenceCache.1

/-- Read the actual full corrected-B physical closed word on the SAME literal bank and point list. -/
@[expose] def bReference : PolynomialSpine.GridFragments.Reference kept.bFragments kept.reference []
    (kept.word.childPoints ++ kept.aFragments.points) extras := kept.referenceCache.2

section Cochains

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

variable {ordinary : Ordinary (Fibre.frameCurve frame).polynomial} {numericTolerance routeAllowance : Rational}
    {routeAllowancePositive : 0 < routeAllowance} {stage workFloor modelStage : Nat}
    {budgets : FaceMeshBudgets (standardDifferential (0 : Fin 1)) kept.word.points numericTolerance
      (numerator := ordinary.numerator) domains}
    {primitives : FacePrimitiveBank (standardDifferential (0 : Fin 1)) stage
      (numerator := ordinary.numerator) domains}
    {shared : FaceSharedMeshes budgets primitives}
    {triangles : {value : TriangleReadings primitives refined.fine.mesh //
      value = TriangleReadings.build primitives refined.fine.mesh}}

/-- The actual A comparison scalar reads the original fresh A word on the SAME P triangle bank. -/
theorem a_cochain_eq
    (routes : PolynomialSpine.GridFragments.Contacts kept.aFragments ordinary routeAllowance routeAllowancePositive)
    (work : PolynomialWork kept.aSelection.1.val.requests.covered workFloor ordinary.val)
    (models : work.Models modelStage)
    (compared : PolynomialSpine.GridFragments.Comparison kept.aReference routes shared triangles work models) :
    compared.value = wordValue (CanonicalEdgeValues.edgeValuation refined.fine.mesh triangles.val.values)
      (fresh.aWord 0) :=
  compared.original_value.trans (congrArg
    (wordValue (CanonicalEdgeValues.edgeValuation refined.fine.mesh triangles.val.values))
    (fresh.aWord_walk 0).symm)

/-- The actual B comparison scalar reads the WHOLE original corrected-B word, with every signed earlier-A occurrence. -/
theorem b_cochain_eq
    (routes : PolynomialSpine.GridFragments.Contacts kept.bFragments ordinary routeAllowance routeAllowancePositive)
    (work : PolynomialWork kept.bSelection.1.val.requests.covered workFloor ordinary.val)
    (models : work.Models modelStage)
    (compared : PolynomialSpine.GridFragments.Comparison kept.bReference routes shared triangles work models) :
    compared.value = wordValue (CanonicalEdgeValues.edgeValuation refined.fine.mesh triangles.val.values)
      (fresh.bWord 0) :=
  compared.original_value.trans (congrArg
    (wordValue (CanonicalEdgeValues.edgeValuation refined.fine.mesh triangles.val.values))
    (fresh.bWord_walk 0).symm)

end Cochains

end PeriodPoints

end GridWord

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry

end
