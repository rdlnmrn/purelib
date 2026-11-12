module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Fragments
public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Occurrences
public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Polynomial.Periods
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Directed
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathChartRoutes
import Purelib.Data.List.Permutation
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Periods
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank.Clearance
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.GeometricBasis
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Chain
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.RootChain
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Annulus
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
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Polynomial

/-! # Actual canonical child-word and point-bank acquisition

A given occurrence completion supplies its original root cache and child
chain. The original grid/domain constructors place those same children,
then the literal vertex-plus-source point list selects one old reference
bank. Its physical word and raw contacts remain reusable inputs for later
independent requested P comparisons; no canonical period is reconstructed.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
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

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basisIndex : Fin 1}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
    {original : LiftedPuncturedGrid base} {patchCount : Nat}
    {patches : List (ContinuedNeighborhood (Fibre.frameCurve frame).polynomial patchCount)}
    {clearance : BranchCellBank.ClearancePreparation base.bank.toBranchCellBank patches}
    {refined : ClearanceRefinement original clearance}
    {vertex : Fin original.vertices.count}
    (period : PeriodWalk base.bank.grid (original.vertices.coordinate vertex)
      (original.vertices.owner original.frames vertex) (standardDifferential basisIndex))
    (faces : PeriodFaces refined vertex period)
    (domains : FaceDomainBank refined.fine.frames refined.fineBase.faces.regulars)
    {count floor precision rootStage : Nat}
    {inputCenters : Centers (frame := frame) (basis := standardDifferential basisIndex)
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

namespace GridWord

include period domains data canonical supplied pieces in
/-- The literal same-fine vertex/source point factory includes every actual analytic endpoint. -/
theorem points_mem
    {entries : SplitSheets domains pieces.regular pieces.request.requests} {points : List Canonical}
    (pointFactory : points = List.ofFn refined.fine.vertices.coordinate ++
      (RegularPrimitiveSplits.SheetEntries.points entries ++ extras)) :
    ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points := by
  intro value member
  rewrite [pointFactory]
  exact List.mem_append_right _ (List.mem_append_left _ member)

/-- The exact original geometry, source observations, occurrences and fine-grid owners of a child word. -/
@[expose] def Inputs : Type _ :=
  (Materialized.Geometry (count := count) diameter positive period.closed.traced.lineage
        inputCenters materialized factory ×
      CellEndpoints.Targets childChain.path precision ×
      Sources (count := count) (floor := floor) (targets := targets) data ×
      Sources.Occurrences (count := count) (floor := floor)
        (original.vertices.owner original.frames vertex) period.closed data childChain
        precision rootStage targets computed sourceBank walkPositive ×
      Fragments (framed := refined.fineBase) (original.vertices.owner original.frames vertex)
        period data canonical (original.vertices.coordinate_onGrid vertex) refined.included supplied ×
      PeriodFaces refined vertex period × FaceDomainBank refined.fine.frames refined.fineBase.faces.regulars ×
      CenteredPathChain data.parents (start := (⟨original.vertices.coordinate vertex, 0⟩ : LiftedPoint 2))
        (finish := (⟨original.vertices.coordinate vertex, 0⟩ : LiftedPoint 2)))

/-- The independent counts, stages and allocation data retained by a child-word acquisition. -/
@[expose] def Allocation : Type :=
  (Nat × Nat × Nat × Nat × Rational × Rational × Nat × Rational × Rational × List Canonical)

end GridWord

/-- The exact retained input and execution payload of a canonical child word. -/
@[expose] def GridWord.InputCache : Type _ :=
  {value : GridWord.Inputs (period := period) (data := data) (canonical := canonical)
      (childChain := childChain) (supplied := supplied) × GridWord.Allocation //
    value = ((data, targets, sourceBank, completed, pieces, faces, domains, childChain),
      (count, floor, precision, rootStage, requestTarget, oldTolerance, oldMinimum,
        routeTarget, chartTarget, extras))}

/-- The actual signed root cache supplied by the retained occurrence completion. -/
@[expose] def GridWord.RootCache : Type _ :=
  {value : RootChain data.parents
      (ownerName (original.vertices.owner original.frames vertex))
      (ownerName (original.vertices.owner original.frames vertex)) // value = completed.2.1.val}

/-- Read the same signed root chain without unfolding the occurrence-completion owner. -/
@[expose] def GridWord.RootCache.roots
    (kept : GridWord.RootCache (period := period) (data := data)
      (childChain := childChain) (completed := completed)) :
    RootChain data.parents (ownerName (original.vertices.owner original.frames vertex))
      (ownerName (original.vertices.owner original.frames vertex)) := kept.val

/-- The exact original numerical and word execution on the supplied signed roots. -/
@[expose] def GridWord.Execution
    (roots : RootChain data.parents
      (ownerName (original.vertices.owner original.frames vertex))
      (ownerName (original.vertices.owner original.frames vertex))) : Type _ :=
  Σ entries : {value : SplitSheets domains pieces.regular pieces.request.requests //
    value = SplitSheets.build domains pieces.regular pieces.request.requests},
  Σ childPoints : {value : List Canonical //
    value = RegularPrimitiveSplits.SheetEntries.points entries.val},
  Σ points : {value : List Canonical // value = List.ofFn refined.fine.vertices.coordinate ++
    (childPoints.val ++ extras)},
  Σ budgets : {value : FaceMeshBudgets (standardDifferential basisIndex) points.val oldTolerance domains //
    value = FaceMeshBudgets.build (standardDifferential basisIndex) points.val oldTolerance oldPositive domains},
  Σ stage : {value : Nat // value = max oldMinimum budgets.val.index},
  Σ primitives : {value : FacePrimitiveBank (standardDifferential basisIndex) stage.val domains //
    value = FacePrimitiveBank.build (standardDifferential basisIndex) stage.val domains},
  Σ reference : {value : FaceSharedMeshes.Acquisition budgets.val primitives.val
      ((Data.Nat.Order.le_max_right _ _).trans_eq stage.property.symm) //
    value = FaceSharedMeshes.acquire budgets.val primitives.val
      ((Data.Nat.Order.le_max_right _ _).trans_eq stage.property.symm)},
  Σ sources : {value : SourceSpine refined.fine.mesh entries.val //
    value = SourceSpine.build refined.fine.mesh entries.val},
  Σ rooted : {value : Rooted entries.val refined.fine.mesh (original.vertices.coordinate vertex)
      (ownerName (original.vertices.owner original.frames vertex)) (original.vertices.coordinate vertex)
      (ownerName (original.vertices.owner original.frames vertex)) //
    value = Rooted.build sources.val
      (RootedWords.ParentCoordinates.ofSwitched (SwitchedPathChain.ofCenteredPathChain childChain))
      roots},
  Σ _word : {value : SplitSheets.Closed reference.val.shared entries.val childChain roots
      (GridWord.points_mem (period := period) (domains := domains) (data := data) (canonical := canonical)
        (supplied := supplied) (pieces := pieces) (extras := extras)
        (points.property.trans (congrArg (fun actual => List.ofFn refined.fine.vertices.coordinate ++
          (actual ++ extras)) childPoints.property))) //
    value = SplitSheets.closedWord reference.val.shared entries.val childChain roots
      (GridWord.points_mem (period := period) (domains := domains) (data := data) (canonical := canonical)
        (supplied := supplied) (pieces := pieces) (extras := extras)
        (points.property.trans (congrArg (fun actual => List.ofFn refined.fine.vertices.coordinate ++
          (actual ++ extras)) childPoints.property)))},
  Σ _routing : {value : RouteRequest rooted.val.pieces routeTarget //
    value = RouteRequest.build rooted.val.pieces canonicalRoute routeTarget routePositive},
  {_charts : RouteChartRequest faces.view.geometry.routeSpine (standardDifferential basisIndex) domains chartTarget //
    _charts = RouteChartRequest.build faces.view.geometry.routeSpine (standardDifferential basisIndex)
      domains chartTarget chartPositive}

attribute [local irreducible] GridWord.InputCache GridWord.RootCache GridWord.Execution
  GridWord.Inputs GridWord.Allocation in
set_option genInjectivity false in
/-- One actual child-source grid word and its original point-bank execution.

The complete given source and occurrence inputs, their signed root cache
and the actual numerical execution stay separate retained fields. The
execution is indexed by those same roots and keeps every original factory;
no geometry, root or source producer is replayed to recover an input.
-/
structure GridWord : Type _ where
  /-- The complete supplied source, occurrence, geometric and allocation data with their whole identity. -/
  inputCache : GridWord.InputCache
    (period := period) (faces := faces) (domains := domains) (data := data) (canonical := canonical)
    (childChain := childChain) (completed := completed) (supplied := supplied) (pieces := pieces)
    (oldTolerance := oldTolerance) (oldMinimum := oldMinimum)
    (routeTarget := routeTarget) (chartTarget := chartTarget) (extras := extras)
  /-- The same complete signed root cache read from the original occurrence completion. -/
  rootData : GridWord.RootCache (period := period) (data := data)
    (childChain := childChain) (completed := completed)
  /-- The original one-bank and ordered-word execution on this exact retained root cache. -/
  execution : GridWord.Execution
    (period := period) (faces := faces) (domains := domains) (data := data) (canonical := canonical)
    (childChain := childChain) (supplied := supplied) (pieces := pieces)
    (oldTolerance := oldTolerance) (oldPositive := oldPositive) (oldMinimum := oldMinimum)
    (routeTarget := routeTarget) (chartTarget := chartTarget)
    (routePositive := routePositive) (chartPositive := chartPositive) (extras := extras) rootData.roots

attribute [local irreducible] GridWord.InputCache GridWord.Execution
  GridWord.Inputs GridWord.Allocation in
constructive_injectivity GridWord

/-- Construct the actual old reference word from GIVEN canonical geometry, completion and fragment caches.

Incoming sheets are acquired before the literal point list is chosen.
Budgets and stage precede one primitive/shared bank, then the original
lifted/rooted/physical/contact constructors run once. The old reference
bank remains reusable for independent subsequent requested P comparisons.
-/
def fromFragments
    (targetCache : {value : CellEndpoints.Targets childChain.path precision // value = targets})
    (bankCache : {value : Sources (count := count) (floor := floor) (targets := targets) data // value = sourceBank}) :
    GridWord period faces domains data canonical childChain completed supplied pieces
    oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras := by
  let rootCache : {value : RootChain data.parents
      (ownerName (original.vertices.owner original.frames vertex))
      (ownerName (original.vertices.owner original.frames vertex)) // value = completed.2.1.val} :=
    ⟨completed.2.1.val, rfl⟩
  let entries : {value : SplitSheets domains pieces.regular pieces.request.requests //
      value = SplitSheets.build domains pieces.regular pieces.request.requests} :=
    ⟨SplitSheets.build domains pieces.regular pieces.request.requests, rfl⟩
  let childPoints : {value : List Canonical //
      value = RegularPrimitiveSplits.SheetEntries.points entries.val} :=
    ⟨RegularPrimitiveSplits.SheetEntries.points entries.val, rfl⟩
  let points : {value : List Canonical // value = List.ofFn refined.fine.vertices.coordinate ++
      (childPoints.val ++ extras)} := ⟨List.ofFn refined.fine.vertices.coordinate ++ (childPoints.val ++ extras), rfl⟩
  have pointsFactory : points.val = List.ofFn refined.fine.vertices.coordinate ++
      (RegularPrimitiveSplits.SheetEntries.points entries.val ++ extras) :=
    points.property.trans (congrArg (fun actual => List.ofFn refined.fine.vertices.coordinate ++ (actual ++ extras))
      childPoints.property)
  have included := GridWord.points_mem (period := period) (domains := domains) (data := data) (canonical := canonical)
        (supplied := supplied) (pieces := pieces) (extras := extras)
    pointsFactory
  let budgets : {value : FaceMeshBudgets (standardDifferential basisIndex) points.val oldTolerance domains //
      value = FaceMeshBudgets.build (standardDifferential basisIndex) points.val oldTolerance oldPositive domains} :=
    ⟨FaceMeshBudgets.build (standardDifferential basisIndex) points.val oldTolerance oldPositive domains, rfl⟩
  let stage : {value : Nat // value = max oldMinimum budgets.val.index} :=
    ⟨max oldMinimum budgets.val.index, rfl⟩
  let primitives : {value : FacePrimitiveBank (standardDifferential basisIndex) stage.val domains //
      value = FacePrimitiveBank.build (standardDifferential basisIndex) stage.val domains} :=
    ⟨FacePrimitiveBank.build (standardDifferential basisIndex) stage.val domains, rfl⟩
  have later : budgets.val.index ≤ stage.val := (Data.Nat.Order.le_max_right _ _).trans_eq stage.property.symm
  let reference : {value : FaceSharedMeshes.Acquisition budgets.val primitives.val later //
      value = FaceSharedMeshes.acquire budgets.val primitives.val later} :=
    ⟨FaceSharedMeshes.acquire budgets.val primitives.val later, rfl⟩
  let sources : {value : SourceSpine refined.fine.mesh entries.val //
      value = SourceSpine.build refined.fine.mesh entries.val} :=
    ⟨SourceSpine.build refined.fine.mesh entries.val, rfl⟩
  let coordinates := RootedWords.ParentCoordinates.ofSwitched (SwitchedPathChain.ofCenteredPathChain childChain)
  let rooted : {value : Rooted entries.val refined.fine.mesh (original.vertices.coordinate vertex)
      (ownerName (original.vertices.owner original.frames vertex)) (original.vertices.coordinate vertex)
      (ownerName (original.vertices.owner original.frames vertex)) //
      value = Rooted.build sources.val coordinates rootCache.val} :=
    ⟨Rooted.build sources.val coordinates rootCache.val, rfl⟩
  let word : {value : SplitSheets.Closed reference.val.shared entries.val childChain rootCache.val included //
      value = SplitSheets.closedWord reference.val.shared entries.val childChain rootCache.val included} :=
    ⟨SplitSheets.closedWord reference.val.shared entries.val childChain rootCache.val included, rfl⟩
  let routing : {value : RouteRequest rooted.val.pieces routeTarget //
      value = RouteRequest.build rooted.val.pieces canonicalRoute routeTarget routePositive} :=
    ⟨RouteRequest.build rooted.val.pieces canonicalRoute routeTarget routePositive, rfl⟩
  let charts : {value : RouteChartRequest faces.view.geometry.routeSpine (standardDifferential basisIndex)
      domains chartTarget // value = RouteChartRequest.build faces.view.geometry.routeSpine
        (standardDifferential basisIndex) domains chartTarget chartPositive} :=
    ⟨RouteChartRequest.build faces.view.geometry.routeSpine (standardDifferential basisIndex)
      domains chartTarget chartPositive, rfl⟩
  have metadata :
      ((data, targetCache.val, bankCache.val, completed, pieces, faces, domains, childChain),
        (count, floor, precision, rootStage, requestTarget, oldTolerance, oldMinimum,
          routeTarget, chartTarget, extras)) =
      ((data, targets, sourceBank, completed, pieces, faces, domains, childChain),
        (count, floor, precision, rootStage, requestTarget, oldTolerance, oldMinimum,
          routeTarget, chartTarget, extras)) := by
    have targetStep := congrArg (fun actual : CellEndpoints.Targets childChain.path precision =>
      ((data, actual, bankCache.val, completed, pieces, faces, domains, childChain),
        (count, floor, precision, rootStage, requestTarget, oldTolerance, oldMinimum,
          routeTarget, chartTarget, extras)))
      targetCache.property
    have bankStep := congrArg (fun actual : Sources (count := count) (floor := floor) (targets := targets) data =>
      ((data, targets, actual, completed, pieces, faces, domains, childChain),
        (count, floor, precision, rootStage, requestTarget, oldTolerance, oldMinimum,
          routeTarget, chartTarget, extras)))
      bankCache.property
    exact targetStep.trans bankStep
  exact
    { inputCache := ⟨((data, targetCache.val, bankCache.val, completed, pieces, faces, domains, childChain),
        (count, floor, precision, rootStage, requestTarget, oldTolerance, oldMinimum,
          routeTarget, chartTarget, extras)), metadata⟩
      rootData := rootCache
      execution := ⟨entries, childPoints, points, budgets, stage, primitives, reference,
        sources, rooted, word, routing, charts⟩ }

namespace GridWord

variable {period faces domains data canonical childChain completed supplied pieces
  oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras}
variable (kept : GridWord period faces domains data canonical childChain completed supplied pieces
  oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras)

/-- Read the complete given geometry/source/occurrence/fine-domain/chain/root inputs. -/
@[expose] def originals : Inputs (period := period) (data := data) (canonical := canonical)
    (childChain := childChain) (supplied := supplied) (refined := refined)
    (patchCount := patchCount) (patches := patches) (clearance := clearance)
    (floor := floor) (precision := precision) (rootStage := rootStage)
    (targets := targets) (computed := computed) (sourceBank := sourceBank) (walkPositive := walkPositive) :=
  kept.inputCache.val.1

/-- All original source completion and geometric/root inputs remain literal given values. -/
theorem originals_eq : kept.originals =
    (data, targets, sourceBank, completed, pieces, faces, domains, childChain) :=
  congrArg Prod.fst kept.inputCache.property

/-- Read the independent actual counts, source/occurrence stages and original reference/raw request parameters. -/
@[expose] def allocation : Allocation :=
  kept.inputCache.val.2

/-- The complete source/reference/request allocation data remains the literal supplied values. -/
theorem allocation_eq : kept.allocation =
    (count, floor, precision, rootStage, requestTarget, oldTolerance, oldMinimum,
          routeTarget, chartTarget, extras) :=
  congrArg Prod.snd kept.inputCache.property

/-- Read the complete given geometric acquisition from the retained input product. -/
@[expose] def geometryData : Materialized.Geometry (count := count) diameter positive
    period.closed.traced.lineage inputCenters materialized factory :=
  kept.originals.1

/-- The retained complete given geometric acquisition is the literal original input. -/
theorem geometryData_eq : kept.geometryData = data :=
  congrArg Prod.fst kept.originals_eq

/-- Read the actual given source Targets from the retained input product. -/
@[expose] def targetCache : CellEndpoints.Targets childChain.path precision :=
  kept.originals.2.1

/-- The retained actual given source Targets is the literal original input. -/
theorem targetCache_eq : kept.targetCache = targets :=
  congrArg Prod.fst (congrArg Prod.snd kept.originals_eq)

/-- Read the SAME given six-source numerical bank from the retained input product. -/
@[expose] def numericSources : Sources (count := count) (floor := floor) (targets := targets) data :=
  kept.originals.2.2.1

/-- The retained SAME given six-source numerical bank is the literal original input. -/
theorem numericSources_eq : kept.numericSources = sourceBank :=
  congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd kept.originals_eq))

/-- Read the complete original occurrence outcome from the retained input product. -/
@[expose] def occurrences : Sources.Occurrences (count := count) (floor := floor)
    (original.vertices.owner original.frames vertex) period.closed data childChain
    precision rootStage targets computed sourceBank walkPositive :=
  kept.originals.2.2.2.1

/-- The retained complete original occurrence outcome is the literal original input. -/
theorem occurrences_eq : kept.occurrences = completed :=
  congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd kept.originals_eq)))

/-- Read the given original primitive-fragment cache from the retained input product. -/
@[expose] def fragmentData : Fragments (framed := refined.fineBase)
    (original.vertices.owner original.frames vertex) period data canonical
    (original.vertices.coordinate_onGrid vertex) refined.included supplied :=
  kept.originals.2.2.2.2.1

/-- The retained given original primitive-fragment cache is the literal original input. -/
theorem fragmentData_eq : kept.fragmentData = pieces :=
  congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd kept.originals_eq))))

/-- Read the given whole original period-frame face cache from the retained input product. -/
@[expose] def periodView : PeriodFaces refined vertex period :=
  kept.originals.2.2.2.2.2.1

/-- The retained given whole original period-frame face cache is the literal original input. -/
theorem periodView_eq : kept.periodView = faces :=
  congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd
    (congrArg Prod.snd (congrArg Prod.snd kept.originals_eq)))))

/-- Read the SAME actual fine-grid domain bank from the retained input product. -/
@[expose] def domainBank : FaceDomainBank refined.fine.frames refined.fineBase.faces.regulars :=
  kept.originals.2.2.2.2.2.2.1

/-- The retained SAME actual fine-grid domain bank is the literal original input. -/
theorem domainBank_eq : kept.domainBank = domains :=
  congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd
    (congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd kept.originals_eq))))))

/-- Read the original given centered child chain from the retained input product. -/
@[expose] def geometryChain : CenteredPathChain data.parents
    (start := (⟨original.vertices.coordinate vertex, 0⟩ : LiftedPoint 2))
    (finish := (⟨original.vertices.coordinate vertex, 0⟩ : LiftedPoint 2)) :=
  kept.originals.2.2.2.2.2.2.2

/-- The retained original given centered child chain is the literal original input. -/
theorem geometryChain_eq : kept.geometryChain = childChain :=
  congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd
    (congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd kept.originals_eq))))))

/-- Read the SAME retained signed root cache, bound before the dependent word fields. -/
@[expose] def rootCache : {value : RootChain data.parents
    (ownerName (original.vertices.owner original.frames vertex))
    (ownerName (original.vertices.owner original.frames vertex)) // value = completed.2.1.val} :=
  kept.rootData

/-- The retained root cache is exactly the given source completion's actual root value. -/
theorem rootCache_eq : kept.rootCache.val = completed.2.1.val := kept.rootData.property

/-- The original whole signed root factory is retained only as a proof, never executed to recover roots. -/
theorem rootCache_factory : kept.rootCache.val =
    Materialized.Geometry.closedRoots (original.vertices.owner original.frames vertex) period.closed data :=
  kept.rootCache_eq.trans completed.2.1.property

/-- Read the actual fragment sheet bank without repeating Point, Entry or query acquisition. -/
@[expose] def entries : SplitSheets domains pieces.regular pieces.request.requests :=
  kept.execution.1.val

/-- The retained sheets have their one original producer on the given regular fragments and requests. -/
theorem entries_eq : kept.entries = SplitSheets.build domains pieces.regular pieces.request.requests :=
  kept.execution.1.property

/-- Read the retained whole actual source endpoint list. -/
@[expose] def childPoints : List Canonical := kept.execution.2.1.val

/-- The source endpoint list is exactly the original retained sheet-bank point operation. -/
theorem childPoints_eq : kept.childPoints = RegularPrimitiveSplits.SheetEntries.points kept.entries :=
  kept.execution.2.1.property

/-- Read the SAME literal point choice made before the original reference bank. -/
@[expose] def points : List Canonical := kept.execution.2.2.1.val

/-- The actual point factory contains both SAME-fine vertices and every original analytic source endpoint. -/
theorem points_eq : kept.points = List.ofFn refined.fine.vertices.coordinate ++
    (RegularPrimitiveSplits.SheetEntries.points kept.entries ++ extras) :=
  kept.execution.2.2.1.property.trans
    (congrArg (fun actual => List.ofFn refined.fine.vertices.coordinate ++ (actual ++ extras)) kept.childPoints_eq)

/-- Every actual analytic endpoint belongs to the same retained old numerical point bank. -/
theorem child_mem : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points kept.entries,
    value ∈ kept.points := points_mem (period := period) (domains := domains) (data := data) (canonical := canonical)
      (supplied := supplied) (pieces := pieces) (extras := extras) kept.points_eq

/-- Read the original reference mesh budgets selected on those exact points. -/
@[expose] def budgets : FaceMeshBudgets (standardDifferential basisIndex) kept.points oldTolerance domains :=
  kept.execution.2.2.2.1.val

/-- Read the original reference numerical stage chosen before its primitive bank. -/
@[expose] def stage : Nat := kept.execution.2.2.2.2.1.val

/-- The numerical stage was chosen from the independent supplied floor and actual point-budget index. -/
theorem stage_eq : kept.stage = max oldMinimum kept.budgets.index := kept.execution.2.2.2.2.1.property

/-- The original numerical stage is sufficient for the actual retained reference mesh requests. -/
theorem later : kept.budgets.index ≤ kept.stage :=
  (Data.Nat.Order.le_max_right _ _).trans_eq kept.stage_eq.symm

/-- Read the one actual original reference primitive bank. -/
@[expose] def primitives : FacePrimitiveBank (standardDifferential basisIndex) kept.stage domains :=
  kept.execution.2.2.2.2.2.1.val

/-- Read the retained original numerical execution and its whole inputs/factory. -/
@[expose] def reference : FaceSharedMeshes.Acquisition kept.budgets kept.primitives kept.later :=
  kept.execution.2.2.2.2.2.2.1.val

/-- Read the one actual lifted source spine on the supplied fine mesh and sheets. -/
@[expose] def liftedSources : SourceSpine refined.fine.mesh kept.entries :=
  kept.execution.2.2.2.2.2.2.2.1.val

/-- Read the original once-flattened rooted word on the SAME source, chain and root data. -/
@[expose] def rooted : Rooted kept.entries refined.fine.mesh (original.vertices.coordinate vertex)
    (ownerName (original.vertices.owner original.frames vertex)) (original.vertices.coordinate vertex)
    (ownerName (original.vertices.owner original.frames vertex)) :=
  kept.execution.2.2.2.2.2.2.2.2.1.val

/-- Read the actual closed physical/numerical word, including every ordered closing gap. -/
@[expose] def word : SplitSheets.Closed kept.reference.shared kept.entries childChain kept.rootCache.val
    kept.child_mem :=
  kept.execution.2.2.2.2.2.2.2.2.2.1.val

/-- Read the first genuine canonical raw route request with all contact geometry retained. -/
@[expose] def routing : RouteRequest kept.rooted.pieces routeTarget :=
  kept.execution.2.2.2.2.2.2.2.2.2.2.1.val

/-- Read the actual original chart contacts on the same period-face route spine. -/
@[expose] def charts : RouteChartRequest faces.view.geometry.routeSpine
    (standardDifferential basisIndex) domains chartTarget :=
  kept.execution.2.2.2.2.2.2.2.2.2.2.2.val

include kept canonical in
/-- The actual source directed refinement supplies this SAME canonical period's parent grouping. -/
theorem source_path : PathSources 0 period.closed.walk.path data.parents := by
  have actual := Materialized.Geometry.periodSources
    (original.vertices.owner original.frames vertex) period kept.geometryData canonical
  have parentsEq := congrArg Materialized.Geometry.parents kept.geometryData_eq
  exact Eq.mp (congrArg (PathSources 0 period.closed.walk.path) parentsEq) actual

/-- Every SAME-fine vertex belongs to that actual point bank by its original literal factory. -/
theorem vertex_mem (vertex : Fin refined.fine.vertices.count) : refined.fine.vertices.coordinate vertex ∈ kept.points :=
  FaceSharedMeshes.Acquisition.vertices_mem (bank := refined.fineBase.bank.toBranchCellBank) refined.fine.vertices []
    (RegularPrimitiveSplits.SheetEntries.points kept.entries ++ extras) kept.points_eq vertex

/-- The retained raw route request has its actual whole canonical-builder identity. -/
theorem routing_eq : kept.routing = RouteRequest.build kept.rooted.pieces canonicalRoute routeTarget
    kept.routing.positive := kept.execution.2.2.2.2.2.2.2.2.2.2.1.property

/-- The actual old reference budgets have their original literal same-points constructor. -/
theorem budgets_eq : kept.budgets = FaceMeshBudgets.build (standardDifferential basisIndex) kept.points
    oldTolerance oldPositive domains := kept.execution.2.2.2.1.property

/-- The old primitive bank retains its single actual constructor on the SAME domains. -/
theorem primitives_eq : kept.primitives = FacePrimitiveBank.build (standardDifferential basisIndex) kept.stage
    domains := kept.execution.2.2.2.2.2.1.property

/-- The complete old numerical execution retains its one original shared-worker factory. -/
theorem reference_eq : kept.reference = FaceSharedMeshes.acquire kept.budgets kept.primitives kept.later :=
  kept.execution.2.2.2.2.2.2.1.property

/-- The original lifted-source placement has its whole factory on the retained entries and fine mesh. -/
theorem liftedSources_eq : kept.liftedSources = SourceSpine.build refined.fine.mesh kept.entries :=
  kept.execution.2.2.2.2.2.2.2.1.property

/-- The flattened rooted word consumes exactly the retained source cache, GIVEN child chain and actual cached roots. -/
theorem rooted_eq : kept.rooted = Rooted.build kept.liftedSources
    (RootedWords.ParentCoordinates.ofSwitched (SwitchedPathChain.ofCenteredPathChain childChain)) kept.rootCache.val :=
  kept.execution.2.2.2.2.2.2.2.2.1.property

/-- The physical/numerical closed word retains its one original constructor, including its literal closing cache. -/
theorem word_eq : kept.word = SplitSheets.closedWord kept.reference.shared kept.entries childChain kept.rootCache.val
    kept.child_mem := kept.execution.2.2.2.2.2.2.2.2.2.1.property

/-- The original chart contacts retain their single whole preparation factory. -/
theorem charts_eq : kept.charts = RouteChartRequest.build faces.view.geometry.routeSpine
    (standardDifferential basisIndex) domains chartTarget chartPositive := kept.execution.2.2.2.2.2.2.2.2.2.2.2.property

section Payment

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Data.Vector (DependentVector)
open Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement
open Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.PairCoordinates
open Purelib.Topology.Polygon.Stokes (triangleEdgeOccurrences)
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes (BoundaryCycleDecomposition)

variable {oldBank : BasedBranchBank original} {newBank : BasedBranchBank refined.fine}
    {oldSheet annulusSheet stripSheet freshSheet : Fin 2}
    {ordered : BasedBranchBank.Ordered oldBank oldSheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    {periods : Paired.PeriodPrograms.Prepared paired}
    {annuli : DependentVector (fun index : BranchIsolation.Data.Index branches =>
      {value : refined.Annulus index annulusSheet // value = refined.annulus index annulusSheet})}
    {strips : DependentVector (fun index : BranchIsolation.Data.Index branches =>
      {value : refined.StemStrip oldBank newBank (annuli.get index).val stripSheet //
        value = refined.stemStrip oldBank newBank (annuli.get index).val stripSheet})}
    {source : refined.PairCompilation oldBank newBank periods annuli strips basisIndex}
    {freshOrdered : BasedBranchBank.Ordered newBank freshSheet}
    {freshPaired : OrderedBranchPairs.Ordered.Paired freshOrdered}
    {fresh : Paired.PeriodPrograms.Prepared freshPaired} {freshBasis : fresh.GeometricBasis}
    {boundary : BoundaryCycleDecomposition (triangleEdgeOccurrences refined.fine.mesh.triangulation.faces)}
    {boundaryFactory : boundary = refined.fine.boundaryComponents}
    (coordinates : PairCoordinates source freshBasis boundary boundaryFactory)
    (minimum : Nat) (polynomial : Ordinary (Fibre.frameCurve frame).polynomial)
    (wordTarget cochainTarget : Rational) (wordPositive : 0 < wordTarget) (cochainPositive : 0 < cochainTarget)
    (minimumFloor modelStage : Nat)

/-- The full given child acquisition and one actual P comparison, both retained with their whole identities.

The source completion, independent old observations and geometric/root
owners remain available in the actual output, alongside the new model,
primitive/triangle and cochain caches. No nominal source owner is replaced.
-/
@[expose] def CanonicalComparison : Type _ :=
  (Σ acquired : {value : GridWord period faces domains data canonical childChain completed supplied pieces
      oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras // value = kept},
  {value : ComparisonRequests.CanonicalPreparation
    (coordinates := coordinates) (domains := domains) (minimum := minimum) (reference := acquired.val.reference)
    (pointPrefix := []) (extraPoints := extras) (sourceSheet := 0)
    (faces := faces) (roots := acquired.val.rootCache.val)
    (word := acquired.val.word) (rooted := acquired.val.rooted) (routing := acquired.val.routing)
      (charts := acquired.val.charts)
    (polynomial := polynomial) (wordTarget := wordTarget) (cochainTarget := cochainTarget)
    (wordPositive := wordPositive) (cochainPositive := cochainPositive)
    (minimumFloor := minimumFloor) (modelStage := modelStage) //
    value = ComparisonRequests.prepareCanonical
    (coordinates := coordinates) (domains := domains) (minimum := minimum) (reference := acquired.val.reference)
    (pointPrefix := []) (extraPoints := extras) (pointFactory := acquired.val.points_eq)
    (faces := faces) (roots := acquired.val.rootCache.val) (ancestry := acquired.val.source_path)
    (word := acquired.val.word) (rooted := acquired.val.rooted) (routing := acquired.val.routing)
      (routingFactory := acquired.val.routing_eq)
    (charts := acquired.val.charts) (polynomial := polynomial) (wordTarget := wordTarget)
      (cochainTarget := cochainTarget)
    (wordPositive := wordPositive) (cochainPositive := cochainPositive)
    (minimumFloor := minimumFloor) (modelStage := modelStage)})

/-- Feed the SAME retained old grid word/reference bank to one actual requested full-numerator cochain preparation.

The complete given source geometry, completion and original raw contacts
are read from the retained acquisition. Its literal point choice and
actual periodSources certificate supply the two genuine couplings. No
old reference bank, fragment, Rooted word, source bank or root factory is
replayed; only the original one-bank requested-P pipeline executes.
-/
def prepareCanonical : CanonicalComparison kept coordinates minimum polynomial wordTarget cochainTarget
    wordPositive cochainPositive minimumFloor modelStage :=
  let acquired : {value : GridWord period faces domains data canonical childChain completed supplied pieces
      oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras //
      value = kept} := ⟨kept, rfl⟩
  let compared : {value : ComparisonRequests.CanonicalPreparation
    (coordinates := coordinates) (domains := domains) (minimum := minimum) (reference := acquired.val.reference)
    (pointPrefix := []) (extraPoints := extras) (sourceSheet := 0)
    (faces := faces) (roots := acquired.val.rootCache.val)
    (word := acquired.val.word) (rooted := acquired.val.rooted) (routing := acquired.val.routing)
      (charts := acquired.val.charts)
    (polynomial := polynomial) (wordTarget := wordTarget) (cochainTarget := cochainTarget)
    (wordPositive := wordPositive) (cochainPositive := cochainPositive)
    (minimumFloor := minimumFloor) (modelStage := modelStage) //
      value = ComparisonRequests.prepareCanonical
    (coordinates := coordinates) (domains := domains) (minimum := minimum) (reference := acquired.val.reference)
    (pointPrefix := []) (extraPoints := extras) (pointFactory := acquired.val.points_eq)
    (faces := faces) (roots := acquired.val.rootCache.val) (ancestry := acquired.val.source_path)
    (word := acquired.val.word) (rooted := acquired.val.rooted) (routing := acquired.val.routing)
      (routingFactory := acquired.val.routing_eq)
    (charts := acquired.val.charts) (polynomial := polynomial) (wordTarget := wordTarget)
      (cochainTarget := cochainTarget)
    (wordPositive := wordPositive) (cochainPositive := cochainPositive)
    (minimumFloor := minimumFloor) (modelStage := modelStage)} :=
    ⟨ComparisonRequests.prepareCanonical
    (coordinates := coordinates) (domains := domains) (minimum := minimum) (reference := acquired.val.reference)
    (pointPrefix := []) (extraPoints := extras) (pointFactory := acquired.val.points_eq)
    (faces := faces) (roots := acquired.val.rootCache.val) (ancestry := acquired.val.source_path)
    (word := acquired.val.word) (rooted := acquired.val.rooted) (routing := acquired.val.routing)
      (routingFactory := acquired.val.routing_eq)
    (charts := acquired.val.charts) (polynomial := polynomial) (wordTarget := wordTarget)
      (cochainTarget := cochainTarget)
    (wordPositive := wordPositive) (cochainPositive := cochainPositive)
    (minimumFloor := minimumFloor) (modelStage := modelStage), rfl⟩
  ⟨acquired, compared⟩

namespace CanonicalComparison

variable {kept coordinates minimum polynomial wordTarget cochainTarget
  wordPositive cochainPositive minimumFloor modelStage}
variable (paid : CanonicalComparison kept coordinates minimum polynomial wordTarget cochainTarget
  wordPositive cochainPositive minimumFloor modelStage)

/-- Read the SAME complete original source completion, reference bank and physical word acquisition. -/
@[expose] def inputWord : GridWord period faces domains data canonical childChain completed supplied pieces
    oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras :=
  paid.1.val

/-- The retained whole original child acquisition is the literal given input. -/
theorem inputWord_eq : paid.inputWord = kept := paid.1.property

/-- Read the one actual requested numerical comparison and its internally derived model/cochain bounds. -/
@[expose] def compared : ComparisonRequests.CanonicalPreparation
    (coordinates := coordinates) (domains := domains) (minimum := minimum) (reference := paid.inputWord.reference)
    (pointPrefix := []) (extraPoints := extras) (sourceSheet := 0)
    (faces := faces) (roots := paid.inputWord.rootCache.val)
    (word := paid.inputWord.word) (rooted := paid.inputWord.rooted) (routing := paid.inputWord.routing)
      (charts := paid.inputWord.charts)
    (polynomial := polynomial) (wordTarget := wordTarget) (cochainTarget := cochainTarget)
    (wordPositive := wordPositive) (cochainPositive := cochainPositive)
    (minimumFloor := minimumFloor) (modelStage := modelStage) :=
  paid.2.val

/-- The new comparison retains its original one-pipeline factory on the SAME complete old acquisition. -/
theorem compared_eq : paid.compared = ComparisonRequests.prepareCanonical
    (coordinates := coordinates) (domains := domains) (minimum := minimum) (reference := paid.inputWord.reference)
    (pointPrefix := []) (extraPoints := extras) (pointFactory := paid.inputWord.points_eq)
    (faces := faces) (roots := paid.inputWord.rootCache.val) (ancestry := paid.inputWord.source_path)
    (word := paid.inputWord.word) (rooted := paid.inputWord.rooted) (routing := paid.inputWord.routing)
      (routingFactory := paid.inputWord.routing_eq)
    (charts := paid.inputWord.charts) (polynomial := polynomial) (wordTarget := wordTarget)
      (cochainTarget := cochainTarget)
    (wordPositive := wordPositive) (cochainPositive := cochainPositive)
    (minimumFloor := minimumFloor) (modelStage := modelStage) := paid.2.property

section Factories

/-- The certified lower preparation on the literal retained word, with its complete original factory. -/
@[expose] def Preparation : Type _ :=
  {value : ComparisonRequests.CanonicalPreparation
    (coordinates := coordinates) (domains := domains) (minimum := minimum) (reference := kept.reference)
    (pointPrefix := []) (extraPoints := extras) (sourceSheet := 0)
    (faces := faces) (roots := kept.rootCache.val)
    (word := kept.word) (rooted := kept.rooted) (routing := kept.routing)
      (charts := kept.charts)
    (polynomial := polynomial) (wordTarget := wordTarget) (cochainTarget := cochainTarget)
    (wordPositive := wordPositive) (cochainPositive := cochainPositive)
    (minimumFloor := minimumFloor) (modelStage := modelStage) //
      value = ComparisonRequests.prepareCanonical
    (coordinates := coordinates) (domains := domains) (minimum := minimum) (reference := kept.reference)
    (pointPrefix := []) (extraPoints := extras) (pointFactory := kept.points_eq)
    (faces := faces) (roots := kept.rootCache.val) (ancestry := kept.source_path)
    (word := kept.word) (rooted := kept.rooted) (routing := kept.routing)
      (routingFactory := kept.routing_eq)
    (charts := kept.charts) (polynomial := polynomial) (wordTarget := wordTarget)
      (cochainTarget := cochainTarget)
    (wordPositive := wordPositive) (cochainPositive := cochainPositive)
    (minimumFloor := minimumFloor) (modelStage := modelStage)}

/-- Retain a given certified lower preparation in the original whole-word comparison cache.

The literal given word and complete lower preparation are packed once.
Its original factory derives the upper constructor identity in an erased
proof; no lower preparation or word acquisition is executed again.
-/
@[expose] def fromPreparation
    (prepared : Preparation (kept := kept) (coordinates := coordinates) (minimum := minimum) (polynomial := polynomial)
      (wordTarget := wordTarget) (cochainTarget := cochainTarget) (wordPositive := wordPositive)
      (cochainPositive := cochainPositive) (minimumFloor := minimumFloor) (modelStage := modelStage)) :
    {value : CanonicalComparison kept coordinates minimum polynomial wordTarget cochainTarget
        wordPositive cochainPositive minimumFloor modelStage //
      value = prepareCanonical kept coordinates minimum polynomial wordTarget cochainTarget
        wordPositive cochainPositive minimumFloor modelStage} :=
  let value : CanonicalComparison kept coordinates minimum polynomial wordTarget cochainTarget
      wordPositive cochainPositive minimumFloor modelStage :=
    ⟨⟨kept, rfl⟩, prepared⟩
  ⟨value, by
    rcases prepared with ⟨prepared, factory⟩
    cases factory
    rfl⟩

/-- The constructor reads triangle values from the same supplied complete lower preparation. -/
theorem fromPreparation_triangles
    (prepared : Preparation (kept := kept) (coordinates := coordinates) (minimum := minimum) (polynomial := polynomial)
      (wordTarget := wordTarget) (cochainTarget := cochainTarget) (wordPositive := wordPositive)
      (cochainPositive := cochainPositive) (minimumFloor := minimumFloor) (modelStage := modelStage)) :
    (fromPreparation prepared).val.compared.prepared.triangles.values =
      prepared.val.prepared.triangles.values := by
  unfold fromPreparation
  rfl

end Factories

end CanonicalComparison

end Payment

end GridWord

/-- Acquire one genuine primitive request on the existing covered children, then construct its old grid word once.

The actual request and fragment product are retained with their complete
original factories. This operation prepares no Geometry, source-bank,
occurrence completion, RootClosedWalk or canonical period. The returned
old reference word can be reused by independent requested P comparisons.
-/
def acquireGridWord
    (targetCache : {value : CellEndpoints.Targets childChain.path precision // value = targets})
    (bankCache : {value : Sources (count := count) (floor := floor) (targets := targets) data // value = sourceBank})
    (primitiveTarget : Rational) (primitivePositive : 0 < primitiveTarget) (primitiveMinimum : Nat) :
    (Σ acquired : {value : AcquiredFragments (framed := refined.fineBase)
        (original.vertices.owner original.frames vertex) period data canonical
        (original.vertices.coordinate_onGrid vertex) refined.included primitiveTarget
        primitivePositive primitiveMinimum //
      value = acquireFragments (framed := refined.fineBase)
        (original.vertices.owner original.frames vertex) period data canonical
        (original.vertices.coordinate_onGrid vertex) refined.included primitiveTarget
        primitivePositive primitiveMinimum},
    {value : GridWord period faces domains data canonical childChain completed
        acquired.val.request acquired.val.fragments
        oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras //
      value = fromFragments period faces domains data canonical childChain completed acquired.val.request
        acquired.val.fragments oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive
        extras targetCache bankCache}) :=
  let acquired : {value : AcquiredFragments (framed := refined.fineBase)
      (original.vertices.owner original.frames vertex) period data canonical
      (original.vertices.coordinate_onGrid vertex) refined.included primitiveTarget
        primitivePositive primitiveMinimum //
      value = acquireFragments (framed := refined.fineBase)
        (original.vertices.owner original.frames vertex) period data canonical
        (original.vertices.coordinate_onGrid vertex) refined.included primitiveTarget
        primitivePositive primitiveMinimum} :=
    ⟨acquireFragments (framed := refined.fineBase) (original.vertices.owner original.frames vertex)
      period data canonical (original.vertices.coordinate_onGrid vertex) refined.included primitiveTarget
      primitivePositive primitiveMinimum, rfl⟩
  let word : {value : GridWord period faces domains data canonical childChain completed acquired.val.request
      acquired.val.fragments oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive
      extras //
      value = fromFragments period faces domains data canonical childChain completed acquired.val.request
        acquired.val.fragments oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive
        extras targetCache bankCache} :=
    ⟨fromFragments period faces domains data canonical childChain completed acquired.val.request acquired.val.fragments
      oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
        targetCache bankCache, rfl⟩
  ⟨acquired, word⟩

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry
