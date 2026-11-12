module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Fragments.Canonical.Weighted
public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Fragments.Canonical.Programs
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Models
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Holomorphic
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity

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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.GeometricBasis
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Chain
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Fragments
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Fragments.Canonical.Periods
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Occurrences
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Polynomial.Preparation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
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
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

/-! # One original and two fresh source observations shared by both actual numerator comparisons

Both original model searches, primitive source/period floors and actual
caller minima select one common stage before the three real preparations.
The two fresh Targets caches and three source observations are retained
once. Both numerator consumers share the observations; the old target
rule retains its original separate callback semantics in each attachment.
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
    (requested : Rational)

variable {coordinates requested}

open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat.Fraction.Order
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Legendre.Periods.Jets.Source
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell renaming PreparedParents -> SourceParents

variable (kept : WeightedPoints period faces domains data canonical childChain completed
    oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
    targetCache bankCache primitiveTarget primitivePositive primitiveMinimum
    fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart coordinates requested)
    (internalTarget : Rational) (internalPositive : 0 < internalTarget)
    (sourcePrecision : Nat → Nat)
    (sourceTargets : (index : Nat) → {value : CellEndpoints.Targets childChain.path (sourcePrecision index) //
      value = CellEndpoints.Targets.build childChain.path (sourcePrecision index)})
    (sourceBanks : (index : Nat) → Sources (count := count) (floor := floor)
      (original := childChain.path) (stage := sourcePrecision index) (targets := (sourceTargets index).val) data)
    (precisionPaid : ∀ index, index ≤ sourcePrecision index)
    (programmeMinimum modelMinimum rightMinimum observedMinimum freshFloor : Nat)

/-- The actual weighted acquisition, fixed source rules and all independent public/requested source minima. -/
@[expose] def ProgrammeSources.Inputs : Type _ :=
  {value : WeightedPoints period faces domains data canonical childChain completed
      oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras
      targetCache bankCache primitiveTarget primitivePositive primitiveMinimum
      fresh aValues bValues aSourceStart aPeriodStart bSourceStart bPeriodStart coordinates requested ×
      (Nat → Nat) ×
      ((index : Nat) → {value : CellEndpoints.Targets childChain.path (sourcePrecision index) //
        value = CellEndpoints.Targets.build childChain.path (sourcePrecision index)}) ×
      ((index : Nat) → Sources (count := count) (floor := floor) (original := childChain.path)
        (stage := sourcePrecision index) (targets := (sourceTargets index).val) data) ×
      (Rational × Nat × Nat × Nat × Nat × Nat) //
    value = (kept, sourcePrecision, sourceTargets, sourceBanks,
      (internalTarget, programmeMinimum, modelMinimum, rightMinimum, observedMinimum, freshFloor)) ∧
      ∀ index, index ≤ sourcePrecision index}

/-- The two genuine original 128-mass model searches retain their complete whole selection factories. -/
@[expose] def ProgrammeSources.ModelSearches : Type _ :=
  {value : Search.Selection (128 * movementMass aValues.1.parents)
      (max rightMinimum (max modelMinimum observedMinimum)) kept.share //
    value = (PolynomialSpine.modelSelection aValues.1 rightMinimum modelMinimum observedMinimum
      kept.share kept.share_positive).val} ×
  {value : Search.Selection (128 * movementMass bValues.1.parents)
      (max rightMinimum (max modelMinimum observedMinimum)) kept.share //
    value = (PolynomialSpine.modelSelection bValues.1 rightMinimum modelMinimum observedMinimum
      kept.share kept.share_positive).val}

/-- The actual common minimum keeps every independent model, source-target and original period floor. -/
@[expose] def ProgrammeSources.raisedMinimum (searches : ProgrammeSources.ModelSearches kept modelMinimum
    rightMinimum observedMinimum) : Nat :=
  max modelMinimum (max searches.1.val.stage (max searches.2.val.stage
    (max observedMinimum (max kept.periodPoints.aSelection.2.1.val.stage
      (max kept.periodPoints.bSelection.2.1.val.stage
        (max kept.periodPoints.aSelection.2.2.val.stage kept.periodPoints.bSelection.2.2.val.stage))))))

/-- The coordinate-independent original source/model selection at that genuinely computed common minimum. -/
@[expose] def ProgrammeSources.Selection
    (searches : ProgrammeSources.ModelSearches kept modelMinimum rightMinimum observedMinimum) : Type _ :=
  ProgrammeComparison.SelectionCache (data := data) (requested := internalTarget)
    (positiveRequest := internalPositive) (programmeMinimum := programmeMinimum)
    (modelMinimum := ProgrammeSources.raisedMinimum kept modelMinimum rightMinimum observedMinimum searches)

/-- The ONE exact original six-channel observation at the common stage and original actual Targets indices. -/
@[expose] def ProgrammeSources.OldObserved
    (searches : ProgrammeSources.ModelSearches kept modelMinimum rightMinimum observedMinimum)
    (selected : ProgrammeSources.Selection kept internalTarget internalPositive programmeMinimum
      modelMinimum rightMinimum observedMinimum searches) : Type _ :=
  {value : Sources (count := count) (floor := floor) (original := childChain.path)
      (stage := sourcePrecision selected.selected.stage)
      (targets := (sourceTargets selected.selected.stage).val) data //
    value = sourceBanks selected.selected.stage}

/-- The same first original retained recast chain, transported as a whole to its actual primitive-request parents. -/
@[expose] def ProgrammeSources.AChain : Type _ :=
  {value : CenteredPathChain
      ((fresh.aWalk 0).initial.state.parents.map (recastCenteredEdge (standardDifferential (0 : Fin 1))))
      (start := (fresh.aWalk 0).initial.state.start) (finish := (fresh.aWalk 0).initial.state.start) //
    value = aValues.1.chain.castParents aValues.1.parents_eq}

/-- The same whole corrected-B retained recast chain under its original parent factory. -/
@[expose] def ProgrammeSources.BChain : Type _ :=
  {value : CenteredPathChain
      ((fresh.bWalk 0).initial.state.parents.map (recastCenteredEdge (standardDifferential (0 : Fin 1))))
      (start := (fresh.bWalk 0).initial.state.start) (finish := (fresh.bWalk 0).initial.state.start) //
    value = bValues.1.chain.castParents bValues.1.parents_eq}

/-- The original target cache on the first actual chain at the selected common source stage. -/
@[expose] def ProgrammeSources.ATargets
    (searches : ProgrammeSources.ModelSearches kept modelMinimum rightMinimum observedMinimum)
    (selected : ProgrammeSources.Selection kept internalTarget internalPositive programmeMinimum
      modelMinimum rightMinimum observedMinimum searches)
    (chain : ProgrammeSources.AChain (fresh := fresh) (aValues := aValues)) : Type _ :=
  {value : CellEndpoints.Targets chain.val.path selected.selected.stage //
    value = CellEndpoints.Targets.build chain.val.path selected.selected.stage}

/-- The original target cache on the second actual chain at the SAME independently selected source stage. -/
@[expose] def ProgrammeSources.BTargets
    (searches : ProgrammeSources.ModelSearches kept modelMinimum rightMinimum observedMinimum)
    (selected : ProgrammeSources.Selection kept internalTarget internalPositive programmeMinimum
      modelMinimum rightMinimum observedMinimum searches)
    (chain : ProgrammeSources.BChain (fresh := fresh) (bValues := bValues)) : Type _ :=
  {value : CellEndpoints.Targets chain.val.path selected.selected.stage //
    value = CellEndpoints.Targets.build chain.val.path selected.selected.stage}

/-- The actual first fresh six-channel source preparation, with its exact target and full original producer. -/
@[expose] def ProgrammeSources.AObserved
    (searches : ProgrammeSources.ModelSearches kept modelMinimum rightMinimum observedMinimum)
    (selected : ProgrammeSources.Selection kept internalTarget internalPositive programmeMinimum
      modelMinimum rightMinimum observedMinimum searches)
    (chain : ProgrammeSources.AChain (fresh := fresh) (aValues := aValues))
    (targets : ProgrammeSources.ATargets kept internalTarget internalPositive programmeMinimum modelMinimum
      rightMinimum observedMinimum searches selected chain) : Type _ :=
  {value : SourceParents (parameter := parameter) (frame := frame)
      kept.periodPoints.aSelection.1.val.requests.covered freshFloor targets.val //
    value = Cell.prepareCovered (parameter := parameter) (frame := frame)
      kept.periodPoints.aSelection.1.val.requests.covered freshFloor targets.val}

/-- The actual full second fresh source preparation on its own original cover, targets and coefficient floor. -/
@[expose] def ProgrammeSources.BObserved
    (searches : ProgrammeSources.ModelSearches kept modelMinimum rightMinimum observedMinimum)
    (selected : ProgrammeSources.Selection kept internalTarget internalPositive programmeMinimum
      modelMinimum rightMinimum observedMinimum searches)
    (chain : ProgrammeSources.BChain (fresh := fresh) (bValues := bValues))
    (targets : ProgrammeSources.BTargets kept internalTarget internalPositive programmeMinimum modelMinimum
      rightMinimum observedMinimum searches selected chain) : Type _ :=
  {value : SourceParents (parameter := parameter) (frame := frame)
      kept.periodPoints.bSelection.1.val.requests.covered freshFloor targets.val //
    value = Cell.prepareCovered (parameter := parameter) (frame := frame)
      kept.periodPoints.bSelection.1.val.requests.covered freshFloor targets.val}

attribute [local irreducible] ProgrammeSources.Inputs ProgrammeSources.ModelSearches ProgrammeSources.Selection
  ProgrammeSources.OldObserved ProgrammeSources.AChain ProgrammeSources.BChain ProgrammeSources.ATargets
  ProgrammeSources.BTargets ProgrammeSources.AObserved ProgrammeSources.BObserved in
set_option genInjectivity false in
/-- Retain one original and two fresh actual six-source observations for both genuine numerator comparisons.

The common stage is chosen before the three preparations from all actual
model/source/period floors. Every observation, chain and Targets value is
an original certified cache. Neither numerator consumer selects, prepares
or recovers these values again.
-/
structure ProgrammeSources : Type _ where
  /-- The complete weighted acquisition, fixed original rules and actual independent input floors. -/
  inputCache : ProgrammeSources.Inputs kept internalTarget sourcePrecision sourceTargets sourceBanks
    programmeMinimum modelMinimum rightMinimum observedMinimum freshFloor
  /-- Both genuine original fresh model-stage search caches. -/
  searches : ProgrammeSources.ModelSearches kept modelMinimum rightMinimum observedMinimum
  /-- The one original coordinate-independent source/model selection. -/
  selection : ProgrammeSources.Selection kept internalTarget internalPositive programmeMinimum
    modelMinimum rightMinimum observedMinimum searches
  /-- The SAME original selected source-bank observation shared by the two numerator attachments. -/
  oldObserved : ProgrammeSources.OldObserved kept internalTarget internalPositive
    sourcePrecision sourceTargets sourceBanks
    programmeMinimum modelMinimum rightMinimum observedMinimum searches selection
  /-- The same actual first whole recast chain. -/
  aChain : ProgrammeSources.AChain (fresh := fresh) (aValues := aValues)
  /-- The same actual second whole recast chain. -/
  bChain : ProgrammeSources.BChain (fresh := fresh) (bValues := bValues)
  /-- The first actual original source Targets cache. -/
  aTargets : ProgrammeSources.ATargets kept internalTarget internalPositive programmeMinimum modelMinimum
    rightMinimum observedMinimum searches selection aChain
  /-- The second actual original source Targets cache. -/
  bTargets : ProgrammeSources.BTargets kept internalTarget internalPositive programmeMinimum modelMinimum
    rightMinimum observedMinimum searches selection bChain
  /-- The actual first six-channel preparation shared by both numerator rows. -/
  aObserved : ProgrammeSources.AObserved kept internalTarget internalPositive programmeMinimum modelMinimum
    rightMinimum observedMinimum freshFloor searches selection aChain aTargets
  /-- The actual full second six-channel preparation shared by both numerator rows. -/
  bObserved : ProgrammeSources.BObserved kept internalTarget internalPositive programmeMinimum modelMinimum
    rightMinimum observedMinimum freshFloor searches selection bChain bTargets

attribute [local irreducible] ProgrammeSources.Inputs in
constructive_injectivity ProgrammeSources

include precisionPaid in
/-- Select the common stage once, then prepare one original and two fresh source caches exactly once.

Original selection factories, recast-chain operations, target factories and
source producers are consumed in that order. All three observations are
retained for both literal numerator-1 and numerator-x consumers.
-/
def observeProgrammes : ProgrammeSources kept internalTarget internalPositive sourcePrecision sourceTargets sourceBanks
    programmeMinimum modelMinimum rightMinimum observedMinimum freshFloor :=
  let aSearch := PolynomialSpine.modelSelection aValues.1 rightMinimum modelMinimum observedMinimum
    kept.share kept.share_positive
  let bSearch := PolynomialSpine.modelSelection bValues.1 rightMinimum modelMinimum observedMinimum
    kept.share kept.share_positive
  let searches : ProgrammeSources.ModelSearches kept modelMinimum rightMinimum observedMinimum :=
    (⟨aSearch.val, rfl⟩, ⟨bSearch.val, rfl⟩)
  let selected : ProgrammeSources.Selection kept internalTarget internalPositive programmeMinimum
      modelMinimum rightMinimum observedMinimum searches :=
    ⟨Sources.PolynomialAttachment.programmeSelection data (internalTarget / 4)
      (Field.div_pos_direct internalPositive (by decide : (0 : Rational) < 4)) programmeMinimum
      (ProgrammeSources.raisedMinimum kept modelMinimum rightMinimum observedMinimum searches), rfl⟩
  let oldObserved : ProgrammeSources.OldObserved kept internalTarget internalPositive
      sourcePrecision sourceTargets sourceBanks
      programmeMinimum modelMinimum rightMinimum observedMinimum searches selected :=
    ⟨sourceBanks selected.selected.stage, rfl⟩
  let aChain : ProgrammeSources.AChain (fresh := fresh) (aValues := aValues) :=
    ⟨aValues.1.chain.castParents aValues.1.parents_eq, rfl⟩
  let bChain : ProgrammeSources.BChain (fresh := fresh) (bValues := bValues) :=
    ⟨bValues.1.chain.castParents bValues.1.parents_eq, rfl⟩
  let aTargets : ProgrammeSources.ATargets kept internalTarget internalPositive programmeMinimum modelMinimum
      rightMinimum observedMinimum searches selected aChain :=
    ⟨CellEndpoints.Targets.build aChain.val.path selected.selected.stage, rfl⟩
  let bTargets : ProgrammeSources.BTargets kept internalTarget internalPositive programmeMinimum modelMinimum
      rightMinimum observedMinimum searches selected bChain :=
    ⟨CellEndpoints.Targets.build bChain.val.path selected.selected.stage, rfl⟩
  let aObserved : ProgrammeSources.AObserved kept internalTarget internalPositive programmeMinimum modelMinimum
      rightMinimum observedMinimum freshFloor searches selected aChain aTargets :=
    ⟨Cell.prepareCovered (parameter := parameter) (frame := frame)
      kept.periodPoints.aSelection.1.val.requests.covered freshFloor aTargets.val, rfl⟩
  let bObserved : ProgrammeSources.BObserved kept internalTarget internalPositive programmeMinimum modelMinimum
      rightMinimum observedMinimum freshFloor searches selected bChain bTargets :=
    ⟨Cell.prepareCovered (parameter := parameter) (frame := frame)
      kept.periodPoints.bSelection.1.val.requests.covered freshFloor bTargets.val, rfl⟩
  let inputs : ProgrammeSources.Inputs kept internalTarget sourcePrecision sourceTargets sourceBanks
      programmeMinimum modelMinimum rightMinimum observedMinimum freshFloor :=
    ⟨(kept, sourcePrecision, sourceTargets, sourceBanks,
      (internalTarget, programmeMinimum, modelMinimum, rightMinimum, observedMinimum, freshFloor)),
      rfl, precisionPaid⟩
  ⟨inputs, searches, selected, oldObserved, aChain, bChain, aTargets, bTargets, aObserved, bObserved⟩

namespace ProgrammeSources

variable {kept internalTarget internalPositive sourcePrecision sourceTargets sourceBanks
  programmeMinimum modelMinimum rightMinimum observedMinimum freshFloor}
    (sources : ProgrammeSources kept internalTarget internalPositive sourcePrecision sourceTargets sourceBanks
      programmeMinimum modelMinimum rightMinimum observedMinimum freshFloor)

/-- Read the actual common source/model stage from the SAME retained original selection. -/
@[expose] def stage : Nat := sources.selection.selected.stage

include sources in
/-- The original programme precision law belongs to the actual retained source rule and input cache. -/
theorem precision_floor (index : Nat) : index ≤ sourcePrecision index := sources.inputCache.property.2 index

/-- Read the actual old six-channel observation without executing the source rule again. -/
@[expose] def oldObservation : Sources (count := count) (floor := floor) (original := childChain.path)
    (stage := sourcePrecision sources.stage) (targets := (sourceTargets sources.stage).val) data :=
  sources.oldObserved.val

/-- The complete old observation is the literal supplied rule at this SAME selected index. -/
theorem oldObservation_eq : sources.oldObservation = sourceBanks sources.stage := sources.oldObserved.property

/-- An abstract finite maximum dominates each of its retained scalar input floors. -/
private theorem common_floors (minimum first last observed firstSource lastSource firstPeriod lastPeriod : Nat) :
    let chosen := max minimum (max first (max last (max observed
      (max firstSource (max lastSource (max firstPeriod lastPeriod))))))
    minimum ≤ chosen ∧ first ≤ chosen ∧ last ≤ chosen ∧ observed ≤ chosen ∧
      firstSource ≤ chosen ∧ lastSource ≤ chosen ∧ firstPeriod ≤ chosen ∧ lastPeriod ≤ chosen := by
  refine ⟨Data.Nat.Order.le_max_left _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)
  · exact (Data.Nat.Order.le_max_left _ _).trans
      ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _))
  · exact (Data.Nat.Order.le_max_left _ _).trans
      ((Data.Nat.Order.le_max_right _ _).trans
        ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)))
  · exact (Data.Nat.Order.le_max_left _ _).trans
      ((Data.Nat.Order.le_max_right _ _).trans
        ((Data.Nat.Order.le_max_right _ _).trans
          ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _))))
  · exact (Data.Nat.Order.le_max_left _ _).trans
      ((Data.Nat.Order.le_max_right _ _).trans
        ((Data.Nat.Order.le_max_right _ _).trans
          ((Data.Nat.Order.le_max_right _ _).trans
            ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)))))
  · exact (Data.Nat.Order.le_max_left _ _).trans
      ((Data.Nat.Order.le_max_right _ _).trans
        ((Data.Nat.Order.le_max_right _ _).trans
          ((Data.Nat.Order.le_max_right _ _).trans
            ((Data.Nat.Order.le_max_right _ _).trans
              ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _))))))
  · exact (Data.Nat.Order.le_max_right _ _).trans
      ((Data.Nat.Order.le_max_right _ _).trans
        ((Data.Nat.Order.le_max_right _ _).trans
          ((Data.Nat.Order.le_max_right _ _).trans
            ((Data.Nat.Order.le_max_right _ _).trans
              ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _))))))

/-- All original observed/source/model/period floors are paid by the one actual common selection. -/
@[expose] def Floors : Prop :=
  modelMinimum ≤ sources.stage ∧ sources.searches.1.val.stage ≤ sources.stage ∧
    sources.searches.2.val.stage ≤ sources.stage ∧ observedMinimum ≤ sources.stage ∧
    kept.periodPoints.aSelection.2.1.val.stage ≤ sources.stage ∧
    kept.periodPoints.bSelection.2.1.val.stage ≤ sources.stage ∧
    kept.periodPoints.aSelection.2.2.val.stage ≤ sources.stage ∧
    kept.periodPoints.bSelection.2.2.val.stage ≤ sources.stage

/-- The actual common stage derives every sufficient floor internally from the original retained search and maxima. -/
theorem floors : Floors sources := by
  have scalar := common_floors modelMinimum sources.searches.1.val.stage sources.searches.2.val.stage observedMinimum
    kept.periodPoints.aSelection.2.1.val.stage kept.periodPoints.bSelection.2.1.val.stage
    kept.periodPoints.aSelection.2.2.val.stage kept.periodPoints.bSelection.2.2.val.stage
  have selected : raisedMinimum kept modelMinimum rightMinimum observedMinimum sources.searches ≤ sources.stage :=
    (Data.Nat.Order.le_max_right _ _).trans sources.selection.selected.lower
  exact ⟨scalar.1.trans selected, scalar.2.1.trans selected, scalar.2.2.1.trans selected,
    scalar.2.2.2.1.trans selected, scalar.2.2.2.2.1.trans selected, scalar.2.2.2.2.2.1.trans selected,
    scalar.2.2.2.2.2.2.1.trans selected, scalar.2.2.2.2.2.2.2.trans selected⟩

/-- The actual caller's old-source programme minimum remains in the common selected stage. -/
theorem programme_minimum_le : programmeMinimum ≤ sources.stage :=
  (Data.Nat.Order.le_max_left _ _).trans sources.selection.selected.lower

/-- Every requested later fresh-programme index is allowed by the true old-model search minimum. -/
theorem right_minimum_le : rightMinimum ≤ sources.stage :=
  ((Data.Nat.Order.le_max_left _ _).trans sources.searches.1.val.lower).trans sources.floors.2.1

end ProgrammeSources

end GridWord

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry

end
