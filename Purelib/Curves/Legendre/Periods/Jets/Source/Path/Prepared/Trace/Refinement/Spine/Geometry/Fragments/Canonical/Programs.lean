module

import Purelib.Curves.Legendre.Periods.Jets.Basic
public import Purelib.Curves.Legendre.Periods.Jets.Programs
public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Jet
public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Fragments.Canonical
public import
Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Polynomial.Preparation
import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Jet.Comparison
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Tactic.Ring
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank.Clearance
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents.Polynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents.Polynomial.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical.Polynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ClosedReduction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.GeometricBasis
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Chain
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Fragments
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Occurrences
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Polynomial
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Requests
import Purelib.Curves.Legendre.Periods.Jets.Specification
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Annulus
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Periods
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Stems
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Comparison
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Coordinates
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Paired
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Polynomial
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Polynomial.Periods
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathTrace.Lineage
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Adaptive source programmes on an actual canonical cochain bank

The original acquired request gives its whole cover identity. A genuine
source/model selection precedes one paid canonical comparison, whose actual
numerical cache is attached once to the fixed source rule. All later source
models compare with that SAME retained cochain; neither a fresh period name
nor a different geometric cycle is manufactured from its scalar reading.
-/

public section

-- The builtin check revisits shared dependent terms exponentially here.
-- Retain the original parameter telescope; check its compiled binder usage.
set_option linter.unusedSectionVars false

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.LiftedPuncturedGrid (ClearanceRefinement)
open Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement (PeriodFaces)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)

open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Data.Gaussian.Norm.Basic (normSq normSq_neg)
open Purelib.Data.Gaussian.Norm.Bounds (normSq_add_le_two)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass)

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
    {primitiveTarget : Rational} {primitivePositive : 0 < primitiveTarget} {primitiveMinimum : Nat}
    (acquired : AcquiredFragments (framed := refined.fineBase)
      (original.vertices.owner original.frames vertex) period data canonical
      (original.vertices.coordinate_onGrid vertex) refined.included
      primitiveTarget primitivePositive primitiveMinimum)
    {oldTolerance : Rational} {oldPositive : 0 < oldTolerance} {oldMinimum : Nat}
    {routeTarget chartTarget : Rational} {routePositive : 0 < routeTarget} {chartPositive : 0 < chartTarget}
    {extras : List Canonical}
    (kept : GridWord period faces domains data canonical childChain completed acquired.request acquired.fragments
      oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras)

variable (sourcePrecision : Nat → Nat)
    (sourceTargets : (index : Nat) → {value : CellEndpoints.Targets childChain.path (sourcePrecision index) //
      value = CellEndpoints.Targets.build childChain.path (sourcePrecision index)})
    (sourceBanks : (index : Nat) → Sources (count := count) (floor := floor)
      (original := childChain.path) (stage := sourcePrecision index) (targets := (sourceTargets index).val) data)
    (precisionPaid : ∀ index, index ≤ sourcePrecision index)

namespace GridWord

/-- The retained acquired request and fragment factory give the SAME complete source cover.

This reads both original whole factories. An arbitrary supplied request
with the same coordinates is insufficient to derive this equality.
-/
theorem acquired_covered : acquired.fragments.request.requests.covered = data.covered :=
  (congrArg (fun actual : ControlledSumRequest data.parents count primitiveTarget => actual.requests.covered)
    acquired.fragments.request_eq).trans
      (Sources.controlledRequests_covered data acquired.request primitivePositive primitiveMinimum acquired.request_eq)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Data.Vector (DependentVector)
open Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement
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
    (minimum : Nat) (coordinate : Fin 2)
    (requested : Rational) (positiveRequest : 0 < requested)
    (programmeMinimum modelMinimum minimumWorkFloor : Nat)

/-- The exact given word, acquisition, source rules and independent request-floor payload. -/
@[expose] def ProgrammeComparison.Inputs : Type _ :=
  GridWord period faces domains data canonical childChain completed acquired.request acquired.fragments
        oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras ×
      AcquiredFragments (framed := refined.fineBase)
        (original.vertices.owner original.frames vertex) period data canonical
        (original.vertices.coordinate_onGrid vertex) refined.included
        primitiveTarget primitivePositive primitiveMinimum ×
      (Nat → Nat) ×
      ((index : Nat) → {value : CellEndpoints.Targets childChain.path (sourcePrecision index) //
        value = CellEndpoints.Targets.build childChain.path (sourcePrecision index)}) ×
      ((index : Nat) → Sources (count := count) (floor := floor) (original := childChain.path)
        (stage := sourcePrecision index) (targets := (sourceTargets index).val) data) ×
      (Fin 2 × Rational × Nat × Nat × Nat)

/-- Retain all original source rules and word inputs with their whole identities and precision law. -/
@[expose] def ProgrammeComparison.InputCache : Type _ :=
  {value : ProgrammeComparison.Inputs (period := period) (faces := faces) (domains := domains) (data := data) (canonical
    := canonical)
    (childChain := childChain) (completed := completed) (acquired := acquired)
    (sourcePrecision := sourcePrecision) (sourceTargets := sourceTargets)
    (oldTolerance := oldTolerance) (oldPositive := oldPositive) (oldMinimum := oldMinimum)
    (routeTarget := routeTarget) (chartTarget := chartTarget)
    (routePositive := routePositive) (chartPositive := chartPositive) (extras := extras) //
    value = (kept, acquired, sourcePrecision, sourceTargets, sourceBanks,
      (coordinate, requested, programmeMinimum, modelMinimum, minimumWorkFloor)) ∧
      ∀ index, index ≤ sourcePrecision index}

/-- The exact retained source attachment on the given selected cochain and source observation. -/
@[expose] def ProgrammeComparison.AttachmentCache
    (selected : Search.Selection (32 * movementMass data.parents)
      (max programmeMinimum modelMinimum) ((requested / 4) / 4))
    (paid : CanonicalComparison kept coordinates minimum
      ⟨Specification.valueSpecification parameter coordinate,
        Specification.valueSpecification_denominatorPairs parameter coordinate⟩
      ((requested / 4) / 4) (requested / 4)
      (Field.div_pos_direct (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
        (by decide : (0 : Rational) < 4))
      (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4)) minimumWorkFloor selected.stage)
    (observed : Sources (count := count) (floor := floor)
      (original := childChain.path) (stage := sourcePrecision selected.stage)
      (targets := (sourceTargets selected.stage).val) data) : Type _ :=
  {attached : Sources.PolynomialAttachment (count := count) (floor := floor)
      (targets := (sourceTargets selected.stage).val)
      data observed acquired.fragments.request.requests (acquired_covered period data canonical acquired)
      childChain coordinate paid.compared.prepared.numerical.work
        paid.compared.prepared.numerical.models
      paid.compared.prepared.numerical.sharedMeshes paid.inputWord.entries
        paid.inputWord.rootCache.val
      paid.compared.prepared.numerical.word //
    attached.comparison = paid.compared.prepared.numerical.comparison}

/-- The exact paid cochain, source observation and attachment execution on one already selected stage. -/
@[expose] def ProgrammeComparison.Execution (selected : Search.Selection (32 * movementMass data.parents)
      (max programmeMinimum modelMinimum) ((requested / 4) / 4)) : Type _ :=
  (Σ paid : {value : CanonicalComparison kept coordinates minimum
      ⟨Specification.valueSpecification parameter coordinate,
        Specification.valueSpecification_denominatorPairs parameter coordinate⟩
      ((requested / 4) / 4) (requested / 4)
      (Field.div_pos_direct (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
        (by decide : (0 : Rational) < 4))
      (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4)) minimumWorkFloor selected.stage
        //
    value = prepareCanonical kept coordinates minimum
      ⟨Specification.valueSpecification parameter coordinate,
        Specification.valueSpecification_denominatorPairs parameter coordinate⟩
      ((requested / 4) / 4) (requested / 4)
      (Field.div_pos_direct (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
        (by decide : (0 : Rational) < 4))
      (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4)) minimumWorkFloor selected.stage},
  Σ observed : {value : Sources (count := count) (floor := floor)
      (original := childChain.path) (stage := sourcePrecision selected.stage)
      (targets := (sourceTargets selected.stage).val) data // value = sourceBanks selected.stage},
  ProgrammeComparison.AttachmentCache
    (period := period) (faces := faces) (domains := domains) (data := data) (canonical := canonical)
    (childChain := childChain) (completed := completed) (acquired := acquired) (kept := kept)
    (sourcePrecision := sourcePrecision) (sourceTargets := sourceTargets)
    (coordinates := coordinates) (minimum := minimum) (coordinate := coordinate)
    (requested := requested) (positiveRequest := positiveRequest)
    (programmeMinimum := programmeMinimum) (modelMinimum := modelMinimum) (minimumWorkFloor := minimumWorkFloor)
    selected paid.val observed.val)

/-- The original actual source/model search and its complete selection factory. -/
@[expose] def ProgrammeComparison.SelectionCache : Type _ :=
  {value : Search.Selection (32 * movementMass data.parents)
      (max programmeMinimum modelMinimum) ((requested / 4) / 4) //
    value = Sources.PolynomialAttachment.programmeSelection data (requested / 4)
      (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4)) programmeMinimum modelMinimum}

/-- Read the actual retained source/model selection without unfolding its factory proof. -/
@[expose] def ProgrammeComparison.SelectionCache.selected
    (retained : ProgrammeComparison.SelectionCache (data := data) (requested := requested)
      (positiveRequest := positiveRequest) (programmeMinimum := programmeMinimum) (modelMinimum := modelMinimum)) :
    Search.Selection (32 * movementMass data.parents)
      (max programmeMinimum modelMinimum) ((requested / 4) / 4) := retained.val

attribute [local irreducible] ProgrammeComparison.Inputs ProgrammeComparison.InputCache
  ProgrammeComparison.Execution ProgrammeComparison.SelectionCache in
set_option genInjectivity false in
/-- The actual acquired geometry, one paid cochain bank and its SAME numerical cache attached to the source rule.

The actual source/model floor is selected before the new bank. The complete
old acquisition, independent programme rules, target and construction floors
remain DATA. No numerical preparation, observation or comparison is rebuilt
when the source attachment is assembled.
-/
structure ProgrammeComparison : Type _ where
  /-- The same whole acquired word, source rules and independent request floors. -/
  inputCache : ProgrammeComparison.InputCache (period := period) (faces := faces) (domains := domains) (data := data)
    (canonical := canonical)
    (childChain := childChain) (completed := completed) (acquired := acquired)
    (sourcePrecision := sourcePrecision) (sourceTargets := sourceTargets)
    (kept := kept) (sourceBanks := sourceBanks) (coordinate := coordinate) (requested := requested)
    (programmeMinimum := programmeMinimum) (modelMinimum := modelMinimum) (minimumWorkFloor := minimumWorkFloor)
  /-- The actual source/model selection made before the shared numerical bank. -/
  selectionCache : ProgrammeComparison.SelectionCache (data := data) (requested := requested)
    (positiveRequest := positiveRequest) (programmeMinimum := programmeMinimum) (modelMinimum := modelMinimum)
  /-- The original paid cochain, source observation and comparison on the selected stage. -/
  executionCache : ProgrammeComparison.Execution
    (period := period) (faces := faces) (domains := domains) (data := data) (canonical := canonical)
    (childChain := childChain) (completed := completed) (acquired := acquired) (kept := kept)
    (sourcePrecision := sourcePrecision) (sourceTargets := sourceTargets) (sourceBanks := sourceBanks)
    (coordinates := coordinates) (minimum := minimum) (coordinate := coordinate)
    (requested := requested) (positiveRequest := positiveRequest)
    (programmeMinimum := programmeMinimum) (modelMinimum := modelMinimum) (minimumWorkFloor := minimumWorkFloor)
    selectionCache.selected

attribute [local irreducible] ProgrammeComparison.Inputs ProgrammeComparison.InputCache
  ProgrammeComparison.Execution in
constructive_injectivity ProgrammeComparison

/-- Attach a given certified source observation to the same paid cochain comparison.

The observation retains its original programme stage, actual target and
whole source-rule factory. Only the existing comparison attachment and
record packing execute; the source rule and numerical bank are not run.
-/
def ProgrammeComparison.fromObserved
    (inputs : ProgrammeComparison.InputCache (period := period) (faces := faces) (domains := domains)
      (data := data) (canonical := canonical) (childChain := childChain) (completed := completed)
      (acquired := acquired) (kept := kept) (sourcePrecision := sourcePrecision) (sourceTargets := sourceTargets)
      (sourceBanks := sourceBanks) (coordinate := coordinate) (requested := requested)
      (programmeMinimum := programmeMinimum) (modelMinimum := modelMinimum) (minimumWorkFloor := minimumWorkFloor))
    (selected : ProgrammeComparison.SelectionCache (data := data) (requested := requested)
      (positiveRequest := positiveRequest) (programmeMinimum := programmeMinimum) (modelMinimum := modelMinimum))
    (paid : {value : CanonicalComparison kept coordinates minimum
      ⟨Specification.valueSpecification parameter coordinate,
        Specification.valueSpecification_denominatorPairs parameter coordinate⟩
      ((requested / 4) / 4) (requested / 4)
      (Field.div_pos_direct (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
        (by decide : (0 : Rational) < 4))
      (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
      minimumWorkFloor selected.val.stage //
      value = prepareCanonical kept coordinates minimum
        ⟨Specification.valueSpecification parameter coordinate,
          Specification.valueSpecification_denominatorPairs parameter coordinate⟩
        ((requested / 4) / 4) (requested / 4)
        (Field.div_pos_direct (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
          (by decide : (0 : Rational) < 4))
        (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
        minimumWorkFloor selected.val.stage})
    (observed : {value : Sources (count := count) (floor := floor)
      (original := childChain.path) (stage := sourcePrecision selected.val.stage)
      (targets := (sourceTargets selected.val.stage).val) data //
      value = sourceBanks selected.val.stage}) :
    ProgrammeComparison period faces domains data canonical childChain completed acquired kept
      sourcePrecision sourceTargets sourceBanks coordinates minimum coordinate requested positiveRequest
      programmeMinimum modelMinimum minimumWorkFloor := by
  let attached : Sources.PolynomialAttachment (count := count) (floor := floor)
      (targets := (sourceTargets selected.val.stage).val)
      data observed.val acquired.fragments.request.requests (acquired_covered period data canonical acquired)
      childChain coordinate paid.val.compared.prepared.numerical.work
        paid.val.compared.prepared.numerical.models
      paid.val.compared.prepared.numerical.sharedMeshes paid.val.inputWord.entries
        paid.val.inputWord.rootCache.val
      paid.val.compared.prepared.numerical.word := Sources.PolynomialAttachment.ofComparison
    (parameter := parameter) (frame := frame) (basis := standardDifferential basisIndex) (sheet := 0)
    (count := count) (floor := floor) (sourcePath := childChain.path) (stage := sourcePrecision selected.val.stage)
    (polynomialFloor := paid.val.compared.prepared.numerical.sourceFloor)
    (polynomialStage := selected.val.stage)
    (branches := branches) (higher := higher) (base := refined.fineBase)
    (rootFrames := refined.fine.frames) (domains := domains)
    (numericIndex := paid.val.compared.prepared.numerical.faceStage)
    (numerics := paid.val.compared.prepared.numerical.primitiveBank) (budgets :=
      paid.val.compared.prepared.numerical.meshBudgets)
    (targets := (sourceTargets selected.val.stage).val)
    data observed.val acquired.fragments.request.requests (acquired_covered period data canonical acquired)
    childChain coordinate paid.val.compared.prepared.numerical.work paid.val.compared.prepared.numerical.models
    paid.val.compared.prepared.numerical.sharedMeshes paid.val.inputWord.entries paid.val.inputWord.rootCache.val
    paid.val.compared.prepared.numerical.word
    ⟨paid.val.compared.prepared.numerical.comparison, paid.val.compared.prepared.numerical.comparison_eq⟩
  have same : attached.comparison = paid.val.compared.prepared.numerical.comparison :=
    Sources.PolynomialAttachment.ofComparison_comparison (count := count) (floor := floor)
      (targets := (sourceTargets selected.val.stage).val) (retained := data) (sourceBank := observed.val)
      (requests := acquired.fragments.request.requests) (sameCovered := acquired_covered period data canonical acquired)
      (childChain := childChain) (coordinate := coordinate) (work := paid.val.compared.prepared.numerical.work)
      (models := paid.val.compared.prepared.numerical.models)
      (shared := paid.val.compared.prepared.numerical.sharedMeshes)
      (entries := paid.val.inputWord.entries) (roots := paid.val.inputWord.rootCache.val)
      (closed := paid.val.compared.prepared.numerical.word)
      ⟨paid.val.compared.prepared.numerical.comparison, paid.val.compared.prepared.numerical.comparison_eq⟩
  exact
    { inputCache := inputs
      selectionCache := selected
      executionCache := ⟨paid, observed, attached, same⟩ }

section ObservedReadbacks

variable
    (inputs : ProgrammeComparison.InputCache (period := period) (faces := faces) (domains := domains)
      (data := data) (canonical := canonical) (childChain := childChain) (completed := completed)
      (acquired := acquired) (kept := kept) (sourcePrecision := sourcePrecision) (sourceTargets := sourceTargets)
      (sourceBanks := sourceBanks) (coordinate := coordinate) (requested := requested)
      (programmeMinimum := programmeMinimum) (modelMinimum := modelMinimum) (minimumWorkFloor := minimumWorkFloor))
    (selected : ProgrammeComparison.SelectionCache (data := data) (requested := requested)
      (positiveRequest := positiveRequest) (programmeMinimum := programmeMinimum) (modelMinimum := modelMinimum))
    (paid : {value : CanonicalComparison kept coordinates minimum
      ⟨Specification.valueSpecification parameter coordinate,
        Specification.valueSpecification_denominatorPairs parameter coordinate⟩
      ((requested / 4) / 4) (requested / 4)
      (Field.div_pos_direct (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
        (by decide : (0 : Rational) < 4))
      (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
      minimumWorkFloor selected.val.stage //
      value = prepareCanonical kept coordinates minimum
        ⟨Specification.valueSpecification parameter coordinate,
          Specification.valueSpecification_denominatorPairs parameter coordinate⟩
        ((requested / 4) / 4) (requested / 4)
        (Field.div_pos_direct (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
          (by decide : (0 : Rational) < 4))
        (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
        minimumWorkFloor selected.val.stage})
    (observed : {value : Sources (count := count) (floor := floor)
      (original := childChain.path) (stage := sourcePrecision selected.val.stage)
      (targets := (sourceTargets selected.val.stage).val) data //
      value = sourceBanks selected.val.stage})

/-- The given-observation attachment retains the SAME complete original selector value. -/
theorem ProgrammeComparison.fromObserved_selection :
    (ProgrammeComparison.fromObserved period faces domains data canonical childChain completed acquired kept
      sourcePrecision sourceTargets sourceBanks coordinates minimum coordinate requested positiveRequest
      programmeMinimum modelMinimum minimumWorkFloor inputs selected paid observed).selectionCache.val = selected.val
        :=
  Eq.refl selected.val

/-- The given-observation attachment retains the whole supplied paid canonical preparation at its actual index. -/
theorem ProgrammeComparison.fromObserved_cochain_heq :
    HEq (ProgrammeComparison.fromObserved period faces domains data canonical childChain completed acquired kept
      sourcePrecision sourceTargets sourceBanks coordinates minimum coordinate requested positiveRequest
      programmeMinimum modelMinimum minimumWorkFloor inputs selected paid observed).executionCache.1.val paid.val :=
  HEq.rfl (a := paid.val)

/-- The original given-observation operation forwards the SAME complete selected source bank. -/
theorem ProgrammeComparison.fromObserved_observation_heq :
    HEq (ProgrammeComparison.fromObserved period faces domains data canonical childChain completed acquired kept
      sourcePrecision sourceTargets sourceBanks coordinates minimum coordinate requested positiveRequest
      programmeMinimum modelMinimum minimumWorkFloor inputs selected paid observed).executionCache.2.1.val
        observed.val :=
  HEq.rfl (a := observed.val)

/-- The given-observation attachment reads triangle values from the same supplied whole cochain preparation. -/
theorem ProgrammeComparison.fromObserved_triangles :
    (ProgrammeComparison.fromObserved period faces domains data canonical childChain completed acquired kept
      sourcePrecision sourceTargets sourceBanks coordinates minimum coordinate requested positiveRequest
      programmeMinimum modelMinimum minimumWorkFloor inputs selected paid
      observed).executionCache.1.val.compared.prepared.triangles.values =
        paid.val.compared.prepared.triangles.values :=
  Eq.refl paid.val.compared.prepared.triangles.values

end ObservedReadbacks

/-- Observe the original source rule once and attach it to a given paid cochain.

The exact selected stage and complete canonical comparison are retained.
The shared given-observation operation performs the remaining attachment.
-/
def ProgrammeComparison.fromCochain
    (inputs : ProgrammeComparison.InputCache (period := period) (faces := faces) (domains := domains)
      (data := data) (canonical := canonical) (childChain := childChain) (completed := completed)
      (acquired := acquired) (kept := kept) (sourcePrecision := sourcePrecision) (sourceTargets := sourceTargets)
      (sourceBanks := sourceBanks) (coordinate := coordinate) (requested := requested)
      (programmeMinimum := programmeMinimum) (modelMinimum := modelMinimum) (minimumWorkFloor := minimumWorkFloor))
    (selected : ProgrammeComparison.SelectionCache (data := data) (requested := requested)
      (positiveRequest := positiveRequest) (programmeMinimum := programmeMinimum) (modelMinimum := modelMinimum))
    (paid : {value : CanonicalComparison kept coordinates minimum
      ⟨Specification.valueSpecification parameter coordinate,
        Specification.valueSpecification_denominatorPairs parameter coordinate⟩
      ((requested / 4) / 4) (requested / 4)
      (Field.div_pos_direct (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
        (by decide : (0 : Rational) < 4))
      (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
      minimumWorkFloor selected.val.stage //
      value = prepareCanonical kept coordinates minimum
        ⟨Specification.valueSpecification parameter coordinate,
          Specification.valueSpecification_denominatorPairs parameter coordinate⟩
        ((requested / 4) / 4) (requested / 4)
        (Field.div_pos_direct (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
          (by decide : (0 : Rational) < 4))
        (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
        minimumWorkFloor selected.val.stage})
    : ProgrammeComparison period faces domains data canonical childChain completed acquired kept
      sourcePrecision sourceTargets sourceBanks coordinates minimum coordinate requested positiveRequest
      programmeMinimum modelMinimum minimumWorkFloor := by
  let observed : {value : Sources (count := count) (floor := floor)
      (original := childChain.path) (stage := sourcePrecision selected.val.stage)
      (targets := (sourceTargets selected.val.stage).val) data //
      value = sourceBanks selected.val.stage} :=
    ⟨sourceBanks selected.val.stage, rfl⟩
  exact ProgrammeComparison.fromObserved period faces domains data canonical childChain completed acquired kept
    sourcePrecision sourceTargets sourceBanks coordinates minimum coordinate requested positiveRequest
    programmeMinimum modelMinimum minimumWorkFloor inputs selected paid observed

include precisionPaid in
/-- Select the actual source/model floor, execute one paid canonical bank and attach its retained comparison once.

The original acquired request derives whole-cover ownership internally.
The given programme rules stay fixed. Their one selected source observation
is retained after the actual model stage has entered the new bank's request
pipeline; no second bank or polynomial comparison is executed.
-/
def prepareProgramme : ProgrammeComparison period faces domains data canonical childChain completed acquired kept
    sourcePrecision sourceTargets sourceBanks coordinates minimum coordinate requested positiveRequest
    programmeMinimum modelMinimum minimumWorkFloor := by
  have sharePositive : 0 < requested / 4 :=
    Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4)
  have wordPositive : 0 < (requested / 4) / 4 :=
    Field.div_pos_direct sharePositive (by decide : (0 : Rational) < 4)
  let selected : {value : Search.Selection (32 * movementMass data.parents)
      (max programmeMinimum modelMinimum) ((requested / 4) / 4) //
      value = Sources.PolynomialAttachment.programmeSelection data (requested / 4)
        sharePositive programmeMinimum modelMinimum} :=
    ⟨Sources.PolynomialAttachment.programmeSelection data (requested / 4)
      sharePositive programmeMinimum modelMinimum, rfl⟩
  let paid : {value : CanonicalComparison kept coordinates minimum
      ⟨Specification.valueSpecification parameter coordinate,
        Specification.valueSpecification_denominatorPairs parameter coordinate⟩
      ((requested / 4) / 4) (requested / 4) wordPositive sharePositive minimumWorkFloor selected.val.stage //
      value = prepareCanonical kept coordinates minimum
        ⟨Specification.valueSpecification parameter coordinate,
          Specification.valueSpecification_denominatorPairs parameter coordinate⟩
        ((requested / 4) / 4) (requested / 4) wordPositive sharePositive minimumWorkFloor selected.val.stage} :=
    ⟨prepareCanonical kept coordinates minimum
      ⟨Specification.valueSpecification parameter coordinate,
        Specification.valueSpecification_denominatorPairs parameter coordinate⟩
      ((requested / 4) / 4) (requested / 4) wordPositive sharePositive minimumWorkFloor selected.val.stage, rfl⟩
  exact ProgrammeComparison.fromCochain period faces domains data canonical childChain completed acquired kept
    sourcePrecision sourceTargets sourceBanks coordinates minimum coordinate requested positiveRequest
    programmeMinimum modelMinimum minimumWorkFloor
    ⟨(kept, acquired, sourcePrecision, sourceTargets, sourceBanks,
      (coordinate, requested, programmeMinimum, modelMinimum, minimumWorkFloor)), rfl, precisionPaid⟩ selected paid

namespace ProgrammeComparison

variable {period faces domains data canonical childChain completed acquired kept
  sourcePrecision sourceTargets sourceBanks coordinates minimum coordinate requested positiveRequest
  programmeMinimum modelMinimum minimumWorkFloor}
variable (compared : ProgrammeComparison period faces domains data canonical childChain completed acquired kept
  sourcePrecision sourceTargets sourceBanks coordinates minimum coordinate requested positiveRequest
  programmeMinimum modelMinimum minimumWorkFloor)

/-- Read all original source rules, acquired geometry and independent input floors as retained DATA. -/
@[expose] def inputs : Inputs (period := period) (faces := faces) (domains := domains) (data := data) (canonical :=
  canonical)
    (childChain := childChain) (completed := completed) (acquired := acquired)
    (sourcePrecision := sourcePrecision) (sourceTargets := sourceTargets)
    (oldTolerance := oldTolerance) (oldPositive := oldPositive) (oldMinimum := oldMinimum)
    (routeTarget := routeTarget) (chartTarget := chartTarget)
    (routePositive := routePositive) (chartPositive := chartPositive) (extras := extras) :=
  compared.inputCache.val

/-- The complete acquired word, original rules, value coordinate and requested floors stay the supplied inputs. -/
theorem inputs_eq : compared.inputs = (kept, acquired, sourcePrecision, sourceTargets, sourceBanks,
    (coordinate, requested, programmeMinimum, modelMinimum, minimumWorkFloor)) := compared.inputCache.property.1

include compared in
/-- The original actual source precision rule pays every programme index, as certified before observations. -/
theorem precision_floor (index : Nat) : index ≤ sourcePrecision index := compared.inputCache.property.2 index

/-- Read the actual source/model geometric selection made before the one new bank. -/
@[expose] def selection : Search.Selection (32 * movementMass data.parents)
    (max programmeMinimum modelMinimum) ((requested / 4) / 4) :=
  compared.selectionCache.val

/-- The retained selection is the original numerical request algorithm on the actual fixed geometry. -/
theorem selection_eq : compared.selection = Sources.PolynomialAttachment.programmeSelection data (requested / 4)
    (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4)) programmeMinimum modelMinimum :=
  compared.selectionCache.property

/-- The actual programme and polynomial-model indices pay both supplied minimum floors. -/
theorem selection_ge : max programmeMinimum modelMinimum ≤ compared.selection.stage := compared.selection.lower

/-- Read the SAME complete one-bank canonical preparation and every old/new owner/cache factory. -/
@[expose] def cochainPreparation : CanonicalComparison kept coordinates minimum
      ⟨Specification.valueSpecification parameter coordinate,
        Specification.valueSpecification_denominatorPairs parameter coordinate⟩
      ((requested / 4) / 4) (requested / 4)
      (Field.div_pos_direct (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
        (by decide : (0 : Rational) < 4))
      (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4)) minimumWorkFloor compared.selection.stage
        :=
  compared.executionCache.1.val

/-- The complete requested comparison has its original one-bank factory at the actual selected model stage. -/
theorem cochainPreparation_eq : compared.cochainPreparation = prepareCanonical kept coordinates minimum
    ⟨Specification.valueSpecification parameter coordinate,
      Specification.valueSpecification_denominatorPairs parameter coordinate⟩
    ((requested / 4) / 4) (requested / 4)
    (Field.div_pos_direct (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
      (by decide : (0 : Rational) < 4))
    (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4)) minimumWorkFloor compared.selection.stage :=
  compared.executionCache.1.property

/-- Read the literal retained old physical word passed through the paid comparison's whole input certificate. -/
@[expose] def physicalWord : GridWord period faces domains data canonical childChain completed acquired.request
  acquired.fragments
    oldTolerance oldPositive oldMinimum routeTarget chartTarget routePositive chartPositive extras :=
  compared.cochainPreparation.inputWord

/-- The complete old word, entries, root cache and reference observations remain the original given value. -/
theorem physicalWord_eq : compared.physicalWord = kept := compared.cochainPreparation.inputWord_eq

/-- Read the actual original polynomial word work, models, endpoint readings and genuine-P bank. -/
@[expose] def numerical : SplitSheets.Closed.PolynomialPreparation.Preparation compared.physicalWord.word
    (Specification.valueSpecification parameter coordinate)
    (Specification.valueSpecification_denominatorPairs parameter coordinate)
    (Inclusion.PeriodCanonical.wordAllowance ((requested / 4) / 4) (requested / 4)
      faces.view.geometry.indexed.length)
    (Inclusion.PeriodCanonical.wordAllowance_positive
      (Field.div_pos_direct (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
        (by decide : (0 : Rational) < 4))
      (Field.div_pos_direct positiveRequest (by decide : (0 : Rational) < 4))
      faces.view.geometry.indexed.length)
    minimumWorkFloor compared.selection.stage
    (some compared.cochainPreparation.compared.prepared.cochainRequests.index) :=
  compared.cochainPreparation.compared.prepared.numerical

/-- Read the one selected source-bank observation without invoking the rule again. -/
@[expose] def bankObservation : Sources (count := count) (floor := floor)
    (original := childChain.path) (stage := sourcePrecision compared.selection.stage)
    (targets := (sourceTargets compared.selection.stage).val) data :=
  compared.executionCache.2.1.val

/-- The selected source observation belongs to its literal original programme index and actual precision. -/
theorem bankObservation_eq : compared.bankObservation = sourceBanks compared.selection.stage :=
  compared.executionCache.2.1.property

/-- Read the existing source attachment on the SAME complete numerical comparison cache. -/
@[expose] def attachment : Sources.PolynomialAttachment (count := count) (floor := floor)
      (targets := (sourceTargets compared.selection.stage).val)
      data compared.bankObservation acquired.fragments.request.requests (acquired_covered period data canonical
        acquired)
      childChain coordinate compared.cochainPreparation.compared.prepared.numerical.work
        compared.cochainPreparation.compared.prepared.numerical.models
      compared.cochainPreparation.compared.prepared.numerical.sharedMeshes compared.cochainPreparation.inputWord.entries
        compared.cochainPreparation.inputWord.rootCache.val
      compared.cochainPreparation.compared.prepared.numerical.word :=
  compared.executionCache.2.2.val

/-- The retained attachment forwards the SAME complete comparison, not only its scalar readback. -/
theorem comparison_eq : compared.attachment.comparison = compared.numerical.comparison :=
  compared.executionCache.2.2.property

/-- The actual smaller internal word allowance is bounded by its distinct public word target. -/
theorem word_bound_lt : compared.numerical.comparison.bound < (requested / 4) / 4 :=
  compared.numerical.bound_lt.trans_le
    (Inclusion.PeriodCanonical.wordAllowance_le ((requested / 4) / 4) (requested / 4)
      faces.view.geometry.indexed.length)

/-- Every later actual source index and the independently selected fixed model stage pay their genuine allowance. -/
theorem source_term_lt (later : Nat) (after : compared.selection.stage ≤ later) :
    16 * (quarterRadius 1 compared.selection.stage +
      (sourceTargets later).val.localBound) * movementMass data.parents < (requested / 4) / 4 :=
  Sources.PolynomialAttachment.source_model_payment data childChain sourcePrecision sourceTargets
    compared.precision_floor
    compared.selection later compared.selection.stage after (Nat.le_refl _)

/-- Two genuinely strict quarter-shares pay their displayed factor-two sum. -/
private theorem quarter_add_lt {first last share : Rational}
    (firstSmall : first < share / 4) (lastSmall : last < share / 4) : 2 * (first + last) < share :=
  (Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rational) < 2)
    (Arithmetic.add_lt_add_direct firstSmall lastSmall)).trans_eq
      ((by ring1 : 2 * (share / 4 + share / 4) = (share / 4) * 4).trans
        (Data.Rat.Fraction.Field.div_mul_cancel_of_ne share 4 (by decide)))

/-- The actual selected source attachment pays its genuine combined allowance without retagging any request. -/
theorem bound_lt : compared.attachment.bound < requested / 4 := by
  have wordPaid : compared.attachment.comparison.bound < (requested / 4) / 4 :=
    (congrArg (fun actual : SplitSheets.PolynomialComparison.Cache compared.numerical.sharedMeshes
      acquired.fragments.request.requests compared.physicalWord.entries childChain
      compared.physicalWord.rootCache.val compared.numerical.word
      compared.numerical.work compared.numerical.models
      (Specification.valueSpecification_denominatorPairs parameter coordinate) => actual.bound)
      compared.comparison_eq).trans_lt compared.word_bound_lt
  exact compared.attachment.bound_eq.trans_lt
    (quarter_add_lt wordPaid
      (compared.source_term_lt compared.selection.stage (Nat.le_refl _)))

/-- The fixed actual model stage and numerical word compare with every later actual source programme model.

The original numerical cache remains unchanged. The source-bank rule is
used only pointwise in this proof; this is not a claim that independently
executed source callbacks are memoized. No new word, bank, query, root or
polynomial comparison is executed to obtain the later bound.
-/
theorem programme_gap_lt (later : Nat) (after : compared.selection.stage ≤ later) :
    normSq (gaussianSum (SplitSheets.Closed.gaps compared.numerical.sharedMeshes
      compared.physicalWord.entries childChain
      compared.physicalWord.rootCache.val compared.numerical.word) -
      ((Sources.certifiedAtPrecision data childChain sourcePrecision sourceTargets sourceBanks compared.precision_floor
        (Specification.Table.valueIndex coordinate)).integral.model later).integralSample) < requested / 4 := by
  let attached : Sources.PolynomialAttachment (count := count) (floor := floor)
      (targets := (sourceTargets later).val)
      data (sourceBanks later) acquired.fragments.request.requests (acquired_covered period data canonical acquired)
      childChain coordinate compared.cochainPreparation.compared.prepared.numerical.work
        compared.cochainPreparation.compared.prepared.numerical.models
      compared.cochainPreparation.compared.prepared.numerical.sharedMeshes compared.cochainPreparation.inputWord.entries
        compared.cochainPreparation.inputWord.rootCache.val
      compared.cochainPreparation.compared.prepared.numerical.word := Sources.PolynomialAttachment.ofComparison
    (parameter := parameter) (frame := frame) (basis := standardDifferential basisIndex) (sheet := 0)
    (count := count) (floor := floor) (sourcePath := childChain.path) (stage := sourcePrecision later)
    (polynomialFloor := compared.numerical.sourceFloor)
    (polynomialStage := compared.selection.stage)
    (branches := branches) (higher := higher) (base := refined.fineBase)
    (rootFrames := refined.fine.frames) (domains := domains)
    (numericIndex := compared.numerical.faceStage)
    (numerics := compared.numerical.primitiveBank) (budgets := compared.numerical.meshBudgets)
    (targets := (sourceTargets later).val)
    data (sourceBanks later) acquired.fragments.request.requests (acquired_covered period data canonical acquired)
    childChain coordinate compared.numerical.work compared.numerical.models compared.numerical.sharedMeshes
    compared.physicalWord.entries compared.physicalWord.rootCache.val compared.numerical.word
    ⟨compared.numerical.comparison, compared.numerical.comparison_eq⟩
  have same : attached.comparison = compared.numerical.comparison :=
    Sources.PolynomialAttachment.ofComparison_comparison (count := count) (floor := floor)
      (targets := (sourceTargets later).val) (retained := data) (sourceBank := sourceBanks later)
      (requests := acquired.fragments.request.requests) (sameCovered := acquired_covered period data canonical acquired)
      (childChain := childChain) (coordinate := coordinate) (work := compared.numerical.work)
      (models := compared.numerical.models) (shared := compared.numerical.sharedMeshes)
      (entries := compared.physicalWord.entries) (roots := compared.physicalWord.rootCache.val)
      (closed := compared.numerical.word)
      ⟨compared.numerical.comparison, compared.numerical.comparison_eq⟩
  have wordPaid : attached.comparison.bound < (requested / 4) / 4 :=
    (congrArg (fun actual : SplitSheets.PolynomialComparison.Cache compared.numerical.sharedMeshes
      acquired.fragments.request.requests compared.physicalWord.entries childChain
      compared.physicalWord.rootCache.val compared.numerical.word
      compared.numerical.work compared.numerical.models
      (Specification.valueSpecification_denominatorPairs parameter coordinate) => actual.bound) same).trans_lt
      compared.word_bound_lt
  have paid : attached.bound < requested / 4 := attached.bound_eq.trans_lt
    (quarter_add_lt wordPaid (compared.source_term_lt later after))
  have actual := (Sources.PolynomialAttachment.programme_error_le (count := count) (floor := floor)
    (retained := data) (requests := acquired.fragments.request.requests)
    (sameCovered := acquired_covered period data canonical acquired) (childChain := childChain)
    (coordinate := coordinate) (work := compared.numerical.work) (models := compared.numerical.models)
    (shared := compared.numerical.sharedMeshes) (entries := compared.physicalWord.entries)
    (roots := compared.physicalWord.rootCache.val)
    (closed := compared.numerical.word)
    sourcePrecision sourceTargets sourceBanks compared.precision_floor later attached).trans_lt paid
  have valueEq : attached.comparison.value = compared.numerical.value :=
    congrArg (fun actual : SplitSheets.PolynomialComparison.Cache compared.numerical.sharedMeshes
      acquired.fragments.request.requests compared.physicalWord.entries childChain
      compared.physicalWord.rootCache.val compared.numerical.word
      compared.numerical.work compared.numerical.models
      (Specification.valueSpecification_denominatorPairs parameter coordinate) => actual.value) same
  have gapsEq := valueEq.trans compared.numerical.value_eq
  exact Eq.mp (congrArg (fun value : Canonical => normSq (value -
    ((Sources.certifiedAtPrecision data childChain sourcePrecision sourceTargets sourceBanks compared.precision_floor
      (Specification.Table.valueIndex coordinate)).integral.model later).integralSample) < requested / 4) gapsEq) actual

/-- Two independently paid differences through the same literal gap value pay the full requested norm. -/
private theorem through_gap {gap first last : Canonical} {target : Rational}
    (left : normSq (gap - first) < target / 4) (right : normSq (gap - last) < target / 4) :
    normSq (last - first) < target := by
  have reversed : normSq (last - gap) < target / 4 := by
    rewrite [show last - gap = -(gap - last) by ring1, normSq_neg]
    exact right
  rewrite [show last - first = (last - gap) + (gap - first) by ring1]
  exact (normSq_add_le_two _ _).trans_lt
    (quarter_add_lt reversed left)

/-- The SAME retained canonical cochain and every sufficiently late actual source model meet the public target. -/
theorem accurate (later : Nat) (after : compared.selection.stage ≤ later) :
    normSq (compared.cochainPreparation.compared.value -
      ((Sources.certifiedAtPrecision data childChain sourcePrecision sourceTargets sourceBanks compared.precision_floor
        (Specification.Table.valueIndex coordinate)).integral.model later).integralSample) < requested :=
  through_gap (compared.programme_gap_lt later after)
    compared.cochainPreparation.compared.gap_lt

/-- The actual frame curve has the original Legendre cubic degree, independently of every numerical stage. -/
private theorem frame_degree : (Fibre.frameCurve frame).polynomial.natDegree = 2 * 1 + 1 :=
  (congrArg (fun polynomial => polynomial.natDegree) (Fibre.frameCurve_polynomial frame)).trans
    (Paths.polynomial_natDegree parameter)

/-- The literal original A factory connects every sufficiently late source value to its actual fresh-basis cochain.

The whole period and vertex identities are original constructor identities,
not numerical, root, Frame or homology conclusions. Every nonzero primitive
jump and all actual source/model/cochain charges remain in the bound.
-/
theorem a_accurate (vertexFactory : vertex = BasedBranchBank.anchor original oldSheet)
    (periodFactory : HEq period (periods.aWalk basisIndex))
    (later : Nat) (after : compared.selection.stage ≤ later) :
    normSq (coordinates.a.coordinates.periodValue
      (CanonicalEdgeValues.edgeValuation refined.fine.mesh
        compared.cochainPreparation.compared.prepared.triangles.values) -
      ((Sources.certifiedAtPrecision data childChain sourcePrecision sourceTargets sourceBanks compared.precision_floor
        (Specification.Table.valueIndex coordinate)).integral.model later).integralSample) < requested :=
  through_gap (compared.programme_gap_lt later after)
    (compared.cochainPreparation.compared.a_cochain_lt vertexFactory periodFactory (frame_degree (frame := frame)))

/-- The full corrected-B factory gives the same paid comparison, preserving every earlier-A and closing occurrence. -/
theorem b_accurate (vertexFactory : vertex = BasedBranchBank.anchor original oldSheet)
    (periodFactory : HEq period (periods.bWalk basisIndex))
    (later : Nat) (after : compared.selection.stage ≤ later) :
    normSq (coordinates.b.coordinates.periodValue
      (CanonicalEdgeValues.edgeValuation refined.fine.mesh
        compared.cochainPreparation.compared.prepared.triangles.values) -
      ((Sources.certifiedAtPrecision data childChain sourcePrecision sourceTargets sourceBanks compared.precision_floor
        (Specification.Table.valueIndex coordinate)).integral.model later).integralSample) < requested :=
  through_gap (compared.programme_gap_lt later after)
    (compared.cochainPreparation.compared.b_cochain_lt vertexFactory periodFactory (frame_degree (frame := frame)))

section ActualJet

open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)

variable (completedRule : (index : Nat) → Sources.Occurrences (count := count) (floor := floor)
    (original.vertices.owner original.frames vertex) period.closed data childChain
    (sourcePrecision index) rootStage (sourceTargets index).val (sourceTargets index).property
    (sourceBanks index) walkPositive)
    (actual : SynchronizedPeriodJet frame)
    (actualFactory : actual = Sources.jet (original.vertices.owner original.frames vertex)
      period.closed data childChain sourcePrecision sourceTargets sourceBanks completedRule precisionPaid)

include completedRule precisionPaid actualFactory in
/-- The GIVEN actual jet's value-zero or full coordinate-one programme meets the actual fresh A cochain bound.

Only the original whole jet factory transports the model owner. Neither
its period nor its root/Frame owner is identified with the fresh basis by
this exact programme readback.
-/
theorem jet_a_accurate (vertexFactory : vertex = BasedBranchBank.anchor original oldSheet)
    (periodFactory : HEq period (periods.aWalk basisIndex))
    (later : Nat) (after : compared.selection.stage ≤ later) :
    normSq (coordinates.a.coordinates.periodValue
      (CanonicalEdgeValues.edgeValuation refined.fine.mesh
        compared.cochainPreparation.compared.prepared.triangles.values) -
      ((actual.programme (Specification.Table.valueIndex coordinate)).model later).integralSample) < requested := by
  have programmeEq := Sources.jet_programme_integral (original.vertices.owner original.frames vertex)
    period.closed data childChain sourcePrecision sourceTargets sourceBanks completedRule precisionPaid
    actual actualFactory (Specification.Table.valueIndex coordinate)
  have modelEq := congrArg (fun programme : RefinementProgram => programme.model later) programmeEq
  exact Eq.mpr (congrArg (fun model : PathModel => normSq (coordinates.a.coordinates.periodValue
    (CanonicalEdgeValues.edgeValuation refined.fine.mesh
      compared.cochainPreparation.compared.prepared.triangles.values) - model.integralSample) < requested) modelEq)
    (compared.a_accurate vertexFactory periodFactory later after)

include completedRule precisionPaid actualFactory in
/-- The GIVEN actual jet's corresponding value programme meets full corrected B's actual fresh cochain bound. -/
theorem jet_b_accurate (vertexFactory : vertex = BasedBranchBank.anchor original oldSheet)
    (periodFactory : HEq period (periods.bWalk basisIndex))
    (later : Nat) (after : compared.selection.stage ≤ later) :
    normSq (coordinates.b.coordinates.periodValue
      (CanonicalEdgeValues.edgeValuation refined.fine.mesh
        compared.cochainPreparation.compared.prepared.triangles.values) -
      ((actual.programme (Specification.Table.valueIndex coordinate)).model later).integralSample) < requested := by
  have programmeEq := Sources.jet_programme_integral (original.vertices.owner original.frames vertex)
    period.closed data childChain sourcePrecision sourceTargets sourceBanks completedRule precisionPaid
    actual actualFactory (Specification.Table.valueIndex coordinate)
  have modelEq := congrArg (fun programme : RefinementProgram => programme.model later) programmeEq
  exact Eq.mpr (congrArg (fun model : PathModel => normSq (coordinates.b.coordinates.periodValue
    (CanonicalEdgeValues.edgeValuation refined.fine.mesh
      compared.cochainPreparation.compared.prepared.triangles.values) - model.integralSample) < requested) modelEq)
    (compared.b_accurate vertexFactory periodFactory later after)

end ActualJet

end ProgrammeComparison

end GridWord

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry
