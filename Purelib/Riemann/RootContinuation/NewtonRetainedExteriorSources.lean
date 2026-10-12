module
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Paths.RectangularSegmentRefinement
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunEndpoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Integration.Path.Dyadic.SourceListResampling
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.Resampling.OrientedBounds
import Purelib.Riemann.RootContinuation.NewtonRequestedHoleComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedChordPolygon
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceJunctions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CertifiedSideFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FamilyBounds
import Purelib.Integration.Polynomial.Rectangle.Perimeter.RetainedIncrements
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SharedPointReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JunctionOwnerBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedSideBlocks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourcePathComparison
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunOrder

public section

/-! Retained exterior source acquisition, ordering, and exact area comparison.
Keep these prerequisites separate from the actively refined quantitative side
bounds so downstream proof edits reuse their checked artifacts. -/
namespace Purelib.Riemann.RootContinuation.NewtonRetainedExteriorSources

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece (junctionCount
  pieceIndex junction_interval)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions.SurfaceOccurrence
  (side_span_endpoints)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit)
open Purelib.Riemann.Integration.PreparedParentSplitting (ParentSplits)
open Purelib.Riemann.Paths.RectangularSegmentRefinement (Subinterval)
open Purelib.Geometry.Rectangle.SourceIntervals (AxisCorrespondence axisIntervals locateSourceInterval)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation (LocatedParent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval (ParentInterval)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation (occurrenceAt)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters (signedAxis blockMidpoint)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters (firstParameter lastParameter)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation (occurrenceParents)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns (StoredSourceChord SourceChordGrouping)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns (SourceChordRun)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns (sourceParentIncrement)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (maximum le_maximum)
open Purelib.Integration.Path.PairedIncrementArea (area total)
open Purelib.Riemann.Normalization
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {first second : Fin genus} {target radius : Fraction.Rational} {floor :
    Nat}
  {differential : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

open Purelib.Curves.Hyperelliptic in
/-- The original prepared exterior surface occurrence for the first retained differential. -/
@[expose] def RetainedExteriorOccurrence (prepared : BoundaryPreparation preparation first second target radius floor)
  :=
  Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    prepared.exterior.regular prepared.domains (standardDifferential first)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Integration in
/-- Every point of a retained original parent split belongs to the exact prepared physical mesh.

The original split-membership witness and surface occurrence locate the point without replacing its parent or either
sheet's cached energy mesh. -/
theorem retained_exterior_points (prepared : BoundaryPreparation preparation first second target radius floor)
    (sheet : Fin 2) (position : Fin prepared.fine.family.single.grid.faces.regulars.length)
    {occurrence : RetainedExteriorOccurrence prepared} (member : occurrence ∈ prepared.exterior.prepared.occurrences)
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve (standardDifferential first)}
    {split : SegmentSplit occurrence.compared.entered.domain.cuts
      (parent.edge.point 0) (parent.edge.point 1)}
    (retained : ParentSplits.Member split occurrence.compared.entered.mesh.splits)
    {point : Basic.Canonical} (present : point ∈ split.points) :
    point ∈ ((prepared.paid.cut.exterior.prepared.energy.entries.get sheet).meshes.entries.get position).points := by
  rw [(prepared.paid.cut.exterior.prepared.energy.entries.get sheet).mesh_eq,
    ((prepared.paid.cut.exterior.prepared.energy.entries.get sheet).entries.get position).mesh_eq]
  change point ∈ ((Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build prepared.domains prepared.paid.cut.cuts
    sheet 0).entries.get position).points
  rw [Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build_points, prepared.cut_points_eq]
  exact prepared.exterior.selected.split_points member retained present

open Purelib.Geometry.Rectangle in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Riemann.Integration in
/-- Locate an original physical axis interval inside the exact retained parent split.

The supplied axis correspondence and unit-parameter bounds retain the same original endpoints, mesh membership and
source range. -/
@[expose] def locateRetainedExteriorInterval (prepared : BoundaryPreparation preparation first second target radius
  floor)
    (sheet : Fin 2) (position : Fin prepared.fine.family.single.grid.faces.regulars.length)
    {occurrence : RetainedExteriorOccurrence prepared} (member : occurrence ∈ prepared.exterior.prepared.occurrences)
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve (standardDifferential first)}
    (split : SegmentSplit occurrence.compared.entered.domain.cuts
      (parent.edge.point 0) (parent.edge.point 1))
    (retained : ParentSplits.Member split occurrence.compared.entered.mesh.splits)
    (vertical : Bool) (physical : PreparedAxisPartitions.Interval)
    (present : physical ∈ SourceIntervals.axisIntervals ((prepared.paid.cut.exterior.prepared.energy.entries.get
      sheet).meshes.entries.get position) vertical)
    (range : PreparedAxisPartitions.Interval) (within : 0 ≤ range.lower ∧ range.upper ≤ 1)
    (correspondence : SourceIntervals.AxisCorrespondence vertical
      (parent.edge.point 0) (parent.edge.point 1) range physical) : Subinterval split range :=
  SourceIntervals.locateSourceInterval ((prepared.paid.cut.exterior.prepared.energy.entries.get
    sheet).meshes.entries.get position) split
    (fun _ present => retained_exterior_points prepared sheet position member retained present)
    vertical physical present range within correspondence

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Allocate a positive-tolerance side-remainder request for the supplied original exterior preparation. -/
@[expose] def exteriorSideRequest (prepared : BoundaryPreparation preparation first second target radius floor)
    (exterior :
      Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation regular
      prepared.domains differential)
    (tolerance : Fraction.Rational) (positive : 0 < tolerance) :

      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.SideRemainderRequest
      exterior prepared.paid.cut.fixed first second tolerance :=

    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.SideRemainderRequest.build
    exterior prepared.paid.cut.fixed first second tolerance positive

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Rectangle in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Riemann.Integration in
/-- Locate the physical interval in its exact assigned original parent using signed midpoint bounds.

The original surface-membership witness and retained mesh points preserve the parent assignment, source orientation and
physical interval owner. -/
@[expose] def locateRetainedParentInterval
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {occurrences : List (RetainedExteriorOccurrence prepared)}
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve (standardDifferential first)}
    (assigned : Meshes.PuncturedGrid.Exterior.BoundaryParentLocation.LocatedParent occurrences parent)
    (member : assigned.occurrence ∈ prepared.exterior.prepared.occurrences)
    (sheet : Fin 2) (position : Fin prepared.fine.family.single.grid.faces.regulars.length)
    (vertical forward : Bool) (physical : PreparedAxisPartitions.Interval)
    (present : physical ∈ SourceIntervals.axisIntervals ((prepared.paid.cut.exterior.prepared.energy.entries.get
      sheet).meshes.entries.get position) vertical)
    (lower : Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward (parent.edge.point 0) ≤
      Meshes.PuncturedGrid.Exterior.SourceBlockParameters.blockMidpoint forward physical)
    (upper : Meshes.PuncturedGrid.Exterior.SourceBlockParameters.blockMidpoint forward physical <
      Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward (parent.edge.point 1)) :
    Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval.ParentInterval parent vertical physical :=
  Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval.LocatedParent.locateInterval assigned
    ((prepared.paid.cut.exterior.prepared.energy.entries.get sheet).meshes.entries.get position)
    (fun _ present => retained_exterior_points prepared sheet position member assigned.selected.member present)
    vertical forward physical present lower upper

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle in
/-- Exact source-chord data for every retained component, boundary occurrence and physical interval.

Each chord is indexed by the original closed comparison, sheet, face and bounded interval; these indices preserve the
original source-parent assignment. -/
@[expose] def RetainedExteriorChordAcquisition
    (prepared : BoundaryPreparation preparation first second target radius floor) : Type _ :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let sheet := occurrence.sideOccurrence.sheet
    let position := occurrence.sideOccurrence.position
    let vertical := occurrence.sourceVertical
    let meshes := (prepared.paid.cut.exterior.prepared.energy.entries.get sheet).meshes
    let intervals := SourceIntervals.axisIntervals (meshes.entries.get position) vertical
    (intervalIndex : Fin intervals.length) → Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData
        comparison
      vertical (intervals[intervalIndex.val]'intervalIndex.isLt)

open Purelib.Curves.Hyperelliptic in
/-- Acquire the original interval's source chord from its retained side crossing and assigned parent.

The exact crossing bounds locate the original parent subinterval; chord construction retains that parent index, physical
orientation and cached mesh depth. -/
@[expose] def retainedExteriorChord
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorChordAcquisition
      prepared := by
  intro componentIndex component requested minimum comparison outer occurrence sheet position vertical meshes intervals
    intervalIndex
  let forward := occurrence.sourceForward
  let physical := intervals[intervalIndex.val]'intervalIndex.isLt
  have present : physical ∈ intervals := List.getElem_mem intervalIndex.isLt
  let crossing := comparison.locateSideInterval outer meshes physical present
  let assigned := crossing.assigned
  have member := assigned.in_surface prepared.exterior.prepared (List.getElem_mem componentIndex.isLt)
  let range := locateRetainedParentInterval prepared assigned member sheet position vertical forward physical present
    crossing.lower crossing.upper
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData.build
    comparison crossing.index forward vertical physical range (crossing.lower.trans_lt crossing.upper)
      (meshes.entries.get position).depth

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Topology.Polygon in
/-- Adjacent retained chords differ only by their original parent-boundary jump.

Within one original parent the junction difference vanishes; crossing parents reads their exact oriented endpoints from
the same retained comparison. -/
@[expose] def RetainedExteriorSourceJunction
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let side := occurrence.sideOccurrence.side
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
      occurrence.sideOccurrence.sheet).meshes.entries.get
      occurrence.sideOccurrence.position
    ∀ i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side),
    let before := retainedExteriorChord prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i.castSucc)
    let after := retainedExteriorChord prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i.succ)
    (comparison.sourceValues after.index (Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.firstParameter
      after.forward after.range)).sub
      (comparison.sourceValues before.index (Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.lastParameter
        before.forward before.range)) =
    if after.index = before.index then Stokes.PrimitivePoint.zero else
      (comparison.sourceValues after.index (if occurrence.sourceForward then 0 else 1)).sub
        (comparison.sourceValues before.index (if occurrence.sourceForward then 1 else 0))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Adjacent retained chord parent indices follow the original source orientation. -/
@[expose] def RetainedExteriorSourceOrder
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let side := occurrence.sideOccurrence.side
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
      occurrence.sideOccurrence.sheet).meshes.entries.get
      occurrence.sideOccurrence.position
    ∀ i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side),
    let before := retainedExteriorChord prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i.castSucc)
    let after := retainedExteriorChord prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i.succ)
    if occurrence.sourceForward then before.index.val ≤ after.index.val else after.index.val ≤ before.index.val

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Rectangle in
/-- The original physical junction order induces the retained source-parent index order. -/
theorem retained_exterior_source_order
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorSourceOrder prepared
      := by
  intro componentIndex component requested minimum comparison outer occurrence side mesh i before after
  let meshes := (prepared.paid.cut.exterior.prepared.energy.entries.get occurrence.sideOccurrence.sheet).meshes
  let intervals := SourceIntervals.axisIntervals mesh occurrence.sourceVertical
  let firstIndex := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side
    i.castSucc
  let lastIndex := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i.succ
  have consecutive := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junction_interval
    ((prepared.traces.get occurrence.sideOccurrence.position).get occurrence.sideOccurrence.sheet) side i
  exact comparison.locateSideInterval_order outer meshes
    (intervals[firstIndex.val]'firstIndex.isLt) (intervals[lastIndex.val]'lastIndex.isLt)
    (List.getElem_mem firstIndex.isLt) (List.getElem_mem lastIndex.isLt) consecutive.symm.le

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Distinct adjacent retained source parents have separated oriented endpoint coordinates.

The original parent indices determine the separation direction, preserving the signed axis and exact endpoint owners. -/
@[expose] def RetainedExteriorParentSeparation
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let side := occurrence.sideOccurrence.side
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
      occurrence.sideOccurrence.sheet).meshes.entries.get
      occurrence.sideOccurrence.position
    ∀ i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side),
    let before := retainedExteriorChord prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i.castSucc)
    let after := retainedExteriorChord prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i.succ)
    let project := Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis occurrence.sourceVertical
      occurrence.sourceForward
    after.index ≠ before.index →
      if occurrence.sourceForward then
        project ((comparison.Parent before.index).edge.point 1) ≤ project ((comparison.Parent after.index).edge.point 0)
      else
        project ((comparison.Parent after.index).edge.point 1) ≤ project ((comparison.Parent before.index).edge.point 0)

/-- Distinct ordered bounded indices select the corresponding strict separation case in either orientation. -/
private theorem ordered_pair_separated {count : Nat} (forward : Bool) (i j : Fin count) {left right : Prop}
    (ordered : if forward then i.val ≤ j.val else j.val ≤ i.val) (different : j ≠ i)
    (first : i.val < j.val → left) (last : j.val < i.val → right) : if forward then left else right := by
  cases forward with
  | true => exact first (Nat.lt_of_le_of_ne ordered (fun equal => different (Fin.ext equal).symm))
  | false => exact last (Nat.lt_of_le_of_ne ordered (fun equal => different (Fin.ext equal)))

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Rectangle in
/-- The original side-interval ordering separates distinct adjacent retained source parents. -/
theorem retained_exterior_parent_separation
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorParentSeparation
      prepared := by
  intro componentIndex component requested minimum comparison outer occurrence side mesh i before after project
    different
  let meshes := (prepared.paid.cut.exterior.prepared.energy.entries.get occurrence.sideOccurrence.sheet).meshes
  let intervals := SourceIntervals.axisIntervals mesh occurrence.sourceVertical
  let firstIndex := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side
    i.castSucc
  let lastIndex := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i.succ
  have ordered := retained_exterior_source_order prepared componentIndex comparison outer i
  apply ordered_pair_separated occurrence.sourceForward before.index after.index ordered different
  · intro strict
    exact comparison.locateSideInterval_separated outer meshes
      (intervals[firstIndex.val]'firstIndex.isLt) (intervals[lastIndex.val]'lastIndex.isLt)
      (List.getElem_mem firstIndex.isLt) (List.getElem_mem lastIndex.isLt) strict
  · intro strict
    exact comparison.locateSideInterval_separated outer meshes
      (intervals[lastIndex.val]'lastIndex.isLt) (intervals[firstIndex.val]'firstIndex.isLt)
      (List.getElem_mem lastIndex.isLt) (List.getElem_mem firstIndex.isLt) strict

open Purelib.Curves.Hyperelliptic in
open Purelib.Topology.Polygon in
/-- The exact retained chord junction equals its original cross-parent endpoint jump or zero.

Physical interval adjacency and oriented parent separation identify the same endpoint parameters; no new parent or
primitive reading is introduced. -/
theorem retained_exterior_source_junction
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorSourceJunction
      prepared := by
  intro componentIndex component requested minimum comparison outer occurrence side mesh i before after
  have consecutive := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junction_interval
    ((prepared.traces.get occurrence.sideOccurrence.position).get occurrence.sideOccurrence.sheet) side i
  if same : after.index = before.index then
    exact (before.same_parent_join after same consecutive).trans (if_pos same).symm
  else
    have separated := retained_exterior_parent_separation prepared componentIndex comparison outer i same
    have endpoints := before.cross_parent_endpoints after occurrence.sourceForward rfl rfl consecutive separated
    have readback := congrArg₂ Stokes.PrimitivePoint.sub
      (congrArg (comparison.sourceValues after.index) endpoints.2)
      (congrArg (comparison.sourceValues before.index) endpoints.1)
    exact readback.trans (if_neg same).symm

/-- An oriented strict index step with its junction condition identifies the immediate successor. -/
private theorem successor_in_orientation {count : Nat} (forward : Bool) (i j : Fin count) {left right : Prop}
    (ordered : if forward then i.val ≤ j.val else j.val ≤ i.val) (different : j ≠ i)
    (joint : if forward then left else right)
    (first : i.val < j.val → left → j.val = i.val + 1)
    (last : j.val < i.val → right → i.val = j.val + 1) :
    if forward then j.val = i.val + 1 else i.val = j.val + 1 := by
  cases forward with
  | true => exact first (Nat.lt_of_le_of_ne ordered (fun equal => different (Fin.ext equal).symm)) joint
  | false => exact last (Nat.lt_of_le_of_ne ordered (fun equal => different (Fin.ext equal))) joint

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Adjacent retained chords stay in one original parent or advance exactly one parent in source orientation. -/
@[expose] def RetainedExteriorNoSkippedParents
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let side := occurrence.sideOccurrence.side
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
      occurrence.sideOccurrence.sheet).meshes.entries.get
      occurrence.sideOccurrence.position
    ∀ i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side),
    let before := retainedExteriorChord prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i.castSucc)
    let after := retainedExteriorChord prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i.succ)
    after.index = before.index ∨
      (if occurrence.sourceForward then after.index.val = before.index.val + 1 else before.index.val = after.index.val +
        1)

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Rectangle in
/-- The retained chord sequence cannot skip an original source parent.

The exact crossing endpoints and original side-interval location rule identify consecutive parent indices in the
retained orientation. -/
theorem retained_exterior_no_skipped_parents
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorNoSkippedParents
      prepared := by
  intro componentIndex component requested minimum comparison outer occurrence side mesh i before after
  if same : after.index = before.index then exact Or.inl same
  else
    apply Or.inr
    let meshes := (prepared.paid.cut.exterior.prepared.energy.entries.get occurrence.sideOccurrence.sheet).meshes
    let intervals := SourceIntervals.axisIntervals mesh occurrence.sourceVertical
    let firstIndex := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side
      i.castSucc
    let lastIndex := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i.succ
    have consecutive := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junction_interval
      ((prepared.traces.get occurrence.sideOccurrence.position).get occurrence.sideOccurrence.sheet) side i
    have separated := retained_exterior_parent_separation prepared componentIndex comparison outer i same
    have endpoints := before.cross_parent_endpoints after occurrence.sourceForward rfl rfl consecutive separated
    have joint := before.parent_junction after occurrence.sourceForward consecutive endpoints
    have ordered := retained_exterior_source_order prepared componentIndex comparison outer i
    apply successor_in_orientation occurrence.sourceForward before.index after.index ordered same joint
    · intro strict equal
      exact comparison.locateSideInterval_no_skip outer meshes
        (intervals[firstIndex.val]'firstIndex.isLt) (intervals[lastIndex.val]'lastIndex.isLt)
        (List.getElem_mem firstIndex.isLt) (List.getElem_mem lastIndex.isLt) strict equal
    · intro strict equal
      exact comparison.locateSideInterval_no_skip outer meshes
        (intervals[lastIndex.val]'lastIndex.isLt) (intervals[firstIndex.val]'firstIndex.isLt)
        (List.getElem_mem lastIndex.isLt) (List.getElem_mem firstIndex.isLt) strict equal

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- The first and last retained chords span the original oriented unit source interval. -/
@[expose] def RetainedExteriorSourceEndpoints
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let side := occurrence.sideOccurrence.side
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
      occurrence.sideOccurrence.sheet).meshes.entries.get
      occurrence.sideOccurrence.position
    let first := retainedExteriorChord prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side 0)
    let last := retainedExteriorChord prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side (Fin.last
        (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side)))
    if occurrence.sourceForward then
      Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.firstParameter first.forward first.range = 0 ∧
        Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.lastParameter last.forward last.range = 1
    else
      Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.lastParameter last.forward last.range = 0 ∧
        Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.firstParameter first.forward first.range = 1

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Rectangle in
/-- Original source and physical side endpoints give the retained chord sequence its complete unit span. -/
theorem retained_exterior_source_endpoints
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorSourceEndpoints
      prepared := by
  intro componentIndex component requested minimum comparison outer occurrence side mesh first last
  let meshes := (prepared.paid.cut.exterior.prepared.energy.entries.get occurrence.sideOccurrence.sheet).meshes
  let intervals := SourceIntervals.axisIntervals mesh occurrence.sourceVertical
  let firstIndex := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side 0
  let lastIndex := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side (Fin.last
    (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side))
  have firstBounds := comparison.locateSideInterval_bounds outer meshes
    (intervals[firstIndex.val]'firstIndex.isLt) (List.getElem_mem firstIndex.isLt)
  have lastBounds := comparison.locateSideInterval_bounds outer meshes
    (intervals[lastIndex.val]'lastIndex.isLt) (List.getElem_mem lastIndex.isLt)
  have source := occurrence.source_span_endpoints
  have physical := Meshes.PuncturedGrid.Exterior.RetainedJunctions.SurfaceOccurrence.side_span_endpoints occurrence
    meshes
  exact first.side_endpoints last occurrence.sourceForward rfl rfl
    ⟨source.1.symm.trans_le firstBounds.1, firstBounds.2.trans_eq source.2⟩
    ⟨source.1.symm.trans_le lastBounds.1, lastBounds.2.trans_eq source.2⟩ physical.1 physical.2

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- The retained chord sequence starts and finishes at the original occurrence's parent-list boundaries.

The exact preceding-occurrence offset and cached parent count determine both extreme indices in the retained
orientation. -/
@[expose] def RetainedExteriorEndpointPositions
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let side := occurrence.sideOccurrence.side
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
      occurrence.sideOccurrence.sheet).meshes.entries.get
      occurrence.sideOccurrence.position
    let first := retainedExteriorChord prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side 0)
    let last := retainedExteriorChord prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side (Fin.last
        (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side)))
    let offset := (Meshes.PuncturedGrid.Exterior.BoundaryParentLocation.occurrenceParents
      (component.prepared.occurrences.take outer.val)).length
    let count := occurrence.compared.entered.cache.parents.length
    if occurrence.sourceForward then first.index.val = offset ∧ last.index.val + 1 = offset + count
    else last.index.val = offset ∧ first.index.val + 1 = offset + count

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Rectangle in
/-- The exact first and last retained chord parents match the original occurrence offset and count. -/
theorem retained_exterior_endpoint_positions
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorEndpointPositions
      prepared := by
  intro componentIndex component requested minimum comparison outer occurrence side mesh first last offset count
  let meshes := (prepared.paid.cut.exterior.prepared.energy.entries.get occurrence.sideOccurrence.sheet).meshes
  let intervals := SourceIntervals.axisIntervals mesh occurrence.sourceVertical
  let firstIndex := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side 0
  let lastIndex := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side (Fin.last
    (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side))
  have source := occurrence.source_span_endpoints
  have physical := Meshes.PuncturedGrid.Exterior.RetainedJunctions.SurfaceOccurrence.side_span_endpoints occurrence
    meshes
  apply first.side_positions last occurrence.sourceForward
    (retained_exterior_source_endpoints prepared componentIndex comparison outer) physical.1 physical.2
  · intro endpoint
    exact comparison.locateSideInterval_at_start outer meshes
      (intervals[firstIndex.val]'firstIndex.isLt) (List.getElem_mem firstIndex.isLt) (endpoint.trans source.1.symm)
  · intro endpoint
    exact comparison.locateSideInterval_at_start outer meshes
      (intervals[lastIndex.val]'lastIndex.isLt) (List.getElem_mem lastIndex.isLt) (endpoint.trans source.1.symm)
  · intro endpoint
    exact comparison.locateSideInterval_at_finish outer meshes
      (intervals[firstIndex.val]'firstIndex.isLt) (List.getElem_mem firstIndex.isLt) (endpoint.trans source.2.symm)
  · intro endpoint
    exact comparison.locateSideInterval_at_finish outer meshes
      (intervals[lastIndex.val]'lastIndex.isLt) (List.getElem_mem lastIndex.isLt) (endpoint.trans source.2.symm)

/-- A finite natural-number walk with upward steps at most one visits every value between its endpoints. -/
private theorem increasing_walk_covers {n : Nat} (values : Fin (n + 1) → Nat)
    (steps : ∀ i : Fin n, values i.succ ≤ values i.castSucc + 1)
    {target : Nat} (lower : values 0 ≤ target) (upper : target ≤ values (Fin.last n)) :
    ∃ i, values i = target := by
  induction n with
  | zero => exact ⟨0, Nat.le_antisymm lower upper⟩
  | succ n ih =>
    if before : target ≤ values (Fin.last n).castSucc then
      obtain ⟨i, equal⟩ := ih (fun i => values i.castSucc) (fun i => steps i.castSucc) lower before
      exact ⟨i.castSucc, equal⟩
    else
      have after := Nat.succ_le_of_lt (Nat.lt_of_not_ge before)
      exact ⟨Fin.last (n + 1), Nat.le_antisymm ((steps (Fin.last n)).trans after) upper⟩

/-- A finite natural-number walk with downward steps at most one visits every value between its endpoints. -/
private theorem decreasing_walk_covers {n : Nat} (values : Fin (n + 1) → Nat)
    (steps : ∀ i : Fin n, values i.castSucc ≤ values i.succ + 1)
    {target : Nat} (lower : target ≤ values 0) (upper : values (Fin.last n) ≤ target) :
    ∃ i, values i = target := by
  induction n with
  | zero => exact ⟨0, Nat.le_antisymm upper lower⟩
  | succ n ih =>
    if before : values (Fin.last n).castSucc ≤ target then
      obtain ⟨i, equal⟩ := ih (fun i => values i.castSucc) (fun i => steps i.castSucc) lower before
      exact ⟨i.castSucc, equal⟩
    else
      have after := Nat.succ_le_of_lt (Nat.lt_of_not_ge before)
      exact ⟨Fin.last (n + 1), Nat.le_antisymm upper
        (Nat.le_of_succ_le_succ (after.trans (steps (Fin.last n))))⟩

/-- A finite oriented walk with stationary or unit steps covers every original index between its retained endpoints. -/
private theorem oriented_walk_covers {n : Nat} (values : Fin (n + 1) → Nat) (forward : Bool)
    {offset count : Nat}
    (steps : ∀ i : Fin n, values i.succ = values i.castSucc ∨
      if forward then values i.succ = values i.castSucc + 1 else values i.castSucc = values i.succ + 1)
    (endpoints : if forward then values 0 = offset ∧ values (Fin.last n) + 1 = offset + count
      else values (Fin.last n) = offset ∧ values 0 + 1 = offset + count)
    (parent : Fin count) : ∃ i, values i = offset + parent.val := by
  have lower := Nat.le_add_right offset parent.val
  have upper := Nat.add_lt_add_left parent.isLt offset
  cases forward with
  | true =>
    apply increasing_walk_covers values _ (endpoints.1.trans_le lower)
      (Nat.le_of_lt_succ (upper.trans_eq endpoints.2.symm))
    intro i
    rcases steps i with same | next
    · exact same.trans_le (Nat.le_succ _)
    · exact next.le
  | false =>
    apply decreasing_walk_covers values _ (Nat.le_of_lt_succ (upper.trans_eq endpoints.2.symm))
      (endpoints.1.trans_le lower)
    intro i
    rcases steps i with same | next
    · exact same.symm.trans_le (Nat.le_succ _)
    · exact next.le

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Every original parent in the retained exterior occurrence is the owner of some retained physical chord. -/
@[expose] def RetainedExteriorParentCoverage
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let side := occurrence.sideOccurrence.side
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
      occurrence.sideOccurrence.sheet).meshes.entries.get
      occurrence.sideOccurrence.position
    let offset := (Meshes.PuncturedGrid.Exterior.BoundaryParentLocation.occurrenceParents
      (component.prepared.occurrences.take outer.val)).length
    ∀ parent : Fin occurrence.compared.entered.cache.parents.length,
      ∃ i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side + 1),
        (retainedExteriorChord prepared componentIndex comparison outer
          (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i)).index.val =
            offset + parent.val

/-- Transport the stationary alternative of a bounded-index step to equality of its natural values. -/
private theorem step_values {count : Nat} {i j : Fin count} {step : Prop}
    (next : j = i ∨ step) : j.val = i.val ∨ step :=
  next.elim (fun same => Or.inl (congrArg Fin.val same)) Or.inr

open Purelib.Curves.Hyperelliptic in
/-- The original endpoint positions and no-skipping law make the retained chords cover every source parent. -/
theorem retained_exterior_parent_coverage
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorParentCoverage
      prepared := by
  intro componentIndex component requested minimum comparison outer occurrence side mesh offset parent
  apply oriented_walk_covers
    (fun i => (retainedExteriorChord prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i)).index.val)
        occurrence.sourceForward _
    (retained_exterior_endpoint_positions prepared componentIndex comparison outer) parent
  intro i
  exact step_values (retained_exterior_no_skipped_parents prepared componentIndex comparison outer i)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle in
/-- The exact ordered physical chords grouped into runs with a common original source parent.

The grouping retains the original comparison, oriented side, physical intervals and source-chord records in bounded
physical-mesh order. -/
@[expose] def RetainedExteriorSourceGrouping
    (prepared : BoundaryPreparation preparation first second target radius floor) : Type _ :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let side := occurrence.sideOccurrence.side
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
      occurrence.sideOccurrence.sheet).meshes.entries.get
      occurrence.sideOccurrence.position
    let intervals := SourceIntervals.axisIntervals mesh occurrence.sourceVertical
    let chords := List.ofFn (fun i : Fin
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side + 1) =>
      let index := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i
      (⟨intervals[index.val]'index.isLt, retainedExteriorChord prepared componentIndex comparison outer index⟩ :
        Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord comparison occurrence.sourceVertical))
    Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordGrouping comparison occurrence.sourceVertical chords

open Purelib.Curves.Hyperelliptic in
/-- Group the exact retained exterior chords into their original source-parent runs. -/
@[expose] def retainedExteriorSourceGrouping
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorSourceGrouping
      prepared := by
  intro componentIndex component requested minimum comparison outer occurrence side mesh intervals chords
  exact Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordGrouping.build chords

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Each retained run's increment total equals its exact original endpoint increment. -/
private def RetainedExteriorEndpointTotals
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let grouped := retainedExteriorSourceGrouping prepared componentIndex comparison outer
    (grouped.runs.map Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.values).map
      PairedIncrementArea.total =
      grouped.runs.map Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.endpointIncrement

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Integration.Path.Dyadic in
/-- Each retained run reads the original parent primitive along its exact cached parameter sequence. -/
@[expose] def RetainedExteriorRunSampling
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let grouped := retainedExteriorSourceGrouping prepared componentIndex comparison outer
    ∀ run ∈ grouped.runs, run.values = SourceListResampling.increments (comparison.sourceValues run.parent)
      (Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.firstParameter run.first.2.forward run.first.2.range)
      run.parameters

section
open Purelib.Curves.Hyperelliptic
/-- Physical chord junctions identify each retained run with its original source-parameter sampling. -/
theorem retained_exterior_run_sampling
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorRunSampling prepared
      := by
  intro componentIndex component requested minimum comparison outer grouped
  let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences outer
  apply grouped.sampling_ofFn
  intro i
  exact Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junction_interval
    ((prepared.traces.get occurrence.sideOccurrence.position).get occurrence.sideOccurrence.sheet)
      occurrence.sideOccurrence.side i

/-- The exact retained junction equations telescope every original run to its endpoint increment. -/
private theorem retained_exterior_endpoint_totals
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorEndpointTotals
      prepared := by
  intro componentIndex component requested minimum comparison outer grouped
  let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences outer
  apply grouped.totals_ofFn
  intro i
  exact Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junction_interval
    ((prepared.traces.get occurrence.sideOccurrence.position).get occurrence.sideOccurrence.sheet)
      occurrence.sideOccurrence.side i

end

open Purelib.Data.Rat in
/-- Rewrite the retained unit endpoints as the two explicit orientation-dependent anchors. -/
private theorem physical_source_anchors (forward : Bool) {first last : Fraction.Rational}
    (ends : if forward then first = 0 ∧ last = 1 else last = 0 ∧ first = 1) :
    first = (if forward then 0 else 1) ∧ last = (if forward then 1 else 0) := by
  cases forward with
  | true => exact ends
  | false => exact ⟨ends.2, ends.1⟩

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Every retained source-parent run covers its full original oriented unit interval. -/
@[expose] def RetainedExteriorRunEndpoints
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let grouped := retainedExteriorSourceGrouping prepared componentIndex comparison outer
    ∀ run ∈ grouped.runs, run.FullEndpoints occurrence.sourceForward

open Purelib.Curves.Hyperelliptic in
/-- Original exterior endpoints and cross-parent junctions give every retained run its full parent span. -/
theorem retained_exterior_run_endpoints
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorRunEndpoints
      prepared := by
  intro componentIndex component requested minimum comparison outer occurrence grouped
  let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
    occurrence.sideOccurrence.sheet).meshes.entries.get
    occurrence.sideOccurrence.position
  let side := occurrence.sideOccurrence.side
  have anchors := physical_source_anchors occurrence.sourceForward
    (retained_exterior_source_endpoints prepared componentIndex comparison outer)
  apply grouped.endpoints_ofFn occurrence.sourceForward _ anchors.1 anchors.2
  intro i different
  let before := retainedExteriorChord prepared componentIndex comparison outer
    (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i.castSucc)
  let after := retainedExteriorChord prepared componentIndex comparison outer
    (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i.succ)
  have consecutive := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junction_interval
    ((prepared.traces.get occurrence.sideOccurrence.position).get occurrence.sideOccurrence.sheet) side i
  have separated := retained_exterior_parent_separation prepared componentIndex comparison outer i different
  exact before.cross_parent_endpoints after occurrence.sourceForward rfl rfl consecutive separated

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Integration.Path.Dyadic in
open Purelib.Integration.Path.Resampling in
/-- Each retained run is an oriented unit-interval sampling chain at the original physical mesh width.

Its exact increment list, endpoint chain and dyadic width bound all refer to the same original parent and retained
parameter sequence. -/
@[expose] def RetainedExteriorRunMesh
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
      occurrence.sideOccurrence.sheet).meshes.entries.get
      occurrence.sideOccurrence.position
    let grouped := retainedExteriorSourceGrouping prepared componentIndex comparison outer
    ∀ run ∈ grouped.runs,
    let parameters := run.parameters.map
      (OrientedBounds.orientParameter occurrence.sourceForward)
    let values := fun parameter => comparison.sourceValues run.parent
      (OrientedBounds.orientParameter occurrence.sourceForward parameter)
    run.values = SourceListResampling.increments values 0 parameters ∧
      SourceResampling.Chain 0 parameters 1 ∧
        SourceResampling.widths 0 parameters ((1 / 2 : Fraction.Rational)^mesh.depth)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- The retained run sampling and endpoint certificates form the original dyadic-width source mesh. -/
theorem retained_exterior_run_mesh
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorRunMesh prepared :=
      by
  intro componentIndex component requested minimum comparison outer occurrence mesh grouped run member parameters values
  have bounds := grouped.parameter_bounds_ofFn
    (fun i => Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junction_interval
      ((prepared.traces.get occurrence.sideOccurrence.position).get occurrence.sideOccurrence.sheet)
        occurrence.sideOccurrence.side i)
    occurrence.sourceForward (width := (1 / 2 : Fraction.Rational)^mesh.depth) (fun _ => ⟨rfl, le_rfl⟩) run member
  have ends := retained_exterior_run_endpoints prepared componentIndex comparison outer run member
  have sampling := retained_exterior_run_sampling prepared componentIndex comparison outer run member
  exact run.sampling_mesh occurrence.sourceForward sampling bounds ends

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Each original run's area differs from its retained source reference by the prescribed squared error bound.

The bound keeps the maximum of the original density-scaled physical mesh error and that parent's retained reference
error. -/
@[expose] def RetainedExteriorRunResampling
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
      occurrence.sideOccurrence.sheet).meshes.entries.get
      occurrence.sideOccurrence.position
    let grouped := retainedExteriorSourceGrouping prepared componentIndex comparison outer
    ∀ run ∈ grouped.runs,
      Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area run.values - comparison.sourceReferenceArea
        occurrence.sourceForward run.parent) ≤
        max (16 * (comparison.sourceDensity run.parent)^2 * ((1 / 2 : Fraction.Rational)^mesh.depth)^2)
          (comparison.entries.get run.parent).referenceError

/-- The exact retained source mesh supplies the original per-run resampling estimate. -/
theorem retained_exterior_run_resampling
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorRunResampling
      prepared := by
  intro componentIndex component requested minimum comparison outer occurrence mesh grouped run member
  have sampled := retained_exterior_run_mesh prepared componentIndex comparison outer run member
  exact comparison.source_run_resampling occurrence.sourceForward run.parent run.values sampled.1 sampled.2.1
    sampled.2.2

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- The retained run parents equal the original occurrence's parent indices in source orientation. -/
@[expose] def RetainedExteriorRunOrder
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let grouped := retainedExteriorSourceGrouping prepared componentIndex comparison outer
    grouped.runs.map Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.parent =
      if occurrence.sourceForward then comparison.parentIndices outer else (comparison.parentIndices outer).reverse

open Purelib.Curves.Hyperelliptic in
/-- The original no-skipping and endpoint-index laws identify the exact retained run-parent order. -/
theorem retained_exterior_run_order
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorRunOrder prepared :=
      by
  intro componentIndex component requested minimum comparison outer occurrence grouped
  let offset := (Meshes.PuncturedGrid.Exterior.BoundaryParentLocation.occurrenceParents
    (component.prepared.occurrences.take outer.val)).length
  let count := occurrence.compared.entered.cache.parents.length
  have order := grouped.parent_order_ofFn occurrence.sourceForward offset count
    (fun i => retained_exterior_no_skipped_parents prepared componentIndex comparison outer i)
    (retained_exterior_endpoint_positions prepared componentIndex comparison outer)
  exact grouped.parent_indices_order occurrence.sourceForward (comparison.parentIndices outer)
    (comparison.parentIndices_values outer) order

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- The retained run totals equal the original source-parent increments in the same oriented order. -/
@[expose] def RetainedExteriorRunTotals
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let grouped := retainedExteriorSourceGrouping prepared componentIndex comparison outer
    (grouped.runs.map Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.values).map
      PairedIncrementArea.total =
      (if occurrence.sourceForward then comparison.parentIndices outer else (comparison.parentIndices
        outer).reverse).map
        (Meshes.PuncturedGrid.Exterior.SourceChordRuns.sourceParentIncrement comparison occurrence.sourceForward)

/-- The full original run endpoints and exact parent order identify every retained total increment. -/
theorem retained_exterior_run_totals
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorRunTotals prepared
      := by
  intro componentIndex component requested minimum comparison outer occurrence grouped
  have totals := grouped.full_totals occurrence.sourceForward
    (retained_exterior_endpoint_totals prepared componentIndex comparison outer)
    (retained_exterior_run_endpoints prepared componentIndex comparison outer)
  exact totals.trans (grouped.parent_increments_order occurrence.sourceForward (comparison.parentIndices outer)
    (retained_exterior_run_order prepared componentIndex comparison outer))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- The retained chord area decomposes into run areas and original parent-increment area, with complete parent coverage.

The equality preserves the ordered source increments, while the separate coverage witness retains every original parent
in an actual grouped run. -/
@[expose] def RetainedExteriorSourceRegrouping
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let side := occurrence.sideOccurrence.side
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
      occurrence.sideOccurrence.sheet).meshes.entries.get
      occurrence.sideOccurrence.position
    let source := fun i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh
      side + 1) =>
      (retainedExteriorChord prepared componentIndex comparison outer
        (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i)).increments
    let grouped := retainedExteriorSourceGrouping prepared componentIndex comparison outer
    let blocks := grouped.runs.map Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.values
    let offset := (Meshes.PuncturedGrid.Exterior.BoundaryParentLocation.occurrenceParents
      (component.prepared.occurrences.take outer.val)).length
    PairedIncrementArea.area (List.ofFn source).flatten =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map PairedIncrementArea.area) +
        PairedIncrementArea.area
          ((if occurrence.sourceForward then comparison.parentIndices outer else (comparison.parentIndices
            outer).reverse).map
            (Meshes.PuncturedGrid.Exterior.SourceChordRuns.sourceParentIncrement comparison occurrence.sourceForward)) ∧
      ∀ parent : Fin occurrence.compared.entered.cache.parents.length,
        ∃ run ∈ grouped.runs, run.parent.val = offset + parent.val

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Regroup the exact retained chord area and certify that every original parent occurs in a run. -/
theorem retained_exterior_source_regrouping
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorSourceRegrouping
      prepared := by
  intro componentIndex component requested minimum comparison outer occurrence side mesh source grouped blocks offset
  constructor
  · exact grouped.area_ofFn.trans (congrArg (fun totals : List Stokes.PrimitivePoint =>
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map PairedIncrementArea.area) + PairedIncrementArea.area totals)
      (retained_exterior_run_totals prepared componentIndex comparison outer))
  · exact grouped.covers (retained_exterior_parent_coverage prepared componentIndex comparison outer)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- The original chord-versus-source area difference equals the difference of their exact block-area sums.

Both sides retain the original oriented source blocks and grouped run order, so their common parent-increment
contribution cancels exactly. -/
@[expose] def RetainedExteriorSourceAreaDifference
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let side := occurrence.sideOccurrence.side
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
      occurrence.sideOccurrence.sheet).meshes.entries.get
      occurrence.sideOccurrence.position
    let source := fun i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh
      side + 1) =>
      (retainedExteriorChord prepared componentIndex comparison outer
        (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i)).increments
    let grouped := retainedExteriorSourceGrouping prepared componentIndex comparison outer
    let blocks := grouped.runs.map Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.values
    let sourceBlocks := comparison.sourceOccurrenceBlocks outer occurrence.sourceForward
    PairedIncrementArea.area (List.ofFn source).flatten - PairedIncrementArea.area sourceBlocks.flatten =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map PairedIncrementArea.area) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (sourceBlocks.map PairedIncrementArea.area)

/-- The exact retained regrouping cancels the common original parent-increment area. -/
theorem retained_exterior_source_area_difference
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorSourceAreaDifference
      prepared := by
  intro componentIndex component requested minimum comparison outer occurrence side mesh source grouped blocks
    sourceBlocks
  exact comparison.source_area_difference outer occurrence.sourceForward blocks (List.ofFn source).flatten
    (retained_exterior_source_regrouping prepared componentIndex comparison outer).1

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- The retained block-area difference is bounded by the squared run count times the maximum original error.

The error list preserves each run's density-scaled physical mesh term and retained parent reference error under the same
original comparison. -/
@[expose] def RetainedExteriorSourceResamplingBound
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
      occurrence.sideOccurrence.sheet).meshes.entries.get
      occurrence.sideOccurrence.position
    let grouped := retainedExteriorSourceGrouping prepared componentIndex comparison outer
    let blocks := grouped.runs.map Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.values
    let sourceBlocks := comparison.sourceOccurrenceBlocks outer occurrence.sourceForward
    let errors := grouped.runs.map (fun run =>
      max (16 * (comparison.sourceDensity run.parent)^2 * ((1 / 2 : Fraction.Rational)^mesh.depth)^2)
        (comparison.entries.get run.parent).referenceError)
    let error := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum id errors
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map PairedIncrementArea.area) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (sourceBlocks.map PairedIncrementArea.area)) ≤
        (grouped.runs.length : Fraction.Rational)^2 * error

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.List in
open Purelib.Data.Rat in
/-- The original per-run resampling bounds control the complete retained block-area difference.

Exact run-parent order identifies the source blocks, and the maximum of the retained error list pays the squared
finite-sum count. -/
theorem retained_exterior_source_resampling_bound
    (prepared : BoundaryPreparation preparation first second target radius floor) :
      RetainedExteriorSourceResamplingBound prepared := by
  intro componentIndex component requested minimum comparison outer occurrence mesh grouped blocks sourceBlocks errors
    error
  apply comparison.source_runs_resampling_bound outer occurrence.sourceForward grouped.runs
    (retained_exterior_run_order prepared componentIndex comparison outer)
  intro run member
  have paid := retained_exterior_run_resampling prepared componentIndex comparison outer run member
  have present : max (16 * (comparison.sourceDensity run.parent)^2 * ((1 / 2 : Fraction.Rational)^mesh.depth)^2)
      (comparison.entries.get run.parent).referenceError ∈ errors :=
    Map.mem_map_of_mem member
  exact paid.trans (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum id present)

end Purelib.Riemann.RootContinuation.NewtonRetainedExteriorSources
