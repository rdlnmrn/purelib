module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularPointReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SharedPointReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularMatchedObservationSides

@[expose] public section

/-! Reuse Newton face-cache readings in common-basis physical fragments. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedReadings
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (OwnedReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}

open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

/-- Use the same face, sheet and numerical stage as the Newton mesh. -/
def sharedRowData (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential)
    {stage : Nat} (cache : RegularMeshes.Numerics domains stage) : FragmentQueries.RowData occurrence stage :=
  fun row => (occurrence.recastComparison (PeriodMatrix.standardDifferential row)).sharedData
    (cache.get row) (occurrence.recastComparison_aligned (PeriodMatrix.standardDifferential row))

/-- Original physical point owners, before transport into the occurrence. -/
def CachedReadings {stage vertices : Nat} (cache : RegularMeshes.Numerics domains stage) (points : Fin vertices →
  InverseRootPolynomial.Gaussian) :=
  (row : Fin genus) → RectangularPointReadings.PointReadings
    (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet row).anchors
    (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet row).offsets points

/-- Transport all rows together, preserving each retained numerical value. -/
def sharedOwnedReadings {stage vertices : Nat} (cache : RegularMeshes.Numerics domains stage) {points : Fin vertices →
  InverseRootPolynomial.Gaussian}
    (original : CachedReadings (occurrence :=
      occurrence) cache points) :
    {readings : OwnerRequest.OwnedReadings
      (sharedRowData occurrence cache) points //
      ∀ row vertex, (readings row).values vertex = (original row).values vertex} := by
  let transported := fun row =>
    (occurrence.recastComparison (PeriodMatrix.standardDifferential row)).sharedReadings
      (cache.get row) (occurrence.recastComparison_aligned (PeriodMatrix.standardDifferential row)) (original row)
  exact ⟨fun row => (transported row).val,
    fun row vertex => congrArg (fun values => values vertex) (transported row).property⟩

open Purelib.Riemann.Normalization.RectangularInverseModels
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
variable {cuts : GridCuts ((domains.get
  occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).geometry}
  {meshBox : Purelib.Geometry.Rational.Box} {mesh :
    ObservationMesh cuts meshBox} {depth stage : Nat}

/-- Read the actual horizontal side trace, retaining both owners at each junction in its indexed vertex list. -/
def horizontalReadings {firstRow secondRow : Fin mesh.partition.y.intervals.length}
    {height : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedHorizontalSide mesh mesh firstRow
      secondRow height}
    (trace : side.Trace depth) (cache : RegularMeshes.Numerics domains stage) :
    OwnerRequest.OwnedReadings (sharedRowData
      occurrence cache)
      (fun vertex => trace.point (trace.vertices.indexed vertex)) :=
  (sharedOwnedReadings cache (fun row =>
    trace.leftReadings
    (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet row).anchors
    (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet row).offsets)).val

/-- The vertical boundary uses the same shared bank and owner-preserving transport. -/
def verticalReadings {firstColumn secondColumn : Fin mesh.partition.x.intervals.length}
    {width : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedVerticalSide mesh mesh firstColumn
      secondColumn width}
    (trace : side.Trace depth) (cache : RegularMeshes.Numerics domains stage) :
    OwnerRequest.OwnedReadings (sharedRowData
      occurrence cache)
      (fun vertex => trace.point (trace.vertices.indexed vertex)) :=
  (sharedOwnedReadings cache (fun row =>
    trace.leftReadings
    (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet row).anchors
    (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet row).offsets)).val

/-- Scalar row readback for the actual shared side bank, before weighting. -/
theorem horizontalReadings_row {firstRow secondRow : Fin mesh.partition.y.intervals.length}
    {height : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedHorizontalSide mesh mesh firstRow
      secondRow height}
    (trace : side.Trace depth) (cache : RegularMeshes.Numerics domains stage)
    (row : Fin genus) (vertex : Fin (trace.vertices.rest.length + 1)) :
    (horizontalReadings (occurrence :=
      occurrence) trace cache row).values vertex =
      SharedPhysicalHorizontalReadings.secondValue (occurrence := occurrence) trace
        (cache.get row) (trace.vertices.indexed vertex) := by
  exact ((sharedOwnedReadings cache (fun
    basisRow => trace.leftReadings
    (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet basisRow).anchors
    (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet basisRow).offsets)).property row
      vertex).trans
      (trace.leftReadings_value
        (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet row).anchors
        (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet row).offsets vertex)

/-- Scalar row readback for the actual shared side bank, before weighting. -/
theorem verticalReadings_row {firstColumn secondColumn : Fin mesh.partition.x.intervals.length}
    {width : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedVerticalSide mesh mesh firstColumn
      secondColumn width}
    (trace : side.Trace depth) (cache : RegularMeshes.Numerics domains stage)
    (row : Fin genus) (vertex : Fin (trace.vertices.rest.length + 1)) :
    (verticalReadings (occurrence := occurrence)
      trace cache row).values vertex =
      SharedPhysicalVerticalReadings.secondValue (occurrence := occurrence) trace
        (cache.get row) (trace.vertices.indexed vertex) := by
  exact ((sharedOwnedReadings cache (fun
    basisRow => trace.leftReadings
    (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet basisRow).anchors
    (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet basisRow).offsets)).property row
      vertex).trans
      (trace.leftReadings_value
        (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet row).anchors
        (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet row).offsets vertex)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedReadings
