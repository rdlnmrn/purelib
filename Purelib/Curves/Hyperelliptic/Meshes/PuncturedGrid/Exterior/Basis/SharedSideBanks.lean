module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedReadings
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
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
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples

open Purelib.Data.Vector

@[expose] public section
/-! Retain shared numerical owners once before assembling physical side groups. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (OwnedReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedReadings (sharedRowData horizontalReadings
  horizontalReadings_row verticalReadings verticalReadings_row)
open Purelib.Riemann.Normalization
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

open Purelib.Riemann.Normalization.RectangularInverseModels
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
variable {stage depth : Nat}
  {cuts : GridCuts ((domains.get
    occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).geometry}
  {meshBox : Purelib.Geometry.Rational.Box} {mesh :
    ObservationMesh cuts meshBox}

namespace SharedHorizontalBank
variable {firstRow secondRow : Fin mesh.partition.y.intervals.length}
  {height : Coordinate} {side :
    MatchedHorizontalSide mesh mesh firstRow
    secondRow height}
  (trace : side.Trace depth) (cache :
    Numerics domains stage)

/-- Read the original shared numerical bank's basis-row value at the retained horizontal side vertex. -/
def values (row : Fin genus) (vertex : side.Vertex depth) : Gaussian :=
  SharedPhysicalHorizontalReadings.secondValue (occurrence := occurrence) trace (cache.get row) vertex

/-- The complete original basis-row owner readings on the retained horizontal trace. -/
def Readings (data : FragmentQueries.RowData occurrence stage) :=
  OwnerRequest.OwnedReadings data (fun vertex => trace.point (trace.vertices.indexed vertex))

/-- The row-data owner is exactly the one transported from the original shared numerical cache. -/
def CanonicalData (data : FragmentQueries.RowData occurrence stage) : Prop := data = SharedReadings.sharedRowData
  occurrence cache

/-- Every retained owner reading equals its original cached basis-row value at the same indexed trace vertex. -/
def Readback {data : FragmentQueries.RowData occurrence stage} (readings :
  Readings trace data) :
  Prop :=
  ∀ row vertex, (readings row).values vertex =
    values trace cache row
    (trace.vertices.indexed vertex)

set_option genInjectivity false in
/-- Cache the transported numerical owner bank together with its exact origin and scalar readbacks. Weighted samples
consume the retained values directly, without acquiring the primitives again. -/
structure Data where
  /-- The retained basis-row face-data owner. -/ data : FragmentQueries.RowData occurrence stage
  /-- The retained row-data owner is the exact transported original numerical cache. -/ data_eq :
    CanonicalData cache
    data
  /-- The retained complete bank of original basis-row owner readings. -/ readings :
    Readings trace data
  /-- Each retained scalar reading equals its exact original cached value. -/ readback :
    Readback trace cache
    readings

constructive_injectivity Data

/-- Cache the transported original horizontal row-reading bank once with its exact owner and scalar readback
certificates. -/
def build : Data trace
  cache := by
  let rows := DependentVector.ofFn (SharedReadings.horizontalReadings (occurrence := occurrence) trace cache)
  refine ⟨sharedRowData occurrence cache, rfl, (fun row => rows.get row), ?_⟩
  intro row vertex
  have retained := DependentVector.ofFn_get (SharedReadings.horizontalReadings (occurrence := occurrence) trace cache)
    row
  exact (congrArg (fun reading => reading.values vertex) retained).trans
    (SharedReadings.horizontalReadings_row trace cache row vertex)

end SharedHorizontalBank

namespace SharedVerticalBank
variable {firstColumn secondColumn : Fin mesh.partition.x.intervals.length}
  {width : Coordinate} {side :
    MatchedVerticalSide mesh mesh
    firstColumn secondColumn width}
  (trace : side.Trace depth) (cache :
    Numerics domains stage)

/-- Read the original shared numerical bank's basis-row value at the retained vertical side vertex. -/
def values (row : Fin genus) (vertex : side.Vertex depth) : Gaussian :=
  SharedPhysicalVerticalReadings.secondValue (occurrence := occurrence) trace (cache.get row) vertex

/-- The complete original basis-row owner readings on the retained vertical trace. -/
def Readings (data : FragmentQueries.RowData occurrence stage) :=
  OwnerRequest.OwnedReadings data (fun vertex => trace.point (trace.vertices.indexed vertex))

/-- The row-data owner is exactly the one transported from the original shared numerical cache. -/
def CanonicalData (data : FragmentQueries.RowData occurrence stage) : Prop := data = SharedReadings.sharedRowData
  occurrence cache

/-- Every retained owner reading equals its original cached basis-row value at the same indexed trace vertex. -/
def Readback {data : FragmentQueries.RowData occurrence stage} (readings :
  Readings trace data) :
  Prop :=
  ∀ row vertex, (readings row).values vertex =
    values trace cache row
    (trace.vertices.indexed vertex)

set_option genInjectivity false in
/-- Cache the transported numerical owner bank together with its exact origin and scalar readbacks. Weighted samples
consume the retained values directly, without acquiring the primitives again. -/
structure Data where
  /-- The retained basis-row face-data owner. -/ data : FragmentQueries.RowData occurrence stage
  /-- The retained row-data owner is the exact transported original numerical cache. -/ data_eq :
    CanonicalData cache data
  /-- The retained complete bank of original basis-row owner readings. -/ readings :
    Readings trace data
  /-- Each retained scalar reading equals its exact original cached value. -/ readback :
    Readback trace cache
    readings

constructive_injectivity Data

/-- Cache the transported original vertical row-reading bank once with its exact owner and scalar readback certificates.
-/
def build : Data trace cache
  := by
  let rows := DependentVector.ofFn (SharedReadings.verticalReadings (occurrence := occurrence) trace cache)
  refine ⟨sharedRowData occurrence cache, rfl, (fun row => rows.get row), ?_⟩
  intro row vertex
  have retained := DependentVector.ofFn_get (SharedReadings.verticalReadings (occurrence := occurrence) trace cache) row
  exact (congrArg (fun reading => reading.values vertex) retained).trans
    (SharedReadings.verticalReadings_row trace cache row vertex)

end SharedVerticalBank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks
