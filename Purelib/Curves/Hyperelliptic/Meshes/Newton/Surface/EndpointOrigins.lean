module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.PairedEndpointPolygon
import Purelib.Riemann.Integration.RectangularExteriorCornerOwners
import Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Readings.RectangularPairedEndpointReadings
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry

open Purelib.Geometry.Rectangle.Partition

open Purelib.Integration.Path

open Purelib.Integration.Path.JoinedTrace

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! Endpoint-polygon requests begin at the retained outer face corner. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointOrigins

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open Purelib.Riemann.Topology.NewtonObservationSurfacePartition (SurfacePartition)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces (HorizontalPieces VerticalPieces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (PiecePerimeterTraces)
open Purelib.Riemann.Readings.RectangularPairedEndpointReadings (PairedEndpointReadingsGeometry)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational} {grid :
    Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {observations : Purelib.Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    grid.faces.regulars} {partitions : Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions
    observations grid}
  {surfaceCuts : Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains}
  {firstSheet lastSheet : Fin 2} {firstDepth lastDepth : Nat}
  {firstFixed : Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains firstSheet}
    {lastFixed : Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains lastSheet}
  {firstError lastError : Purelib.Data.Rat.Fraction.Rational}

variable {firstRequest : Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions
  (Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
  firstSheet firstDepth) firstFixed firstError}
  {lastRequest : Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions
    (Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
    lastSheet lastDepth) lastFixed lastError}
  {first last : Fin grid.faces.regulars.length}
  (firstTraces : Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.PiecePerimeterTraces firstRequest
    first) (lastTraces : Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.PiecePerimeterTraces
    lastRequest last)

namespace EndpointGeometry

/-- The original paired horizontal endpoint polygon starts at the retained upper-left corner of the first complete face.
-/
theorem horizontal_origin
    (equal : (partitions.get first).cuts.x.intervals = (partitions.get last).cuts.x.intervals)
    (adjacent : (grid.faces.regulars[first.val]'first.isLt).cell.box.yUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.yLower) :
    (EndpointGeometry.horizontalPieces firstTraces lastTraces (HorizontalPieces.build _ _ equal adjacent)).points 0 =
      PreparedRectangleCuts.corner (grid.faces.regulars[first.val]'first.isLt).cell.box false true := by
  let geometry := EndpointGeometry.horizontalPieces firstTraces lastTraces (HorizontalPieces.build _ _ equal adjacent)
  rw [← geometry.left_point 0, geometry.left_eq 0]
  dsimp only [VertexTrace.indexed, Dyadic.DyadicTrace.indexed]
  rw [PairedEndpointPolygon.pairedEndpointPolygon, VertexTrace.concatenate, VertexTrace.glue_first]
  change (RectangularOwnedPerimeterTraces.topOwned (firstTraces.get (PieceIndices.pieceIndex (partitions.get first) 0
    (Fin.last (PieceIndices.rows (partitions.get first)))))).first.point = _
  have endpoint := congrArg PrimitivePoint.left
    ((RectangularOwnedPerimeterTraces.topOwned_first (firstTraces.get (PieceIndices.pieceIndex (partitions.get first) 0
      (Fin.last (PieceIndices.rows (partitions.get first))))))
      (fun _ _ point => ⟨point, 0⟩))
  dsimp only at endpoint
  rw [endpoint, RectangularExteriorCornerOwners.exteriorCornerOwner_point, PieceIndices.piece_box (partitions.get
    first)]
  apply Data.Gaussian.Basic.ext
  · exact (partitions.get first).cuts.x.first_lower (Fin.cast (PieceIndices.columns_eq (partitions.get first)) 0).isLt
  · exact (partitions.get first).cuts.y.last_upper _ (PieceIndices.rows_eq (partitions.get first))

/-- The original paired vertical endpoint polygon starts at the retained lower-right corner of the first complete face.
-/
theorem vertical_origin
    (equal : (partitions.get first).cuts.y.intervals = (partitions.get last).cuts.y.intervals)
    (adjacent : (grid.faces.regulars[first.val]'first.isLt).cell.box.xUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.xLower) :
    (EndpointGeometry.verticalPieces firstTraces lastTraces (VerticalPieces.build _ _ equal adjacent)).points 0 =
      PreparedRectangleCuts.corner (grid.faces.regulars[first.val]'first.isLt).cell.box true false := by
  let geometry := EndpointGeometry.verticalPieces firstTraces lastTraces (VerticalPieces.build _ _ equal adjacent)
  rw [← geometry.left_point 0, geometry.left_eq 0]
  dsimp only [VertexTrace.indexed, Dyadic.DyadicTrace.indexed]
  rw [PairedEndpointPolygon.pairedEndpointPolygon, VertexTrace.concatenate, VertexTrace.glue_first]
  change (RectangularOwnedPerimeterTraces.rightOwned (firstTraces.get (PieceIndices.pieceIndex (partitions.get first)
    (Fin.last (PieceIndices.columns (partitions.get first))) 0))).first.point = _
  have endpoint := congrArg PrimitivePoint.left
    ((RectangularOwnedPerimeterTraces.rightOwned_first (firstTraces.get (PieceIndices.pieceIndex (partitions.get first)
      (Fin.last (PieceIndices.columns (partitions.get first))) 0)))
      (fun _ _ point => ⟨point, 0⟩))
  dsimp only at endpoint
  rw [endpoint, RectangularExteriorCornerOwners.exteriorCornerOwner_point, PieceIndices.piece_box (partitions.get
    first)]
  apply Data.Gaussian.Basic.ext
  · exact (partitions.get first).cuts.x.last_upper _ (PieceIndices.columns_eq (partitions.get first))
  · exact (partitions.get first).cuts.y.first_lower (Fin.cast (PieceIndices.rows_eq (partitions.get first)) 0).isLt

end EndpointGeometry
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointOrigins
