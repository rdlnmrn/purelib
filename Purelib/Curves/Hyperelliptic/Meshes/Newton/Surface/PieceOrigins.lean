module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Integration.RectangularMatchedCornerReadback
import Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CrossFaceSides
public import Purelib.Riemann.Integration.RectangularEndpointPieceOrigins
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.PairedEndpointPolygon
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularPairedEndpointReadings
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry

open Purelib.Riemann.Integration.RectangularEndpointPieceOrigins

open Purelib.Riemann.Integration.RectangularMatchedCornerReadback.MatchedHorizontalSide

open Purelib.Riemann.Integration.RectangularMatchedCornerReadback.MatchedVerticalSide

open Purelib.Riemann.Paths

open Purelib.Topology.Polygon.Stokes

public section

/-! Matched piece traces start at their exact retained endpoint-polygon
occurrences, allowing the cached common owner to seed every contact. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceOrigins

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

/-- The actual matched horizontal piece trace begins at its retained paired endpoint polygon origin.

The retained top-side trace and paired endpoint polygon read the same original first horizontal piece occurrence. -/
theorem horizontalPiece_origin {count depth : Nat}
    (pieces : Fin (count + 1) → BoundaryPieces.HorizontalPieces (partitions.get first) (partitions.get last))
    (piece : Fin (count + 1))
    (trace : (CrossFaceSides.horizontalFaceSide firstRequest lastRequest first last (pieces piece).firstPiece (pieces
      piece).lastPiece
      (pieces piece).lower_eq (pieces piece).upper_eq (pieces piece).joined).Trace depth) :
    trace.point (trace.vertices.indexed 0) =
      (EndpointGeometry.horizontalPieces firstTraces lastTraces pieces).points
        (VertexTrace.pairedEndpointStart
          (fun index => (RectangularOwnedPerimeterTraces.topOwned (firstTraces.get (pieces index).firstPiece)))
          (fun index => (RectangularOwnedPerimeterTraces.bottomOwned (lastTraces.get (pieces index).lastPiece))) piece)
            := by
  rw [PairedEndpointReadingsGeometry.pieceStart_point (EndpointGeometry.horizontalPieces firstTraces lastTraces pieces)]
  have traceCorner := congrArg PrimitivePoint.left
    (Trace.left_corner (above := true) trace (fun _ _ point => ⟨point, 0⟩) rfl false)
  have ownedCorner := congrArg PrimitivePoint.left
    ((RectangularOwnedPerimeterTraces.topOwned_first (firstTraces.get (pieces piece).firstPiece)) (fun _ _ point =>
      ⟨point, 0⟩))
  dsimp only at traceCorner
  exact traceCorner.trans ownedCorner.symm

/-- The actual matched vertical piece trace begins at its retained paired endpoint polygon origin.

The retained right-side trace and paired endpoint polygon read the same original first vertical piece occurrence. -/
theorem verticalPiece_origin {count depth : Nat}
    (pieces : Fin (count + 1) → BoundaryPieces.VerticalPieces (partitions.get first) (partitions.get last))
    (piece : Fin (count + 1))
    (trace : (CrossFaceSides.verticalFaceSide firstRequest lastRequest first last (pieces piece).firstPiece (pieces
      piece).lastPiece
      (pieces piece).lower_eq (pieces piece).upper_eq (pieces piece).joined).Trace depth) :
    trace.point (trace.vertices.indexed 0) =
      (EndpointGeometry.verticalPieces firstTraces lastTraces pieces).points
        (VertexTrace.pairedEndpointStart
          (fun index => (RectangularOwnedPerimeterTraces.rightOwned (firstTraces.get (pieces index).firstPiece)))
          (fun index => (RectangularOwnedPerimeterTraces.leftOwned (lastTraces.get (pieces index).lastPiece))) piece) :=
            by
  rw [PairedEndpointReadingsGeometry.pieceStart_point (EndpointGeometry.verticalPieces firstTraces lastTraces pieces)]
  have traceCorner := congrArg PrimitivePoint.left
    (Trace.left_corner (rightward := true) trace (fun _ _ point => ⟨point, 0⟩) rfl false)
  have ownedCorner := congrArg PrimitivePoint.left
    ((RectangularOwnedPerimeterTraces.rightOwned_first (firstTraces.get (pieces piece).firstPiece)) (fun _ _ point =>
      ⟨point, 0⟩))
  dsimp only at traceCorner
  exact traceCorner.trans ownedCorner.symm

end EndpointGeometry
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceOrigins
