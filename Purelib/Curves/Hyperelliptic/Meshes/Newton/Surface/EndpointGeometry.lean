module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Integration.RectangularExteriorCornerOwners
import Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces
public import Purelib.Riemann.Readings.RectangularPairedEndpointReadings
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularPairedEndpointReadings

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! Shared endpoint coordinates for the actual outer piece perimeters of
adjacent complete surface faces. All original model owners are retained. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry

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
open Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces

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

section EndpointGeometry

/-- Pair the actual top and bottom piece-trace endpoints using the original matching horizontal cut coordinates. -/
def horizontalPieces {count : Nat}
    (pieces : Fin (count + 1) → BoundaryPieces.HorizontalPieces (partitions.get first) (partitions.get last)) :
    RectangularPairedEndpointReadings.PairedEndpointReadingsGeometry
      (fun index => (RectangularOwnedPerimeterTraces.topOwned (firstTraces.get (pieces index).firstPiece)))
      (fun index => (RectangularOwnedPerimeterTraces.bottomOwned (lastTraces.get (pieces index).lastPiece))) := by
  apply PairedEndpointReadingsGeometry.build
  · intro index
    have leftEq := congrArg PrimitivePoint.left
      ((RectangularOwnedPerimeterTraces.topOwned_first (firstTraces.get (pieces index).firstPiece)) (fun _ _ point =>
        ⟨point, 0⟩))
    have rightEq := congrArg PrimitivePoint.left
      ((RectangularOwnedPerimeterTraces.bottomOwned_first (lastTraces.get (pieces index).lastPiece)) (fun _ _ point =>
        ⟨point, 0⟩))
    dsimp only at leftEq rightEq
    rw [leftEq, rightEq, RectangularExteriorCornerOwners.exteriorCornerOwner_point,
      RectangularExteriorCornerOwners.exteriorCornerOwner_point]
    apply Data.Gaussian.Basic.ext
    · exact (pieces index).lower_eq
    · exact (pieces index).joined
  · intro index
    have leftEq := congrArg PrimitivePoint.left
      ((RectangularOwnedPerimeterTraces.topOwned_last (firstTraces.get (pieces index).firstPiece)) (fun _ _ point =>
        ⟨point, 0⟩))
    have rightEq := congrArg PrimitivePoint.left
      ((RectangularOwnedPerimeterTraces.bottomOwned_last (lastTraces.get (pieces index).lastPiece)) (fun _ _ point =>
        ⟨point, 0⟩))
    dsimp only at leftEq rightEq
    rw [leftEq, rightEq, RectangularExteriorCornerOwners.exteriorCornerOwner_point,
      RectangularExteriorCornerOwners.exteriorCornerOwner_point]
    apply Data.Gaussian.Basic.ext
    · exact (pieces index).upper_eq
    · exact (pieces index).joined

/-- Pair the actual right and left piece-trace endpoints using the original matching vertical cut coordinates. -/
def verticalPieces {count : Nat}
    (pieces : Fin (count + 1) → BoundaryPieces.VerticalPieces (partitions.get first) (partitions.get last)) :
    RectangularPairedEndpointReadings.PairedEndpointReadingsGeometry
      (fun index => (RectangularOwnedPerimeterTraces.rightOwned (firstTraces.get (pieces index).firstPiece)))
      (fun index => (RectangularOwnedPerimeterTraces.leftOwned (lastTraces.get (pieces index).lastPiece))) := by
  apply PairedEndpointReadingsGeometry.build
  · intro index
    have leftEq := congrArg PrimitivePoint.left
      ((RectangularOwnedPerimeterTraces.rightOwned_first (firstTraces.get (pieces index).firstPiece)) (fun _ _ point =>
        ⟨point, 0⟩))
    have rightEq := congrArg PrimitivePoint.left
      ((RectangularOwnedPerimeterTraces.leftOwned_first (lastTraces.get (pieces index).lastPiece)) (fun _ _ point =>
        ⟨point, 0⟩))
    dsimp only at leftEq rightEq
    rw [leftEq, rightEq, RectangularExteriorCornerOwners.exteriorCornerOwner_point,
      RectangularExteriorCornerOwners.exteriorCornerOwner_point]
    apply Data.Gaussian.Basic.ext
    · exact (pieces index).joined
    · exact (pieces index).lower_eq
  · intro index
    have leftEq := congrArg PrimitivePoint.left
      ((RectangularOwnedPerimeterTraces.rightOwned_last (firstTraces.get (pieces index).firstPiece)) (fun _ _ point =>
        ⟨point, 0⟩))
    have rightEq := congrArg PrimitivePoint.left
      ((RectangularOwnedPerimeterTraces.leftOwned_last (lastTraces.get (pieces index).lastPiece)) (fun _ _ point =>
        ⟨point, 0⟩))
    dsimp only at leftEq rightEq
    rw [leftEq, rightEq, RectangularExteriorCornerOwners.exteriorCornerOwner_point,
      RectangularExteriorCornerOwners.exteriorCornerOwner_point]
    apply Data.Gaussian.Basic.ext
    · exact (pieces index).joined
    · exact (pieces index).upper_eq

end EndpointGeometry
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry
