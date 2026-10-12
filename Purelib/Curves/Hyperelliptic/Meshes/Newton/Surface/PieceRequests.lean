module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CrossFaceSides
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Riemann.Integration.RectangularEndpointPieceOrigins
import Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
public import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceOrigins
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointTraceHandoffs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.ConjugateEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.PairedEndpointPolygon
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointTraceHandoffs

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.ConjugateEnergy.MatchedSidePreparation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy.MatchedVerticalSidePreparation

open Purelib.Data.Rat

open Purelib.Riemann.Integration.RectangularEndpointPieceOrigins

open Purelib.Riemann.Paths

@[expose] public section

/-! Piece requests inherit the common root from the retained endpoint path
bank. No additional incoming owner or piece-origin certificate is supplied. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Topology.NewtonObservationSurfacePartition (SurfacePartition)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces (HorizontalPieces VerticalPieces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceOrigins
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (PiecePerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)

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
  {first last : Fin grid.faces.regulars.length}
  {start : Purelib.Data.Gaussian.Basic.Canonical} {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    (curve.polynomial.eval start)}
  (firstEntry : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (domains.get
    first).models start owner)
  (lastEntry : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (domains.get last).models
    start owner)
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {error :
    Purelib.Data.Rat.Fraction.Rational}

variable (requests : Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests
  (fun sheet => Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains
    surfaceCuts sheet coarseDepth) fixed error)

variable
  (firstTraces : Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.PiecePerimeterTraces
    (requests.entries.get firstEntry.sheet) first)
  (lastTraces : Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.PiecePerimeterTraces
    (requests.entries.get lastEntry.sheet) last)

/-- Prepare the actual original horizontal piece comparison from its retained endpoint polygon contact.

The original shared root and piece origin are inherited from that bank, and the request pays both synchronized surface
stages and the supplied floor. -/
def horizontalPieceRequest {count : Nat}
    (pieces : Fin (count + 1) → BoundaryPieces.HorizontalPieces (partitions.get first) (partitions.get last))
    (endpoints : PuncturedGrid.EndpointPolygonPreparation (leftEntry := firstEntry) (rightEntry :=
      lastEntry)
      (EndpointGeometry.horizontalPieces firstTraces lastTraces pieces))
    (piece : Fin (count + 1))
    (trace : (CrossFaceSides.horizontalFaceSide (requests.entries.get firstEntry.sheet) (requests.entries.get
      lastEntry.sheet)
      first last (pieces piece).firstPiece (pieces piece).lastPiece
      (pieces piece).lower_eq (pieces piece).upper_eq (pieces piece).joined).Trace requests.depth)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat) :=
  let vertex := VertexTrace.pairedEndpointStart
    (fun index => RectangularOwnedPerimeterTraces.topOwned (firstTraces.get (pieces index).firstPiece))
    (fun index => RectangularOwnedPerimeterTraces.bottomOwned (lastTraces.get (pieces index).lastPiece)) piece
  let contact := EndpointPolygonPreparation.horizontalAt endpoints vertex trace
    (EndpointGeometry.horizontalPiece_origin firstTraces lastTraces pieces piece trace)
  EnergyRequest.build contact allowance positive (max requests.index floor)

/-- Prepare the actual original vertical piece comparison from its retained endpoint polygon contact.

The original shared root and piece origin are inherited from that bank, and the request pays both synchronized surface
stages and the supplied floor. -/
def verticalPieceRequest {count : Nat}
    (pieces : Fin (count + 1) → BoundaryPieces.VerticalPieces (partitions.get first) (partitions.get last))
    (endpoints : PuncturedGrid.EndpointPolygonPreparation (leftEntry := firstEntry) (rightEntry :=
      lastEntry)
      (EndpointGeometry.verticalPieces firstTraces lastTraces pieces))
    (piece : Fin (count + 1))
    (trace : (CrossFaceSides.verticalFaceSide (requests.entries.get firstEntry.sheet) (requests.entries.get
      lastEntry.sheet)
      first last (pieces piece).firstPiece (pieces piece).lastPiece
      (pieces piece).lower_eq (pieces piece).upper_eq (pieces piece).joined).Trace requests.depth)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat) :=
  let vertex := VertexTrace.pairedEndpointStart
    (fun index => RectangularOwnedPerimeterTraces.rightOwned (firstTraces.get (pieces index).firstPiece))
    (fun index => RectangularOwnedPerimeterTraces.leftOwned (lastTraces.get (pieces index).lastPiece)) piece
  let contact := EndpointPolygonPreparation.verticalAt endpoints vertex trace
    (EndpointGeometry.verticalPiece_origin firstTraces lastTraces pieces piece trace)
  EnergyRequest.build contact allowance positive (max requests.index floor)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceRequests
