module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry
public import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
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
import Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Readings.RectangularPairedEndpointReadings
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy.EndpointPolygonPreparation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonPreparation

open Purelib.Data.Rat

@[expose] public section

/-! Endpoint-polygon requests on every boundary piece of adjacent complete
faces. Their tail covers the synchronized surface requests on both sheets. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointRequests

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
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (PiecePerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (EndpointPolygonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy.EndpointPolygonPreparation (EnergyRequest)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational} {grid :
    NewtonGrid preparation target radius}
  {observations : ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {partitions : SurfacePartitions
    observations grid}
  {surfaceCuts : SurfaceCuts partitions domains}
  {first last : Fin grid.faces.regulars.length}
  {start : Purelib.Data.Gaussian.Basic.Canonical} {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    (curve.polynomial.eval start)}
  (firstEntry : Entry (domains.get
    first).models start owner)
  (lastEntry : Entry (domains.get last).models
    start owner)
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet} {error :
    Rational}

variable (requests : SynchronizedSurfaceRequests
  (fun sheet => Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains
    surfaceCuts sheet coarseDepth) fixed error)

variable
  (firstTraces : PiecePerimeterTraces
    (requests.entries.get firstEntry.sheet) first)
  (lastTraces : PiecePerimeterTraces
    (requests.entries.get lastEntry.sheet) last)

/-- Prepare the actual horizontal face-pair endpoint polygon on the original shared root owner, paying both synchronized
surface stages and the supplied floor. -/
def horizontalEndpointRequest
    (equal : (partitions.get first).cuts.x.intervals = (partitions.get last).cuts.x.intervals)
    (adjacent : (grid.faces.regulars[first.val]'first.isLt).cell.box.yUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.yLower)
    (origin : (EndpointGeometry.horizontalPieces firstTraces lastTraces
      (HorizontalPieces.build _ _ equal adjacent)).points 0 = start)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat) :
    let geometry := EndpointGeometry.horizontalPieces firstTraces lastTraces
      (HorizontalPieces.build _ _ equal adjacent)
    let contacts := EndpointPolygonPreparation.build
      (leftEntry := firstEntry) (rightEntry := lastEntry) geometry origin
    EndpointPolygonPreparation.EnergyRequest contacts allowance (max requests.index floor) :=
  EnergyRequest.build
    (EndpointPolygonPreparation.build (leftEntry := firstEntry) (rightEntry := lastEntry)
      (EndpointGeometry.horizontalPieces firstTraces lastTraces
        (HorizontalPieces.build _ _ equal adjacent)) origin)
    allowance positive (max requests.index floor)

/-- Prepare the actual vertical face-pair endpoint polygon on the original shared root owner, paying both synchronized
surface stages and the supplied floor. -/
def verticalEndpointRequest
    (equal : (partitions.get first).cuts.y.intervals = (partitions.get last).cuts.y.intervals)
    (adjacent : (grid.faces.regulars[first.val]'first.isLt).cell.box.xUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.xLower)
    (origin : (EndpointGeometry.verticalPieces firstTraces lastTraces
      (VerticalPieces.build _ _ equal adjacent)).points 0 = start)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat) :
    let geometry := EndpointGeometry.verticalPieces firstTraces lastTraces
      (VerticalPieces.build _ _ equal adjacent)
    let contacts := EndpointPolygonPreparation.build
      (leftEntry := firstEntry) (rightEntry := lastEntry) geometry origin
    EndpointPolygonPreparation.EnergyRequest contacts allowance (max requests.index floor) :=
  EnergyRequest.build
    (EndpointPolygonPreparation.build (leftEntry := firstEntry) (rightEntry := lastEntry)
      (EndpointGeometry.verticalPieces firstTraces lastTraces
        (VerticalPieces.build _ _ equal adjacent)) origin)
    allowance positive (max requests.index floor)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointRequests
