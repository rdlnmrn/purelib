module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointOrigins
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEntries
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.PairedEndpointPolygon
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Readings.RectangularPairedEndpointReadings
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Topology.Mesh.IndexedQuadrilaterals

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Data.Rat

@[expose] public section

/-! Endpoint contact requests derive their common owner and starting point
from the retained lifted mesh. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEndpointRequests

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
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointOrigins
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (PiecePerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEntries
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointRequests (horizontalEndpointRequest
  verticalEndpointRequest)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
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
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {error :
    Purelib.Data.Rat.Fraction.Rational}

variable (requests : Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests
  (fun sheet => Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains
    surfaceCuts sheet coarseDepth) fixed error)

variable {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid.shrunk.prepared.grid} {edges :
  Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {mesh : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges grid.faces} {sheet : Fin 2}
  (source : mesh.LocatedFace first sheet)

/-- Prepare the original horizontal endpoint comparison from its actual retained lifted source face.

The shared root owner and first polygon point come from the original mesh, with matching partitions and the requested
tolerance and floor preserved. -/
def horizontalLiftedEndpointRequest
    (firstTraces : PerimeterTraces.PiecePerimeterTraces (requests.entries.get sheet) first)
    (lastTraces : PerimeterTraces.PiecePerimeterTraces (requests.entries.get (HorizontalContact.next (last := last)
      source).sheet) last)
    (lower : (grid.faces.regulars[first.val]'first.isLt).cell.box.xLower =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.xLower)
    (upper : (grid.faces.regulars[first.val]'first.isLt).cell.box.xUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.xUpper)
    (adjacent : (grid.faces.regulars[first.val]'first.isLt).cell.box.yUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.yLower)
    (equal : (partitions.get first).cuts.x.intervals = (partitions.get last).cuts.x.intervals)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat) :=
  EndpointRequests.horizontalEndpointRequest (HorizontalContact.firstEntry (domains := domains) source)
    (HorizontalContact.lastEntry (domains := domains) source lower upper adjacent)
    requests firstTraces lastTraces equal adjacent
    ((EndpointGeometry.horizontal_origin firstTraces lastTraces equal adjacent).trans
      source.lifted.coordinates.2.2.2.symm)
    allowance positive floor

/-- Prepare the original vertical endpoint comparison from its actual retained lifted source face.

The shared root owner and first polygon point come from the original mesh, with matching partitions and the requested
tolerance and floor preserved. -/
def verticalLiftedEndpointRequest
    (firstTraces : PerimeterTraces.PiecePerimeterTraces (requests.entries.get sheet) first)
    (lastTraces : PerimeterTraces.PiecePerimeterTraces (requests.entries.get (VerticalContact.next (last := last)
      source).sheet) last)
    (lower : (grid.faces.regulars[first.val]'first.isLt).cell.box.yLower =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.yLower)
    (upper : (grid.faces.regulars[first.val]'first.isLt).cell.box.yUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.yUpper)
    (adjacent : (grid.faces.regulars[first.val]'first.isLt).cell.box.xUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.xLower)
    (equal : (partitions.get first).cuts.y.intervals = (partitions.get last).cuts.y.intervals)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat) :=
  EndpointRequests.verticalEndpointRequest (VerticalContact.firstEntry (domains := domains) source)
    (VerticalContact.lastEntry (domains := domains) source lower upper adjacent)
    requests firstTraces lastTraces equal adjacent
    ((EndpointGeometry.vertical_origin firstTraces lastTraces equal adjacent).trans source.lifted.coordinates.2.1.symm)
    allowance positive floor

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEndpointRequests
