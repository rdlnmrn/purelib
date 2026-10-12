module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Integration.Path.JoinedCenteredArea
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.VerticalBoundaryRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition

public section

/-! Every later common stage pays the retained piece and endpoint requests
on the actual numerical bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.VerticalBoundaryAccuracy

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.VerticalBoundaryRequest
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.LinearAlgebra.Gaussian.Energy
open Purelib.Riemann.Paths
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy

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
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces (VerticalPieces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (PiecePerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceRequests (verticalPieceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (EndpointPolygonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy.EndpointPolygonPreparation (EnergyRequest)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius
    : Data.Rat.Fraction.Rational} {grid : Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid
    preparation target radius}
  {observations : Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars}
    {partitions : Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {surfaceCuts : Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains}
  {first last : Fin grid.faces.regulars.length}
  {start : Data.Gaussian.Basic.Canonical} {owner : Riemann.Topology.SquareRootContinuationChain.Owner
    (curve.polynomial.eval start)}
  (firstEntry : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (domains.get first).models start
    owner)
  (lastEntry : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (domains.get last).models start
    owner)
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) → Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights
    domains sheet} {error : Data.Rat.Fraction.Rational}

variable (requests : Riemann.Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests
  (fun sheet => Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains
    surfaceCuts sheet coarseDepth) fixed error)

variable
  (firstTraces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.PiecePerimeterTraces (requests.entries.get
    firstEntry.sheet) first)
  (lastTraces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.PiecePerimeterTraces (requests.entries.get
    lastEntry.sheet) last)

namespace VerticalBoundaryRequest

variable {count : Nat}
  (pieces : Fin (count + 1) → Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces.VerticalPieces (partitions.get
    first) (partitions.get last))
  (endpoints : PuncturedGrid.EndpointPolygonPreparation
    (leftEntry := firstEntry) (rightEntry := lastEntry)
    (EndpointGeometry.verticalPieces firstTraces lastTraces
      pieces))

variable (traces : VerticalBoundaryRequest.Traces
  firstEntry lastEntry requests pieces)
  {pieceAllowance polygonAllowance : Data.Rat.Fraction.Rational} {floor stage : Nat}

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas (seamValues)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)

variable {firstEntry lastEntry requests firstTraces lastTraces pieces endpoints traces}

/-- The paid vertical boundary request bounds the actual right and left area difference for each retained matched piece.

The bound uses the original numerical cache, owned perimeters and homogeneous coefficient factor. -/
theorem Request.piece_accurate
    (request : VerticalBoundaryRequest.Request firstEntry lastEntry requests firstTraces lastTraces pieces endpoints
      traces pieceAllowance polygonAllowance floor)
    (later : request.index ≤ stage) (cache : LocalMeshes.Numerics domains stage) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector
      genus)
    (piece : Fin (count + 1))
    (left : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients first
      ((RectangularOwnedPerimeterTraces.rightOwned (firstTraces.get (pieces piece).firstPiece)).indexed vertex)))
    (right : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients last
      ((RectangularOwnedPerimeterTraces.leftOwned (lastTraces.get (pieces piece).lastPiece)).indexed vertex))) :
    Data.Gaussian.Norm.Basic.normSq (left.centeredArea - right.centeredArea) ≤
      (genus : Fraction.Rational)^2 * (FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Norm.Basic.normSq
        (coefficients i)))^2 * pieceAllowance := by
  let leftAssembly := ClippedAssembly.build
    (((requests.entries.get firstEntry.sheet).meshes.get first).entries.get (pieces piece).firstPiece)
    (SeamAreas.seamValues (sheet := firstEntry.sheet) cache coefficients first)
  let rightAssembly := ClippedAssembly.build
    (((requests.entries.get lastEntry.sheet).meshes.get last).entries.get (pieces piece).lastPiece)
    (SeamAreas.seamValues (sheet := lastEntry.sheet) cache coefficients last)
  exact (request.entries.get piece).owned_accurate ((request.entries_le piece).trans later)
    (fun i => cache.atDomain first firstEntry.sheet i) (fun i => cache.atDomain last lastEntry.sheet i) coefficients
    (firstTraces.get (pieces piece).firstPiece) (lastTraces.get (pieces piece).lastPiece) left right
    leftAssembly rightAssembly (Perimeter.build leftAssembly) (Perimeter.build rightAssembly)
    (((requests.entries.get firstEntry.sheet).mesh_depth first (pieces piece).firstPiece).trans (requests.depth_eq
      firstEntry.sheet)).symm
    (((requests.entries.get lastEntry.sheet).mesh_depth last (pieces piece).lastPiece).trans (requests.depth_eq
      lastEntry.sheet)).symm
    rfl (pieces piece).joined

/-- The paid vertical boundary request bounds the actual endpoint-polygon area difference on the same retained piece
list and numerical cache. -/
theorem Request.polygon_accurate
    (request : VerticalBoundaryRequest.Request firstEntry lastEntry requests firstTraces lastTraces pieces endpoints
      traces pieceAllowance polygonAllowance floor)
    (later : request.index ≤ stage) (cache : LocalMeshes.Numerics domains stage) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector
      genus)
    (left : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients first
      ((JoinedCenteredArea.endpointPolygon (fun piece => RectangularOwnedPerimeterTraces.rightOwned (firstTraces.get
        (pieces piece).firstPiece))).indexed vertex)))
    (right : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients last
      ((JoinedCenteredArea.endpointPolygon (fun piece => RectangularOwnedPerimeterTraces.leftOwned (lastTraces.get
        (pieces piece).lastPiece))).indexed vertex))) :
    Data.Gaussian.Norm.Basic.normSq (left.centeredArea - right.centeredArea) ≤
      (genus : Fraction.Rational)^2 * (FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Norm.Basic.normSq
        (coefficients i)))^2 * polygonAllowance :=
  request.polygon.original_accurate (request.polygon_le.trans later)
    (fun i => cache.atDomain first firstEntry.sheet i) (fun i => cache.atDomain last lastEntry.sheet i) coefficients
    (fun _ _ => CenteredBilinearPath.Sample.build _) (fun _ _ => CenteredBilinearPath.Sample.build _)
    (fun _ _ => CenteredBilinearPath.Sample.build _) (fun _ _ => CenteredBilinearPath.Sample.build _) left right

end VerticalBoundaryRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.VerticalBoundaryAccuracy
