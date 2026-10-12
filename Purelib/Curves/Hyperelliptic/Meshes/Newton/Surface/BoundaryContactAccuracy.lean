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
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.HorizontalBoundaryRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.VerticalBoundaryRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Integration.Path.JoinedCenteredArea
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.HorizontalBoundaryAccuracy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.VerticalBoundaryAccuracy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredComparison
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
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
import Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Tactic.Ring

public section

/-! A complete boundary request discharges every contact-error premise of
the complete-face comparison at its certified common tail. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryContactAccuracy

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredComparison
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.HorizontalBoundaryAccuracy
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.HorizontalBoundaryRequest
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.VerticalBoundaryAccuracy
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.VerticalBoundaryRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.LinearAlgebra.Gaussian.Energy
open Purelib.Riemann.Periods
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
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces (HorizontalPieces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (PiecePerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceRequests (horizontalPieceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy.EndpointPolygonPreparation (EnergyRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.HorizontalBoundaryRequest
  (Traces Request)

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

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces)

variable
  (firstTraces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces (requests.entries.get
    firstEntry.sheet) first)
  (lastTraces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces (requests.entries.get
    lastEntry.sheet) last)

open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {pieceAllowance polygonAllowance : Data.Rat.Fraction.Rational} {floor stage : Nat}

/-- The paid horizontal contact request bounds the actual top-to-bottom centered-area discrepancy.

Matched column pieces and their endpoint polygons use the same retained numerical cache and homogeneous coefficient
factor. -/
theorem horizontalBoundary_accurate
    (equal : (partitions.get first).cuts.x.intervals = (partitions.get last).cuts.x.intervals)
    (adjacent : (grid.faces.regulars[first.val]'first.isLt).cell.box.yUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.yLower)
    (endpoints : PuncturedGrid.EndpointPolygonPreparation (leftEntry := firstEntry) (rightEntry :=
      lastEntry)
      (EndpointGeometry.horizontalPieces firstTraces.pieces lastTraces.pieces
        (HorizontalPieces.build _ _ equal adjacent)))
    (traces : HorizontalBoundaryRequest.Traces firstEntry lastEntry requests (HorizontalPieces.build _ _ equal
      adjacent))
    (request : HorizontalBoundaryRequest.Request firstEntry lastEntry requests firstTraces.pieces lastTraces.pieces
      (HorizontalPieces.build _ _ equal adjacent) endpoints traces pieceAllowance polygonAllowance floor)
    (later : request.index ≤ stage) (cache : LocalMeshes.Numerics domains stage) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector
      genus)
    (firstSamples : FacePerimeterTraces.Centered firstTraces cache coefficients)
    (lastSamples : FacePerimeterTraces.Centered lastTraces cache coefficients) :
    Data.Gaussian.Norm.Basic.normSq (firstSamples.top.centeredArea - lastSamples.bottom.centeredArea) ≤
      2 * (genus : Fraction.Rational)^2 * (FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Norm.Basic.normSq
        (coefficients i)))^2 *
        ((((PieceIndices.columns (partitions.get first)) + 1 : Nat) : Fraction.Rational)^2 * pieceAllowance +
          polygonAllowance) := by
  let counts := (PieceIndices.columns_eq (partitions.get first)).trans ((congrArg List.length equal).trans
    (PieceIndices.columns_eq (partitions.get last)).symm)
  let firstPieces := fun index => CenteredBilinearPath.Sample.build (fun vertex => FacePerimeterTraces.ownerValues cache
    coefficients first
    ((firstTraces.pieces.topPieces index).indexed vertex))
  let lastPieces := fun index => CenteredBilinearPath.Sample.build (fun vertex => FacePerimeterTraces.ownerValues cache
    coefficients last
    ((lastTraces.pieces.bottomPieces (Fin.cast counts index)).indexed vertex))
  let firstPolygon := CenteredBilinearPath.Sample.build (fun vertex => FacePerimeterTraces.ownerValues cache
    coefficients first
    ((JoinedCenteredArea.endpointPolygon firstTraces.pieces.topPieces).indexed vertex))
  let lastPolygon := CenteredBilinearPath.Sample.build (fun vertex => FacePerimeterTraces.ownerValues cache coefficients
    last
    ((JoinedCenteredArea.endpointPolygon (fun index => lastTraces.pieces.bottomPieces (Fin.cast counts index))).indexed
      vertex))
  have piecesBound := fun piece => HorizontalBoundaryRequest.Request.piece_accurate request later cache coefficients
    piece (firstPieces piece) (lastPieces piece)
  have polygonBound := HorizontalBoundaryRequest.Request.polygon_accurate request later cache coefficients firstPolygon
    lastPolygon
  have bound := FacePerimeterComparison.horizontal counts firstSamples lastSamples
    firstPieces lastPieces firstPolygon lastPolygon piecesBound polygonBound
  exact bound.trans_eq (by ring1)

/-- The paid vertical contact request bounds the actual right-to-left centered-area discrepancy.

Matched row pieces and their endpoint polygons use the same retained numerical cache and homogeneous coefficient factor.
-/
theorem verticalBoundary_accurate
    (equal : (partitions.get first).cuts.y.intervals = (partitions.get last).cuts.y.intervals)
    (adjacent : (grid.faces.regulars[first.val]'first.isLt).cell.box.xUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.xLower)
    (endpoints : PuncturedGrid.EndpointPolygonPreparation (leftEntry := firstEntry) (rightEntry :=
      lastEntry)
      (EndpointGeometry.verticalPieces firstTraces.pieces lastTraces.pieces
        (VerticalPieces.build _ _ equal adjacent)))
    (traces : VerticalBoundaryRequest.Traces firstEntry lastEntry requests (VerticalPieces.build _ _ equal adjacent))
    (request : VerticalBoundaryRequest.Request firstEntry lastEntry requests firstTraces.pieces lastTraces.pieces
      (VerticalPieces.build _ _ equal adjacent) endpoints traces pieceAllowance polygonAllowance floor)
    (later : request.index ≤ stage) (cache : LocalMeshes.Numerics domains stage) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector
      genus)
    (firstSamples : FacePerimeterTraces.Centered firstTraces cache coefficients)
    (lastSamples : FacePerimeterTraces.Centered lastTraces cache coefficients) :
    Data.Gaussian.Norm.Basic.normSq (firstSamples.right.centeredArea - lastSamples.left.centeredArea) ≤
      2 * (genus : Fraction.Rational)^2 * (FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Norm.Basic.normSq
        (coefficients i)))^2 *
        ((((PieceIndices.rows (partitions.get first)) + 1 : Nat) : Fraction.Rational)^2 * pieceAllowance +
          polygonAllowance) := by
  let counts := (PieceIndices.rows_eq (partitions.get first)).trans ((congrArg List.length equal).trans
    (PieceIndices.rows_eq (partitions.get last)).symm)
  let firstPieces := fun index => CenteredBilinearPath.Sample.build (fun vertex => FacePerimeterTraces.ownerValues cache
    coefficients first
    ((firstTraces.pieces.rightPieces index).indexed vertex))
  let lastPieces := fun index => CenteredBilinearPath.Sample.build (fun vertex => FacePerimeterTraces.ownerValues cache
    coefficients last
    ((lastTraces.pieces.leftPieces (Fin.cast counts index)).indexed vertex))
  let firstPolygon := CenteredBilinearPath.Sample.build (fun vertex => FacePerimeterTraces.ownerValues cache
    coefficients first
    ((JoinedCenteredArea.endpointPolygon firstTraces.pieces.rightPieces).indexed vertex))
  let lastPolygon := CenteredBilinearPath.Sample.build (fun vertex => FacePerimeterTraces.ownerValues cache coefficients
    last
    ((JoinedCenteredArea.endpointPolygon (fun index => lastTraces.pieces.leftPieces (Fin.cast counts index))).indexed
      vertex))
  have piecesBound := fun piece => VerticalBoundaryRequest.Request.piece_accurate request later cache coefficients piece
    (firstPieces piece) (lastPieces piece)
  have polygonBound := VerticalBoundaryRequest.Request.polygon_accurate request later cache coefficients firstPolygon
    lastPolygon
  have bound := FacePerimeterComparison.vertical counts firstSamples lastSamples
    firstPieces lastPieces firstPolygon lastPolygon piecesBound polygonBound
  exact bound.trans_eq (by ring1)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryContactAccuracy
