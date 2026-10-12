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
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
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
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredComparison
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonPreparation
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

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Periods

@[expose] public section

/-! The endpoint request controls the original complete-face endpoint polygons
at the same cached numerical stage. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointAccuracy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces (HorizontalPieces VerticalPieces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices (columns_eq rows_eq)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointGeometry
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointRequests (horizontalEndpointRequest
  verticalEndpointRequest)

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
  (firstEntry : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (domains.get
    first).models start owner)
  (lastEntry : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (domains.get last).models
    start owner)
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet} {error :
    Rational}

variable (requests : SynchronizedSurfaceRequests
  (fun sheet => Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains
    surfaceCuts sheet coarseDepth) fixed error)

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces (ownerValues)

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {stage : Nat} (cache : Numerics
  domains stage) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

/-- The original horizontal endpoint request bounds the complete retained top-versus-bottom endpoint polygon
discrepancy.

Both original face banks are read at the same paid numerical stage with the supplied coefficient vector. -/
theorem horizontalEndpointRequest_accurate
    (firstTraces : PerimeterTraces.FacePerimeterTraces (requests.entries.get firstEntry.sheet) first)
    (lastTraces : PerimeterTraces.FacePerimeterTraces (requests.entries.get lastEntry.sheet) last)
    (equal : (partitions.get first).cuts.x.intervals = (partitions.get last).cuts.x.intervals)
    (adjacent : (grid.faces.regulars[first.val]'first.isLt).cell.box.yUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.yLower)
    (origin : (EndpointGeometry.horizontalPieces firstTraces.pieces lastTraces.pieces
      (HorizontalPieces.build _ _ equal adjacent)).points 0 = start)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat)
    (later : (EndpointRequests.horizontalEndpointRequest firstEntry lastEntry requests firstTraces.pieces
      lastTraces.pieces
      equal adjacent origin allowance positive floor).index ≤ stage)
    (firstPolygon : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients first
      ((JoinedCenteredArea.endpointPolygon firstTraces.pieces.topPieces).indexed vertex)))
    (lastPolygon : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients last
      ((JoinedCenteredArea.endpointPolygon (fun index => lastTraces.pieces.bottomPieces
        (Fin.cast ((PieceIndices.columns_eq (partitions.get first)).trans ((congrArg List.length equal).trans
          (PieceIndices.columns_eq (partitions.get last)).symm)) index))).indexed vertex))) :
    Data.Gaussian.Norm.Basic.normSq (firstPolygon.centeredArea - lastPolygon.centeredArea) ≤
      (genus : Fraction.Rational)^2 * (FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Norm.Basic.normSq
        (coefficients i)))^2 * allowance := by
  let request := EndpointRequests.horizontalEndpointRequest firstEntry lastEntry requests firstTraces.pieces
    lastTraces.pieces
    equal adjacent origin allowance positive floor
  exact request.original_accurate later (fun i => cache.atDomain first firstEntry.sheet i)
    (fun i => cache.atDomain last lastEntry.sheet i) coefficients
    (fun _ _ => CenteredBilinearPath.Sample.build _) (fun _ _ => CenteredBilinearPath.Sample.build _)
    (fun _ _ => CenteredBilinearPath.Sample.build _) (fun _ _ => CenteredBilinearPath.Sample.build _) firstPolygon
      lastPolygon

/-- The original vertical endpoint request bounds the complete retained right-versus-left endpoint polygon discrepancy.

Both original face banks are read at the same paid numerical stage with the supplied coefficient vector. -/
theorem verticalEndpointRequest_accurate
    (firstTraces : PerimeterTraces.FacePerimeterTraces (requests.entries.get firstEntry.sheet) first)
    (lastTraces : PerimeterTraces.FacePerimeterTraces (requests.entries.get lastEntry.sheet) last)
    (equal : (partitions.get first).cuts.y.intervals = (partitions.get last).cuts.y.intervals)
    (adjacent : (grid.faces.regulars[first.val]'first.isLt).cell.box.xUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.xLower)
    (origin : (EndpointGeometry.verticalPieces firstTraces.pieces lastTraces.pieces
      (VerticalPieces.build _ _ equal adjacent)).points 0 = start)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat)
    (later : (EndpointRequests.verticalEndpointRequest firstEntry lastEntry requests firstTraces.pieces
      lastTraces.pieces
      equal adjacent origin allowance positive floor).index ≤ stage)
    (firstPolygon : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients first
      ((JoinedCenteredArea.endpointPolygon firstTraces.pieces.rightPieces).indexed vertex)))
    (lastPolygon : CenteredBilinearPath.Sample (fun vertex => FacePerimeterTraces.ownerValues cache coefficients last
      ((JoinedCenteredArea.endpointPolygon (fun index => lastTraces.pieces.leftPieces
        (Fin.cast ((PieceIndices.rows_eq (partitions.get first)).trans ((congrArg List.length equal).trans
          (PieceIndices.rows_eq (partitions.get last)).symm)) index))).indexed vertex))) :
    Data.Gaussian.Norm.Basic.normSq (firstPolygon.centeredArea - lastPolygon.centeredArea) ≤
      (genus : Fraction.Rational)^2 * (FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Norm.Basic.normSq
        (coefficients i)))^2 * allowance := by
  let request := EndpointRequests.verticalEndpointRequest firstEntry lastEntry requests firstTraces.pieces
    lastTraces.pieces
    equal adjacent origin allowance positive floor
  exact request.original_accurate later (fun i => cache.atDomain first firstEntry.sheet i)
    (fun i => cache.atDomain last lastEntry.sheet i) coefficients
    (fun _ _ => CenteredBilinearPath.Sample.build _) (fun _ _ => CenteredBilinearPath.Sample.build _)
    (fun _ _ => CenteredBilinearPath.Sample.build _) (fun _ _ => CenteredBilinearPath.Sample.build _) firstPolygon
      lastPolygon

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.EndpointAccuracy
