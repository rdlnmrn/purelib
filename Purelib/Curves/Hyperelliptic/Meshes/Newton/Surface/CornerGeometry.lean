module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
public import Purelib.Riemann.Integration.RectangularExteriorCornerOwners
import Init.Data.Fin.Basic
import Init.Prelude
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Geometry.Rectangle.Partition

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.RectangularExteriorCornerOwners

open Purelib.Riemann.Topology

public section

/-! The four cached readings at an observation-cut junction belong to
possibly different model cells, all containing the same physical point. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CornerGeometry

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonObservationSurfacePartition (SurfacePartition)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (Perimeters faceCorners)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas (seamValues)

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
    grid.faces.regulars} {sheet : Fin 2}

namespace SurfacePartition

variable {position : Fin grid.faces.regulars.length}

/-- The physical Gaussian point at an internal junction of the original retained observation cuts. -/
@[expose] def junctionPoint (partition : NewtonObservationSurfacePartition.SurfacePartition observations grid position)
    (column : Fin (PieceIndices.columns partition)) (row : Fin (PieceIndices.rows partition)) : Gaussian :=
  ⟨(partition.cuts.x.intervals[(Fin.cast (PieceIndices.columns_eq partition) column.castSucc).val]'
      (Fin.cast (PieceIndices.columns_eq partition) column.castSucc).isLt).upper,
    (partition.cuts.y.intervals[(Fin.cast (PieceIndices.rows_eq partition) row.castSucc).val]'
      (Fin.cast (PieceIndices.rows_eq partition) row.castSucc).isLt).upper⟩

/-- Each of the four original neighboring piece corners equals the same physical cut junction. -/
theorem junction_corner (partition : NewtonObservationSurfacePartition.SurfacePartition observations grid position)
    (column : Fin (PieceIndices.columns partition)) (row : Fin (PieceIndices.rows partition)) (right above : Bool) :
    let piece := PieceIndices.pieceIndex partition (if right then column.succ else column.castSucc) (if above then
      row.succ else row.castSucc)
    PreparedRectangleCuts.corner (partition.cuts.boxes[piece.val]'piece.isLt) (!right) (!above) =
      junctionPoint partition column row :=
      by
  have horizontal := partition.cuts.x.consecutive column.val (by
      rw [← PieceIndices.columns_eq partition];
      exact Nat.succ_lt_succ column.isLt)
  have vertical := partition.cuts.y.consecutive row.val (by
      rw [← PieceIndices.rows_eq partition];
      exact Nat.succ_lt_succ row.isLt)
  cases right <;> cases above <;>
    simp only [-eq_self, -iff_self, if_neg (show (false : Bool) ≠ true by decide), if_pos (rfl : (true : Bool) = true),
      Bool.not_false, Bool.not_true, PieceIndices.piece_box partition,
      PreparedRectangleCuts.corner, PreparedRectangleCuts.intervalBox,
        junctionPoint]
  · rfl
  · exact Data.Gaussian.Basic.ext rfl vertical.symm
  · exact Data.Gaussian.Basic.ext horizontal.symm rfl
  · exact Data.Gaussian.Basic.ext horizontal.symm vertical.symm

end SurfacePartition

namespace SurfaceRequest

variable {partitions : SurfacePartitions observations grid}
  {coarse : SurfaceMeshes partitions domains sheet}
  {fixed : Preflights domains sheet} {error :
    Rational}

/-- The actual retained mesh vertex owner for the selected neighboring piece at an original internal cut junction. -/
@[expose] def junctionOwner (energy : NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed error)
  (position : Fin grid.faces.regulars.length)
    (column : Fin (PieceIndices.columns (partitions.get position))) (row : Fin (PieceIndices.rows (partitions.get
      position))) (right above : Bool) :
    RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry :=
  let partition := partitions.get position
  let piece := PieceIndices.pieceIndex partition (if right then column.succ else column.castSucc) (if above then
    row.succ else row.castSucc)
  RectangularExteriorCornerOwners.exteriorCornerOwner ((energy.meshes.get position).entries.get piece) (!right) (!above)

/-- Every selected original junction owner has the same retained physical junction point. -/
theorem junctionOwner_point (energy : NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed error)
  (position : Fin grid.faces.regulars.length)
    (column : Fin (PieceIndices.columns (partitions.get position))) (row : Fin (PieceIndices.rows (partitions.get
      position))) (right above : Bool) :
    (junctionOwner energy position column row
      right above).point = Curves.Hyperelliptic.Meshes.Newton.Surface.CornerGeometry.SurfacePartition.junctionPoint
      (partitions.get position) column row :=
  (RectangularExteriorCornerOwners.exteriorCornerOwner_point ((energy.meshes.get position).entries.get _) (!right)
    (!above)).trans
    (Curves.Hyperelliptic.Meshes.Newton.Surface.CornerGeometry.SurfacePartition.junction_corner (partitions.get
      position) column row right above)

namespace ExteriorRequest

variable {energy : SurfaceRequest partitions coarse fixed error}
  {stage : Nat} {cache : Numerics domains
  stage}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {assemblies :
    ExteriorRequest.Assemblies energy cache
    coefficients}
  {perimeters : Perimeters assemblies} {position : Fin
    grid.faces.regulars.length}

/-- The four acquired face corners read the actual primitive caches of their original junction owners at the common
physical point. -/
theorem FaceAssembly.corner_junction (face : FaceAssembly perimeters position)
    (column : Fin (PieceIndices.columns (partitions.get position))) (row : Fin (PieceIndices.rows (partitions.get
      position))) :
    let value := fun right above =>
      let owner := Curves.Hyperelliptic.Meshes.Newton.Surface.CornerGeometry.SurfaceRequest.junctionOwner energy
        position column row right above
      SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point
    (face.corners column.castSucc row.castSucc).upperRight = value false false ∧
    (face.corners column.castSucc row.succ).lowerRight = value false true ∧
    (face.corners column.succ row.succ).lowerLeft = value true true ∧
    (face.corners column.succ row.castSucc).upperLeft = value true false := by
  simp only [-eq_self, -iff_self, face.corners_eq, FaceAssembly.faceCorners]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (ClippedAssembly.exterior_corners ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get
      position) column.castSucc row.castSucc))).2.2.2
  · exact (ClippedAssembly.exterior_corners ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get
      position) column.castSucc row.succ))).2.1
  · exact (ClippedAssembly.exterior_corners ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get
      position) column.succ row.succ))).1
  · exact (ClippedAssembly.exterior_corners ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get
      position) column.succ row.castSucc))).2.2.1

end ExteriorRequest
end SurfaceRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CornerGeometry
