module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MatchedSides
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Integration.RectangularExteriorCornerOwners
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CornerGeometry
import Purelib.Riemann.Integration.RectangularMatchedCornerReadback
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Riemann.Integration.RectangularExteriorCornerOwners

open Purelib.Riemann.Integration.RectangularMatchedCornerReadback.MatchedHorizontalSide

open Purelib.Riemann.Integration.RectangularMatchedCornerReadback.MatchedVerticalSide

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

public section

/-! The full cross-owner endpoint terms of the paired traces are exactly
the terms subtracted in the complete face-assembly seam identity. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamEndpoints

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Topology.Polygon.Stokes (edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
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
  {partitions : SurfacePartitions observations grid}
  {surfaceCuts : SurfaceCuts partitions domains}
    {depth : Nat}
  {fixed : Preflights domains sheet} {error :
    Rational}
  {energy : SurfaceRequest partitions
    (Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
    sheet depth) fixed error}
  {stage : Nat} {cache : Numerics domains
    stage} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {assemblies : ExteriorRequest.Assemblies energy
    cache coefficients} {perimeters : Perimeters
    assemblies}
  {position : Fin grid.faces.regulars.length}

/-- The original paired horizontal seam trace's cross-owner endpoint difference is exactly the retained
vertical-junction term of the complete face assembly. -/
theorem FaceAssembly.horizontal_trace_endpoint (face : FaceAssembly perimeters position)
    (column : Fin ((PieceIndices.columns (partitions.get position)) + 1)) (row : Fin (PieceIndices.rows (partitions.get
      position)))
    (trace : (MatchedSides.horizontalSeamSide energy position column row).Trace energy.depth) :
    let values := SeamAreas.seamValues (sheet := sheet) cache coefficients position
    Stokes.edgeArea (trace.rightValue values (trace.vertices.indexed (Fin.last trace.vertices.rest.length)))
        (trace.leftValue values (trace.vertices.indexed (Fin.last trace.vertices.rest.length))) -
      Stokes.edgeArea (trace.rightValue values (trace.vertices.indexed 0)) (trace.leftValue values
        (trace.vertices.indexed 0)) =
      BilinearGridBoundary.verticalEndpoint face.corners column row := by
  let values := SeamAreas.seamValues (sheet := sheet) cache coefficients position
  have leftFirst := Trace.left_corner trace (above := false) values (PieceIndices.vertical_neighbor (partitions.get
    position) column row) false
  have leftLast := Trace.left_corner trace (above := false) values (PieceIndices.vertical_neighbor (partitions.get
    position) column row) true
  have rightFirst := Trace.right_corner trace (above := true) values rfl false
  have rightLast := Trace.right_corner trace (above := true) values rfl true
  simp only [-eq_self, -iff_self, if_neg (show (false : Bool) ≠ true by decide), if_pos (rfl : (true : Bool) = true)]
    at leftFirst leftLast rightFirst rightLast
  refine (congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => a - b)
    (congrArg₂ Stokes.edgeArea rightLast leftLast) (congrArg₂ Stokes.edgeArea rightFirst leftFirst)).trans ?_
  simp only [-eq_self, -iff_self, BilinearGridBoundary.verticalEndpoint, face.corners_eq, FaceAssembly.faceCorners]
  have below := ClippedAssembly.exterior_corners ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get
    position) column row.castSucc))
  have above := ClippedAssembly.exterior_corners ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get
    position) column row.succ))
  rw [below.2.2.2, above.2.1, below.2.2.1, above.1]
  rfl

/-- The original paired vertical seam trace's cross-owner endpoint difference is exactly the retained
horizontal-junction term of the complete face assembly. -/
theorem FaceAssembly.vertical_trace_endpoint (face : FaceAssembly perimeters position)
    (column : Fin (PieceIndices.columns (partitions.get position))) (row : Fin ((PieceIndices.rows (partitions.get
      position)) + 1))
    (trace : (MatchedSides.verticalSeamSide energy position column row).Trace energy.depth) :
    let values := SeamAreas.seamValues (sheet := sheet) cache coefficients position
    Stokes.edgeArea (trace.rightValue values (trace.vertices.indexed (Fin.last trace.vertices.rest.length)))
        (trace.leftValue values (trace.vertices.indexed (Fin.last trace.vertices.rest.length))) -
      Stokes.edgeArea (trace.rightValue values (trace.vertices.indexed 0)) (trace.leftValue values
        (trace.vertices.indexed 0)) =
      BilinearGridBoundary.horizontalEndpoint face.corners column row := by
  let values := SeamAreas.seamValues (sheet := sheet) cache coefficients position
  have leftFirst := Trace.left_corner trace (rightward := true) values rfl false
  have leftLast := Trace.left_corner trace (rightward := true) values rfl true
  have rightFirst := Trace.right_corner trace (rightward := false) values (PieceIndices.horizontal_neighbor
    (partitions.get position) column row) false
  have rightLast := Trace.right_corner trace (rightward := false) values (PieceIndices.horizontal_neighbor
    (partitions.get position) column row) true
  simp only [-eq_self, -iff_self, if_neg (show (false : Bool) ≠ true by decide), if_pos (rfl : (true : Bool) = true)]
    at leftFirst leftLast rightFirst rightLast
  refine (congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => a - b)
    (congrArg₂ Stokes.edgeArea rightLast leftLast) (congrArg₂ Stokes.edgeArea rightFirst leftFirst)).trans ?_
  simp only [-eq_self, -iff_self, BilinearGridBoundary.horizontalEndpoint, face.corners_eq, FaceAssembly.faceCorners]
  have left := ClippedAssembly.exterior_corners ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get
    position) column.castSucc row))
  have right := ClippedAssembly.exterior_corners ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get
    position) column.succ row))
  rw [right.2.2.1, left.2.2.2, right.1, left.2.1]
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamEndpoints
