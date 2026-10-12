module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.QuadrilateralDual
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeCancellation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings

open Purelib.Riemann.Normalization

open Purelib.Topology.Mesh.QuadrilateralDual

@[expose] public section

/-!
# Opposite-sheet edge sums in the original lifted triangle readings

The request starts from the retained domain bank and a positive tolerance.
Its conclusion is about the exact indexed triangle values consumed by the
cut-surface formulas, at independently chosen later primitive indices.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSheetCancellation

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests (PairedEdgeRequest)
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
open Purelib.Topology.Mesh.QuadrilateralDual (QuadOccurrence)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces}
  {domains : FaceDomainBank frames faces.regulars}
    {differential : Differential genus}

/-- Prepare the actual two-domain split and every error budget before materializing either later primitive bank. No root
or path data is rebuilt. -/
def pairedEdgeRequest (domains : DomainBanks.FaceDomainBank frames faces.regulars) (differential :
  Differentials.Basic.Differential genus)
    (position : Fin faces.regulars.length) (kind : RectangleEdge.Kind) (target : InverseRootPolynomial.Coordinate)
      (positive : 0 < target) :
    PairedEdgeRequests.PairedEdgeRequest (domains.get position) differential
      (FaceCorners.point faces.regulars[position.val].cell.box (FaceCorners.quad.edge kind).start)
      (FaceCorners.point faces.regulars[position.val].cell.box (FaceCorners.quad.edge kind).finish) target :=
  PairedEdgeRequest.build (domains.get position) differential _ _
    (FaceCorners.inside _ _) (FaceCorners.inside _ _) target positive

/-- Coordinate agreement alone is not used as root closure. The negative root comparison, two grids, primitive offsets
and both sheet occurrences have all been paid by the retained request. -/
theorem opposite_edge_accurate {leftIndex rightIndex : Nat}
    {leftBank : PrimitiveData.FacePrimitiveBank differential leftIndex domains} {rightBank :
      PrimitiveData.FacePrimitiveBank differential rightIndex domains}
    (left : TrianglePrimitiveReadings.TriangleReadings leftBank mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings rightBank mesh)
    (position : Fin faces.regulars.length) (kind : RectangleEdge.Kind) {target : InverseRootPolynomial.Coordinate}
    (request : PairedEdgeRequests.PairedEdgeRequest (domains.get position) differential
      (FaceCorners.point faces.regulars[position.val].cell.box (FaceCorners.quad.edge kind).start)
      (FaceCorners.point faces.regulars[position.val].cell.box (FaceCorners.quad.edge kind).finish) target)
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex) :
    Data.Gaussian.Norm.Basic.normSq ((left.values (mesh.triangleIndex position 0 (QuadOccurrence.upperSide
      kind)) (FaceCorners.lastCorner kind) -
        left.values (mesh.triangleIndex position 0 (QuadOccurrence.upperSide kind)) (FaceCorners.firstCorner kind)) +
      (right.values (mesh.triangleIndex position 1 (QuadOccurrence.upperSide kind)) (FaceCorners.lastCorner kind) -
        right.values (mesh.triangleIndex position 1 (QuadOccurrence.upperSide kind)) (FaceCorners.firstCorner kind))) <
          target := by
  rw [left.values_eq, right.values_eq, FaceCorners.triangle_increment, FaceCorners.triangle_increment]
  exact PairedEdgeCancellation.corners_accurate request ((leftBank.get position).atSheet 0) ((rightBank.get
    position).atSheet 1)
    leftLater rightLater (FaceCorners.quad.edge kind).start (FaceCorners.quad.edge kind).finish rfl rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSheetCancellation
