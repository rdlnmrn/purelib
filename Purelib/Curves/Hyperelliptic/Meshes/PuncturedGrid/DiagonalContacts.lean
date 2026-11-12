module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceContactRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

@[expose] public section

/-!
# Exact cancellation of original diagonal contacts

The opposite positive occurrence is uniquely the other triangle of the same
retained face and sheet. Both triangles read one four-corner primitive cache,
so their contact requires no path preparation or accuracy refinement.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DiagonalContacts

open Purelib.Topology.Polygon.Stokes
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {frames : SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {differential : Differentials.Basic.Differential genus} {index : Nat} {domains :
    Face.DomainBanks.FaceDomainBank frames faces.regulars}
  {numerator : CoefficientPolynomial}
  {shared : Face.PrimitiveData.FacePrimitiveBank differential index domains (numerator := numerator)}

namespace LocatedContact

variable {contact : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact mesh.triangulation.faces}

/-- Opposite diagonal occurrences using the same original four-corner cache have exactly zero contact mismatch. -/
private theorem diagonal_zero (located : SourceContactRequests.LocatedContact
  contact) (oppositeKind : RectangleEdge.Kind)
    (opposite : located.left.lifted.quad.edge oppositeKind =
      (located.left.lifted.quad.edge located.left.kind).reverse)
    (corners : (FaceCorners.quad).edge oppositeKind =
      ((FaceCorners.quad).edge
        located.left.kind).reverse)
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
      contact.mismatch readings.values = 0 := by
  let other := located.left.atKind oppositeKind
  have same : other.sourceEdge = contact.right :=
    TriangleSourceUniqueness.LiftedMesh.source_eq_of_project_eq mesh
      (TriangleSourceUniqueness.LiftedFaces.EdgeLocation.sourceEdge_positive other)
      (located.right_eq ▸
        TriangleSourceUniqueness.LiftedFaces.EdgeLocation.sourceEdge_positive
        located.right)
      (other.sourceEdge_project.trans (opposite.trans
        ((congrArg OrientedEdge.reverse located.left.edge_eq).trans contact.opposite.symm)))
  unfold Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact.mismatch
  rw [← located.left_eq, ← same, readings.location_increment, readings.location_increment,
    shared.edgeIncrement_eq, shared.edgeIncrement_eq]
  change Gaussian.Norm.Basic.normSq
    ((((shared.get located.left.position).atSheet located.left.sheet).corners.values
          ((FaceCorners.quad).edge located.left.kind).finish -
        ((shared.get located.left.position).atSheet located.left.sheet).corners.values
          ((FaceCorners.quad).edge located.left.kind).start) +
      (((shared.get located.left.position).atSheet located.left.sheet).corners.values
          ((FaceCorners.quad).edge oppositeKind).finish -
        ((shared.get located.left.position).atSheet located.left.sheet).corners.values
          ((FaceCorners.quad).edge oppositeKind).start)) = 0
  rw [corners]
  simp only [OrientedEdge.reverse]
  have cancel (first last : Gaussian.Basic.Canonical) : (last - first) + (first - last) = 0 := by ring1
  rw [cancel]
  exact Gaussian.Norm.Basic.normSq_zero

/-- The original up-diagonal contact cancels exactly against its retained down-diagonal occurrence. -/
theorem upDiagonal_zero (located : SourceContactRequests.LocatedContact contact)
  (kind : located.left.kind = .upDiagonal)
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
      contact.mismatch readings.values = 0 :=
  LocatedContact.diagonal_zero located .downDiagonal
    (by rw [kind]; rfl) (by rw [kind]; rfl) readings

/-- The original down-diagonal contact cancels exactly against its retained up-diagonal occurrence. -/
theorem downDiagonal_zero (located : SourceContactRequests.LocatedContact contact)
  (kind : located.left.kind = .downDiagonal)
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
      contact.mismatch readings.values = 0 :=
  LocatedContact.diagonal_zero located .upDiagonal
    (by rw [kind]; rfl) (by rw [kind]; rfl) readings

end LocatedContact
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DiagonalContacts
