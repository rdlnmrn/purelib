module
import Purelib.Data.List.Membership
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.QuadrilateralDual
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
public import Purelib.Integration.Path.PairedIncrementArea
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

/-! The four actual face sources form the polygon of the same cached
corner readings used by its two triangles, on the retained lifted sheet. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon
public section
open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
open Purelib.Integration.Path
open Purelib.Riemann.Meshes
open Purelib.Topology.Mesh.QuadrilateralDual
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Sewing
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
open Purelib.Topology.Mesh.QuadrilateralDual (QuadOccurrence)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank}

namespace LiftedMesh

/-- Select the actual retained triangle source edge for one original face side and sheet. -/
@[expose]
def faceSource (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (position : Fin faces.regulars.length)
    (sheet : Fin 2) (kind : RectangleEdge.Kind) : SewnPrimitiveContacts.SourceEdge mesh.triangles.length :=
  ⟨mesh.triangleIndex position sheet (QuadOccurrence.upperSide kind),
    FaceCorners.firstCorner kind, FaceCorners.lastCorner kind⟩

/-- The actual selected triangle source projects exactly to the retained lifted quadrilateral side. -/
theorem faceSource_project (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (position : Fin
  faces.regulars.length)
    (sheet : Fin 2) (kind : RectangleEdge.Kind) :
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSource mesh position sheet
      kind).project mesh.triangulation.faces =
      (mesh.locateFace position sheet).lifted.quad.edge kind := by
  unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSource
    SewnPrimitiveContacts.SourceEdge.project
  rw [mesh.triangleIndex_face, FaceCorners.source_edge]

/-- Read the four actual face sources in bottom, right, top and left boundary order. -/
@[expose]
def faceSources (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (position : Fin faces.regulars.length) (sheet :
  Fin 2) :
    List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length) :=
  [Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSource mesh position sheet .bottom,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSource mesh position sheet .right,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSource mesh position sheet .top,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSource mesh position sheet .left]

/-- The four retained source occurrences project exactly to the original indexed face boundary on its actual sheet. -/
theorem faceSources_project (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (position : Fin
  faces.regulars.length) (sheet : Fin 2) :
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSources mesh position
      sheet).map (fun source => source.project mesh.triangulation.faces) =
      edges.indexedEdges vertices (faces.regulars[position.val]'position.isLt).boundary sheet := by
  unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSources
  rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSource_project mesh,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSource_project mesh,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSource_project mesh,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSource_project mesh]
  exact (mesh.locateFace position sheet).lifted.boundary_eq

/-- Every actual retained face source has distinct original endpoint corners.

The proof follows membership in the retained list through its original head, tail or concatenation, preserving the
supplied occurrence witness. -/
theorem faceSources_nonloop (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (position : Fin
  faces.regulars.length) (sheet : Fin 2) :
    ∀ source ∈ Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSources mesh position sheet,
      source.first ≠ source.last := by
  intro source member
  have each (kind : RectangleEdge.Kind) :
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSource mesh position sheet kind).first
    ≠
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSource mesh position sheet kind).last
        := by
    change FaceCorners.firstCorner kind ≠ FaceCorners.lastCorner kind
    cases kind <;> decide
  rcases Membership.mem_cons.mp member with rfl | member
  · exact each .bottom
  rcases Membership.mem_cons.mp member with rfl | member
  · exact each .right
  rcases Membership.mem_cons.mp member with rfl | member
  · exact each .top
  rcases Membership.mem_cons.mp member with rfl | member
  · exact each .left
  · exact (List.not_mem_nil member).elim

end LiftedMesh

variable {mesh : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges faces} {domains :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}
  {stage : Nat} {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {shared :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage domains}

namespace TriangleReadings

/-- The actual triangle source increment is exactly the difference of its retained cached face-corner readings. -/
theorem faceSource_increment (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh)
    (position : Fin faces.regulars.length) (sheet : Fin 2) (kind : RectangleEdge.Kind) :
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSource mesh position sheet
      kind).increment readings.values =
      ((shared.get position).atSheet sheet).corners.values (FaceCorners.quad.edge kind).finish -
        ((shared.get position).atSheet sheet).corners.values (FaceCorners.quad.edge kind).start := by
  unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSource
    SewnPrimitiveContacts.SourceEdge.increment
  rw [readings.values_eq, FaceCorners.triangle_increment]

/-- The paired increment area around four actual corner values equals the sum of their two original triangle wedges. -/
private theorem quadrilateral_area (a b c d : Stokes.PrimitivePoint) :
    PairedIncrementArea.area [b.sub a, c.sub b, d.sub c, a.sub d] =
      Stokes.triangleWedgeArea a b c + Stokes.triangleWedgeArea a c d := by
  simp only [PairedIncrementArea.area, PairedIncrementArea.terms, PairedIncrementArea.total,
    List.map_cons, List.map_nil, Data.Gaussian.Norm.Sum.Basic.gaussianSum, PrimitivePoint.sub,
    Stokes.edgeArea, Stokes.triangleWedgeArea]
  ring1

/-- No smallness assumption is needed for this readback. The full polygon area equals the two local wedges even when the
closed polygon has nonzero area. -/
theorem faceSources_area {cache : RegularMeshes.Numerics domains stage} {i j : Fin genus}
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (position : Fin faces.regulars.length) (sheet : Fin 2) :
    PairedIncrementArea.area ((Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSources mesh
      position sheet).map (fun source =>
      (⟨source.increment left.values, source.increment right.values⟩ : Stokes.PrimitivePoint))) =
      TriangleReadings.bilinearArea left right (mesh.triangleIndex position sheet false) +
        TriangleReadings.bilinearArea left right (mesh.triangleIndex position sheet true) := by
  simp only [Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh.faceSources, List.map_cons,
    List.map_nil,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.TriangleReadings.faceSource_increment left,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.TriangleReadings.faceSource_increment right]
  rw [TriangleReadings.bilinearArea_eq_corners left right, TriangleReadings.bilinearArea_eq_corners left right]
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.TriangleReadings.quadrilateral_area
    (Numerics.cornerPair cache i j position sheet 0) (Numerics.cornerPair cache i j position sheet 1)
    (Numerics.cornerPair cache i j position sheet 2) (Numerics.cornerPair cache i j position sheet 3)

end TriangleReadings
end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon
