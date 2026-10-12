module
import Purelib.Data.List.Membership
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.List.Nodup

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.ClearGridCoverage
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.DualWalks
import Purelib.Topology.Surface.Sewing.SewingForest
public import Purelib.Riemann.Meshes.GridLiftedMesh
public import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
public import Purelib.Topology.Surface.Sewing.SewingConnected

public section

/-!
# Unique oriented edges of the actual two-sheeted punctured grid

The retained grid partition supplies disjoint regular interiors. The two
actual lifts over each regular face have distinct corresponding corners by
root-transport injectivity. Together these facts prove uniqueness of every
oriented triangle-edge occurrence, without a caller-supplied manifold check.
Dual-face connectivity remains a separate geometric obligation.
-/

namespace Purelib.Riemann.Meshes

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Riemann.Meshes.PuncturedGridFaces (FaceSplit RegularFace PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedFaces LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open _root_.Purelib.Topology.Surface.Sewing (SewingForest)
open Purelib.Topology.Mesh.DualWalks (DualConnection)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

namespace PuncturedGridFaces.FaceSplit

open Purelib.Curves in
open Purelib.Polynomial in
/-- Retaining only regular cells preserves pairwise separation of their interiors.

Structural classification retains either the original regular head or only the unchanged tail. The original cell-list
separation applies to those same retained regular occurrences. -/
theorem regulars_pairwise : ∀ {cells : List (Geometry.Grid.ClearGrid.Cell curve.polynomial
  (Hyperelliptic.Branches.Cuts.Ambient curve))} (split : FaceSplit bank cells),
    cells.Pairwise (fun first second => first.box.InteriorSeparated second.box) →
      split.regulars.Pairwise (fun first second => first.cell.box.InteriorSeparated second.cell.box)
  | _, .nil, _ => .nil
  | _, .regular head tail, separated =>
      .cons (fun other member => (List.pairwise_cons.mp separated).1 other.cell (tail.regular_member member))
        (tail.regulars_pairwise (List.pairwise_cons.mp separated).2)
  | _, .hole _ tail, separated => tail.regulars_pairwise (List.pairwise_cons.mp separated).2

end PuncturedGridFaces.FaceSplit

namespace PuncturedGridFaces.PuncturedFaces

open Purelib.Polynomial in
/-- The retained regular faces have pairwise separated interiors.

The cached regular-list equation identifies the original classified spine. Its retained cell separation restricts to
those exact regular-face occurrences. -/
theorem regulars_pairwise (faces : PuncturedFaces bank) :
    faces.regulars.Pairwise (fun first second => first.cell.box.InteriorSeparated second.cell.box) := by
  rw [faces.regulars_eq]
  exact faces.split.regulars_pairwise (Polynomial.Geometry.Grid.ClearGridCoverage.cells_pairwise bank.grid)

end PuncturedGridFaces.PuncturedFaces

namespace GridLiftedFaces.BranchCellBank.LiftedFace

variable {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
  Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {face : RegularFace bank} {sheet : Fin 2}

open Purelib.Geometry in
/-- The actual lifted quadrilateral has the coordinates of its retained rectangular cell.

The stored four corner-coordinate equalities identify the original lifted quadrilateral with its supplied regular-cell
box. The certificate retains the original vertices and corner order. -/
theorem rectangleCoordinates (lifted : LiftedFace vertices edges face sheet) :
    Rectangle.Partition.RectangularEdgeUniqueness.IndexedQuadrilateral.RectangleCoordinates lifted.quad
      vertices.coordinate face.cell.box :=
  ⟨lifted.coordinates.1, lifted.coordinates.2.1, lifted.coordinates.2.2.1, lifted.coordinates.2.2.2⟩

/-- The two triangles of one lifted proper rectangle have distinct oriented edges.

The two original triangles have the retained rectangle coordinates. Properness of the same cell box excludes repeated
oriented boundary occurrences within that lifted quadrilateral. -/
theorem triangleEdges_nodup (lifted : LiftedFace vertices edges face sheet) :
    (lifted.quad.triangles.flatMap OrientedTriangle.boundary).Nodup :=
  lifted.rectangleCoordinates.edges_nodup face.cell.box_proper

/-- Opposite sheet lifts of the same regular face have disjoint oriented triangle edges.

The two actual lifts retain the same regular-cell coordinates and opposite corresponding root owners. Those corner
inequalities exclude equal oriented triangle-edge occurrences across the two sheets. -/
theorem sheets_edges_disjoint (zero : LiftedFace vertices edges face 0) (one : LiftedFace vertices edges face 1) :
    ∀ left ∈ zero.quad.triangles.flatMap OrientedTriangle.boundary,
      ∀ right ∈ one.quad.triangles.flatMap OrientedTriangle.boundary, left ≠ right :=
  zero.rectangleCoordinates.sheets_disjoint one.rectangleCoordinates face.cell.box_proper (zero.opposite_corners one)

end GridLiftedFaces.BranchCellBank.LiftedFace

namespace GridLiftedMesh.LiftedFaces

variable {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
  Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

/-- Read a retained face pair's oriented triangle edges before the tail's edges.

Each face contributes its original zero-sheet and one-sheet triangle boundaries before the unchanged tail. The equation
preserves all oriented edge occurrences and their concatenation order. -/
theorem triangleEdges_cons {face : RegularFace bank} {faces : List (RegularFace bank)}
    (zero : LiftedFace vertices edges face 0) (one : LiftedFace vertices edges face 1) (tail : LiftedFaces vertices
      edges faces) :
    ((LiftedFaces.cons zero one tail).triangles.flatMap OrientedTriangle.boundary) =
      (zero.quad.triangles.flatMap OrientedTriangle.boundary ++ one.quad.triangles.flatMap OrientedTriangle.boundary) ++
        tail.triangles.flatMap OrientedTriangle.boundary := rfl

open Purelib.Riemann in
/-- Locate the retained face, sheet and lift supplying an oriented triangle edge.

The witness belongs to the original ordered face list and reuses its actual lifted quadrilateral. -/
theorem triangleEdge_member : ∀ {faces : List (RegularFace bank)} (lifts : LiftedFaces vertices edges faces)
    {edge : OrientedEdge vertices.count}, edge ∈ lifts.triangles.flatMap OrientedTriangle.boundary →
      ∃ face ∈ faces, ∃ sheet, ∃ lifted : LiftedFace vertices edges face sheet,
        edge ∈ lifted.quad.triangles.flatMap OrientedTriangle.boundary
  | _, .nil, _, member => (List.not_mem_nil member).elim
  | _, .cons zero one tail, edge, member => by
      rw [Meshes.GridLiftedMesh.LiftedFaces.triangleEdges_cons] at member
      rcases Data.List.Membership.mem_append.mp member with localMember | tailMember
      · rcases Data.List.Membership.mem_append.mp localMember with zeroMember | oneMember
        · exact ⟨_, List.mem_cons_self, 0, zero, zeroMember⟩
        · exact ⟨_, List.mem_cons_self, 1, one, oneMember⟩
      · obtain ⟨face, faceMember, sheet, lifted, liftedMember⟩ := tail.triangleEdge_member tailMember
        exact ⟨face, List.mem_cons_of_mem _ faceMember, sheet, lifted, liftedMember⟩

open Purelib.Riemann in
open Purelib.Data in
open Purelib.Polynomial in
/-- Separated regular interiors yield unique oriented edge occurrences across all retained lifts.

Local rectangle uniqueness and opposite-sheet disjointness combine with separation between different cells. -/
theorem triangleEdges_nodup : ∀ {faces : List (RegularFace bank)} (lifts : LiftedFaces vertices edges faces),
    faces.Pairwise (fun first second => first.cell.box.InteriorSeparated second.cell.box) →
      (lifts.triangles.flatMap OrientedTriangle.boundary).Nodup
  | _, .nil, _ => .nil
  | _, .cons zero one tail, separated => by
      rw [Meshes.GridLiftedMesh.LiftedFaces.triangleEdges_cons]
      refine List.Nodup.nodup_append
        (List.Nodup.nodup_append zero.triangleEdges_nodup one.triangleEdges_nodup (zero.sheets_edges_disjoint one))
        (tail.triangleEdges_nodup (List.pairwise_cons.mp separated).2) ?_
      intro left leftMember right rightMember
      obtain ⟨other, otherMember, sheet, lifted, liftedMember⟩ := tail.triangleEdge_member rightMember
      have apart := (List.pairwise_cons.mp separated).1 other otherMember
      rcases Data.List.Membership.mem_append.mp leftMember with zeroMember | oneMember
      · exact zero.rectangleCoordinates.edges_disjoint lifted.rectangleCoordinates
          (Geometry.Grid.ClearGrid.Cell.box_proper _) other.cell.box_proper apart left zeroMember right liftedMember
      · exact one.rectangleCoordinates.edges_disjoint lifted.rectangleCoordinates
          (Geometry.Grid.ClearGrid.Cell.box_proper _) other.cell.box_proper apart left oneMember right liftedMember

end GridLiftedMesh.LiftedFaces

namespace GridLiftedMesh.LiftedMesh

variable {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
  Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {faces : PuncturedFaces bank}

/-- Every oriented triangle-edge occurrence in the actual lifted mesh is unique.

The proof uses the retained regular-face separation and exact lifted quadrilaterals; reversed shared occurrences remain
distinct. -/
theorem orientedEdges_unique (mesh : LiftedMesh vertices edges faces) :
    (triangleEdgeOccurrences mesh.triangulation.faces).Nodup := by
  rw [mesh.triangleEdges_eq]
  exact mesh.lifts.triangleEdges_nodup faces.regulars_pairwise

open Purelib.Topology in
/-- Construct the sewing forest's single-polygon certificate from actual dual connectivity.

The lifted mesh supplies its proved oriented-edge uniqueness, so the only extra geometric evidence is the retained dual
connection. -/
@[expose] def singlePolygon (mesh : LiftedMesh vertices edges faces) (forest : Topology.Surface.Sewing.SewingForest
  mesh.triangulation.faces)
    (connected : Mesh.DualWalks.DualConnection mesh.triangulation.faces) :
      Surface.Sewing.SewingConnected.SewingForest.SinglePolygon forest :=
  Surface.Sewing.SewingConnected.SewingForest.singlePolygon forest mesh.orientedEdges_unique connected

end GridLiftedMesh.LiftedMesh

end Purelib.Riemann.Meshes
