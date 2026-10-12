module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
public import Purelib.Riemann.Paths.ClearBoxPathWinding
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Geometry

open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Polynomial.Geometry.Grid.FromStates

public section

/-!
# Face containment of actual indexed mesh-edge occurrences

The selected lifted rectangle and orientation are retained. Containment uses
its exact corner coordinates, not equality with a separately prepared detour.
In particular an original grid segment keeps its own line-clearance payload.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Topology.Mesh.IndexedQuadrilaterals (IndexedQuadrilateral)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge (Kind)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedFaces LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces (EdgeLocation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (EdgeRoute)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

namespace Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

/-- Every retained lifted rectangle edge has both actual vertex coordinates inside the original face rectangle. -/
theorem edge_endpoints_inside {face :
  RegularFace bank} {sheet : Fin 2}
    (lifted : LiftedFace vertices edges face sheet) (kind : RectangleEdge.Kind) :
    face.cell.box.Contains (vertices.coordinate (lifted.quad.edge kind).start) ∧
      face.cell.box.Contains (vertices.coordinate (lifted.quad.edge kind).finish) := by
  have first : face.cell.box.Contains (vertices.coordinate lifted.quad.first) := by
    rw [lifted.coordinates.1]
    exact face.cell.box.contains_anchor
  have second : face.cell.box.Contains (vertices.coordinate lifted.quad.second) := by
    rw [lifted.coordinates.2.1]
    exact ⟨face.cell.box.x_valid, le_rfl, le_rfl, face.cell.box.y_valid⟩
  have third : face.cell.box.Contains (vertices.coordinate lifted.quad.third) := by
    rw [lifted.coordinates.2.2.1]
    exact ⟨face.cell.box.x_valid, le_rfl, face.cell.box.y_valid, le_rfl⟩
  have fourth : face.cell.box.Contains (vertices.coordinate lifted.quad.fourth) := by
    rw [lifted.coordinates.2.2.2]
    exact ⟨le_rfl, face.cell.box.x_valid, face.cell.box.y_valid, le_rfl⟩
  cases kind with
  | bottom => exact ⟨first, second⟩
  | right => exact ⟨second, third⟩
  | top => exact ⟨third, fourth⟩
  | left => exact ⟨fourth, first⟩
  | upDiagonal => exact ⟨first, third⟩
  | downDiagonal => exact ⟨third, first⟩

end Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation

/-- The selected original face contains both actual endpoints of the retained oriented edge occurrence. -/
theorem endpoints_inside {faces : List
  (RegularFace bank)}
    {lifts : LiftedFaces vertices edges faces} {edge : OrientedEdge vertices.count}
    (location : EdgeLocation lifts edge) :
    location.face.cell.box.Contains (vertices.coordinate edge.start) ∧
      location.face.cell.box.Contains (vertices.coordinate edge.finish) := by
  have inside := location.lifted.edge_endpoints_inside location.kind
  exact (congrArg (fun edge : OrientedEdge vertices.count =>
    location.face.cell.box.Contains (vertices.coordinate edge.start) ∧
      location.face.cell.box.Contains (vertices.coordinate edge.finish)) location.edge_eq).mp inside

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation

section

variable {faces : PuncturedFaces bank} {mesh : LiftedMesh vertices edges faces}

section

variable {edge : OrientedEdge vertices.count}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute

/-- Read the original regular face retained by this oriented edge route or segment placement. -/
@[expose] def face :
  MeshPathWalks.EdgeRoute mesh edge → RegularFace bank
  | .forward location => location.face
  | .backward location => location.face

/-- Read the original lifted sheet retained by this oriented edge route. -/
@[expose] def sheet :
  MeshPathWalks.EdgeRoute mesh edge → Fin 2
  | .forward location => location.sheet
  | .backward location => location.sheet

/-- Read the original lifted rectangle retained by the edge route with its exact face and sheet indices. -/
@[expose] def lifted : (route :
  MeshPathWalks.EdgeRoute mesh edge) → LiftedFace vertices edges route.face route.sheet
  | .forward location => location.lifted
  | .backward location => location.lifted

/-- The index is retained by the original lookup, so sharing a face-model bank requires no new membership search. -/
@[expose] def position :
  MeshPathWalks.EdgeRoute mesh edge → Fin faces.regulars.length
  | .forward location => location.position
  | .backward location => location.position

/-- The retained finite face position reads back the exact original selected face. -/
theorem face_eq (route :
  MeshPathWalks.EdgeRoute mesh edge) : faces.regulars[route.position.val] = route.face := by
  cases route with
  | forward location => exact location.face_eq
  | backward location => exact location.face_eq

/-- The selected original face occurs in the retained regular-face list. -/
theorem face_mem (route :
  MeshPathWalks.EdgeRoute mesh edge) : route.face ∈ faces.regulars := by
  cases route with
  | forward location => exact location.member
  | backward location => exact location.member

/-- The selected original face contains both actual endpoints of the retained oriented edge occurrence. -/
theorem endpoints_inside (route :
  MeshPathWalks.EdgeRoute mesh edge) :
    route.face.cell.box.Contains (vertices.coordinate edge.start) ∧
      route.face.cell.box.Contains (vertices.coordinate edge.finish) := by
  cases route with
  | forward location => exact location.endpoints_inside
  | backward location => exact ⟨location.endpoints_inside.2, location.endpoints_inside.1⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute

end

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh

set_option genInjectivity false in
/-- A stored lifted occurrence locates the original segment. No path or root-owner preparation is contained in this
geometric cache. -/
structure SegmentFace (mesh : LiftedMesh vertices edges faces)
  {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    (_segment : ClearPath.ClearSegment curve.polynomial ambient start finish) where
  /-- The retained oriented edge occurrence in the original vertex bank. -/ indexed : OrientedEdge vertices.count
  /-- The retained orientation and lifted face locating this exact edge occurrence. -/ location :
    MeshPathWalks.EdgeRoute mesh indexed
  /-- The original segment start equals the retained indexed start coordinate. -/ start_eq : vertices.coordinate
    indexed.start = start
  /-- The original segment finish equals the retained indexed finish coordinate. -/ finish_eq : vertices.coordinate
    indexed.finish = finish

constructive_injectivity Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.SegmentFace

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh

open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)

section

variable {ambient : Purelib.Geometry.Rational.Box} {start finish :
  Purelib.Data.Gaussian.Basic.Canonical}
  {segment : ClearSegment curve.polynomial ambient start finish}

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.SegmentFace

/-- Read the original regular face retained by this oriented edge route or segment placement. -/
@[expose] def face (placement : SegmentFace mesh
  segment) : RegularFace bank := placement.location.face

/-- The original segment lies in its retained face rectangle through its exact endpoint-coordinate equalities. -/
theorem inside (placement : SegmentFace mesh
  segment) :
    (ClearPath.cons segment (.nil finish)).InBox placement.face.cell.box := by
  change placement.face.cell.box.Contains start ∧ placement.face.cell.box.Contains finish
  exact ⟨(congrArg placement.face.cell.box.Contains placement.start_eq).mp placement.location.endpoints_inside.1,
    (congrArg placement.face.cell.box.Contains placement.finish_eq).mp placement.location.endpoints_inside.2⟩

/-- The original segment start is a vertex of the retained grid. -/
theorem start_onGrid (placement : SegmentFace mesh
  segment) : Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid start := by
  rw [← placement.start_eq]
  exact vertices.coordinate_onGrid _

/-- The original segment finish is a vertex of the retained grid. -/
theorem finish_onGrid (placement : SegmentFace mesh
  segment) : Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid finish := by
  rw [← placement.finish_eq]
  exact vertices.coordinate_onGrid _

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.SegmentFace

end

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh

set_option genInjectivity false in
/-- One selected face per original segment, preserving every repetition. -/
inductive PathFaces (mesh : LiftedMesh vertices edges faces)
  {ambient : Rational.Box} :
    {start finish : Data.Gaussian.Basic.Canonical} → Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish → Type
  /-- The empty original path has no face placements. -/ | nil (point : Data.Gaussian.Basic.Canonical) : PathFaces mesh
    (.nil point)
  /-- Retain the exact original head segment's face placement and the matching original path tail. -/ | cons {start
    middle finish : Data.Gaussian.Basic.Canonical} {head : ClearPath.ClearSegment curve.polynomial ambient start middle}
      {tail : Polynomial.Geometry.ClearPath curve.polynomial ambient middle finish}
      (first : SegmentFace mesh head) (remaining : PathFaces mesh tail) : PathFaces mesh (.cons head tail)

constructive_injectivity Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.PathFaces

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh

end
end
