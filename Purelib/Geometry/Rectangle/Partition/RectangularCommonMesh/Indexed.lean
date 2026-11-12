module

public import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Geometry.Rectangle.Partition.RectangularMeshRefinement
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Topology.Mesh.CoordinateTriangulation
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Flatten

/-! # Original cell and rectangle occurrences in a retained common mesh

The constructors follow actual stored spines and bounded rectangle positions.
They return indices in the unchanged triangle lists; no cell, partition,
triangle or coordinate lookup is prepared again. Repeated selections keep
their distinct original positions and their complete original payloads.
-/

public section

namespace Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh

open Purelib
open Purelib.Data.List
open Purelib.Geometry.Rectangle.Partition
open Purelib.Geometry.Rational (Box)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation (boxTriangles lowerTriangle upperTriangle)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Topology.Mesh
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Topology.Surface.Sewing

namespace RectangularInverseModels

variable {columns rows : Nat} {geometry : Geometry columns rows}
    {points : List Data.Gaussian.Basic.Canonical}

namespace CutCells

/-- Read the complete original cell at its retained selection position. -/
@[expose] def get : {selection : List (Fin (columns + 1) × Fin (rows + 1))} →
    (cells : CutCells geometry points selection) → (position : Fin selection.length) →
    CutCell geometry (selection[position.val]'position.isLt).1 (selection[position.val]'position.isLt).2 points
  | _, .nil, position => Fin.elim0 position
  | _, .cons cell _, ⟨0, _⟩ => cell
  | _, .cons _ rest, ⟨index + 1, bound⟩ => get rest ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- Embed one actual cell's triangle index in the original concatenated triangle bank. -/
@[expose] def faceIndex : {selection : List (Fin (columns + 1) × Fin (rows + 1))} →
    (cells : CutCells geometry points selection) → (position : Fin selection.length) →
    Fin (cells.get position).triangles.length → Fin cells.triangles.length
  | _, .nil, position, _ => Fin.elim0 position
  | _, .cons cell rest, ⟨0, _⟩, localIndex =>
      ⟨localIndex.val, Eq.mp (congrArg (fun size : Nat => localIndex.val < size)
        (Append.length_append cell.triangles rest.triangles).symm)
        (localIndex.isLt.trans_le (Nat.le_add_right _ _))⟩
  | _, .cons cell rest, ⟨index + 1, bound⟩, localIndex =>
      let tail := faceIndex rest ⟨index, Nat.lt_of_succ_lt_succ bound⟩ localIndex
      ⟨cell.triangles.length + tail.val,
        Eq.mp (congrArg (fun size : Nat => cell.triangles.length + tail.val < size)
          (Append.length_append cell.triangles rest.triangles).symm)
          (Nat.add_lt_add_left tail.isLt _)⟩

/-- The selected triangle is the same complete original triangle, including its coarse owner and containment data. -/
theorem faceIndex_entry : {selection : List (Fin (columns + 1) × Fin (rows + 1))} →
    (cells : CutCells geometry points selection) → (position : Fin selection.length) →
    (localIndex : Fin (cells.get position).triangles.length) →
    cells.triangles[(cells.faceIndex position localIndex).val]'(cells.faceIndex position localIndex).isLt =
      (cells.get position).triangles[localIndex.val]'localIndex.isLt
  | _, .nil, position, _ => Fin.elim0 position
  | _, .cons cell rest, ⟨0, _⟩, localIndex =>
      Append.getElem_append_left cell.triangles rest.triangles localIndex.val localIndex.isLt _
  | _, .cons cell rest, ⟨index + 1, bound⟩, localIndex =>
      let inner : Fin _ := ⟨index, Nat.lt_of_succ_lt_succ bound⟩
      let tail := rest.faceIndex inner localIndex
      (Append.getElem_append_right cell.triangles rest.triangles tail.val tail.isLt _).trans
        (faceIndex_entry rest inner localIndex)

end CutCells

namespace CutCell

/-- Each retained rectangle occurrence has one lower and one upper coordinate-triangle position. -/
private def boxFaceIndex : (boxes : List Box) → (position : Fin boxes.length) →
    Bool → Fin (boxTriangles boxes).length
  | [], position, _ => Fin.elim0 position
  | _ :: _, ⟨0, _⟩, false => ⟨0, Nat.zero_lt_succ _⟩
  | _ :: _, ⟨0, _⟩, true => ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩
  | _ :: rest, ⟨index + 1, bound⟩, upper =>
      (boxFaceIndex rest ⟨index, Nat.lt_of_succ_lt_succ bound⟩ upper).succ.succ

/-- The coordinate face at that position is the lower or upper triangle of the same original rectangle. -/
private theorem boxFaceIndex_entry : (boxes : List Box) →
    (position : Fin boxes.length) → (upper : Bool) →
    (boxTriangles boxes)[(boxFaceIndex boxes position upper).val]'(boxFaceIndex boxes position upper).isLt =
      if upper then upperTriangle (boxes[position.val]'position.isLt)
      else lowerTriangle (boxes[position.val]'position.isLt)
  | [], position, _ => Fin.elim0 position
  | _ :: _, ⟨0, _⟩, false => rfl
  | _ :: _, ⟨0, _⟩, true => rfl
  | _ :: rest, ⟨index + 1, bound⟩, upper =>
      boxFaceIndex_entry rest ⟨index, Nat.lt_of_succ_lt_succ bound⟩ upper

variable {column : Fin (columns + 1)} {row : Fin (rows + 1)}

/-- Embed a retained rectangle's lower or upper face in the SAME original owned cell triangle cache. -/
def faceIndex (cell : CutCell geometry column row points) (position : Fin cell.partition.boxes.length)
    (upper : Bool) : Fin cell.triangles.length :=
  let index := boxFaceIndex cell.partition.boxes position upper
  let lengthEq : cell.triangles.length = (boxTriangles cell.partition.boxes).length :=
    (Map.length_map ModelTriangle.triangle cell.triangles).symm.trans (congrArg List.length cell.coordinates)
  ⟨index.val, Eq.mp (congrArg (fun size : Nat => index.val < size) lengthEq.symm) index.isLt⟩

/-- The embedded face preserves the exact original rectangle's oriented coordinate triangle. -/
theorem faceIndex_triangle (cell : CutCell geometry column row points)
    (position : Fin cell.partition.boxes.length) (upper : Bool) :
    (cell.triangles[(cell.faceIndex position upper).val]'(cell.faceIndex position upper).isLt).triangle =
      if upper then upperTriangle (cell.partition.boxes[position.val]'position.isLt)
      else lowerTriangle (cell.partition.boxes[position.val]'position.isLt) := by
  let index := boxFaceIndex cell.partition.boxes position upper
  have bounded : index.val < (cell.triangles.map ModelTriangle.triangle).length :=
    Eq.mp (congrArg (fun size : Nat => index.val < size) (congrArg List.length cell.coordinates).symm) index.isLt
  exact (Map.getElem_map ModelTriangle.triangle cell.triangles index.val
    (cell.faceIndex position upper).isLt bounded).symm.trans
      ((getElem_congr cell.coordinates rfl bounded).trans (boxFaceIndex_entry _ position upper))

end CutCell

namespace CommonMesh

variable {selection : List (Fin (columns + 1) × Fin (rows + 1))}

/-- Embed the actual rectangle-face occurrence through the stored cell spine into the SAME common triangle cache. -/
def faceIndex (mesh : CommonMesh geometry selection points) (cellPosition : Fin selection.length)
    (rectangle : Fin (mesh.cells.get cellPosition).partition.boxes.length) (upper : Bool) :
    Fin mesh.triangles.length :=
  let localIndex := (mesh.cells.get cellPosition).faceIndex rectangle upper
  let selected := mesh.cells.faceIndex cellPosition localIndex
  ⟨selected.val, Eq.mp (congrArg (fun size : Nat => selected.val < size)
    (congrArg List.length mesh.triangles_eq).symm) selected.isLt⟩

/-- The common face retains its original selected cell and exact rectangle-coordinate triangle. -/
theorem faceIndex_triangle (mesh : CommonMesh geometry selection points) (cellPosition : Fin selection.length)
    (rectangle : Fin (mesh.cells.get cellPosition).partition.boxes.length) (upper : Bool) :
    (mesh.triangles[(mesh.faceIndex cellPosition rectangle upper).val]'
      (mesh.faceIndex cellPosition rectangle upper).isLt).triangle =
      if upper then upperTriangle ((mesh.cells.get cellPosition).partition.boxes[rectangle.val]'rectangle.isLt)
      else lowerTriangle ((mesh.cells.get cellPosition).partition.boxes[rectangle.val]'rectangle.isLt) := by
  let localIndex := (mesh.cells.get cellPosition).faceIndex rectangle upper
  exact (congrArg ModelTriangle.triangle (getElem_congr mesh.triangles_eq rfl
    (mesh.faceIndex cellPosition rectangle upper).isLt)).trans
      ((congrArg ModelTriangle.triangle (mesh.cells.faceIndex_entry cellPosition localIndex)).trans
        ((mesh.cells.get cellPosition).faceIndex_triangle rectangle upper))

/-- The same original face occurrence has its bounded index in the retained coordinate-triangle table. -/
def coordinateFaceIndex (mesh : CommonMesh geometry selection points) (cellPosition : Fin selection.length)
    (rectangle : Fin (mesh.cells.get cellPosition).partition.boxes.length) (upper : Bool) :
    Fin (mesh.triangles.map ModelTriangle.triangle).length :=
  let original := mesh.faceIndex cellPosition rectangle upper
  ⟨original.val, Eq.mp (congrArg (fun size : Nat => original.val < size)
    (Map.length_map ModelTriangle.triangle mesh.triangles).symm) original.isLt⟩

/-- The indexed coordinate table reads the same actual rectangle's retained oriented face. -/
theorem coordinateFaceIndex_triangle (mesh : CommonMesh geometry selection points)
    (cellPosition : Fin selection.length)
    (rectangle : Fin (mesh.cells.get cellPosition).partition.boxes.length) (upper : Bool) :
    (mesh.triangles.map ModelTriangle.triangle)[(mesh.coordinateFaceIndex cellPosition rectangle upper).val]'
      (mesh.coordinateFaceIndex cellPosition rectangle upper).isLt =
      if upper then upperTriangle ((mesh.cells.get cellPosition).partition.boxes[rectangle.val]'rectangle.isLt)
      else lowerTriangle ((mesh.cells.get cellPosition).partition.boxes[rectangle.val]'rectangle.isLt) :=
  (Map.getElem_map ModelTriangle.triangle mesh.triangles
    (mesh.faceIndex cellPosition rectangle upper).val (mesh.faceIndex cellPosition rectangle upper).isLt
    (mesh.coordinateFaceIndex cellPosition rectangle upper).isLt).trans
      (mesh.faceIndex_triangle cellPosition rectangle upper)

/-- The actual indexed face has the same three ordered coordinates as its original retained rectangle triangle. -/
theorem face_coordinates (mesh : CommonMesh geometry selection points) (cellPosition : Fin selection.length)
    (rectangle : Fin (mesh.cells.get cellPosition).partition.boxes.length) (upper : Bool) :
    let triangle := if upper then upperTriangle ((mesh.cells.get cellPosition).partition.boxes[rectangle.val]'
      rectangle.isLt) else lowerTriangle ((mesh.cells.get cellPosition).partition.boxes[rectangle.val]'rectangle.isLt)
    let face := mesh.surface.mesh.triangulation.faces (mesh.coordinateFaceIndex cellPosition rectangle upper)
    mesh.surface.mesh.coordinate face.first = triangle.first ∧
      mesh.surface.mesh.coordinate face.second = triangle.second ∧
      mesh.surface.mesh.coordinate face.third = triangle.third := by
  have original := mesh.surface.mesh.face_coordinates (mesh.coordinateFaceIndex cellPosition rectangle upper)
  have actual := mesh.coordinateFaceIndex_triangle cellPosition rectangle upper
  exact ⟨original.1.trans (congrArg CoordinateTriangulation.CoordinateTriangle.first actual),
    original.2.1.trans (congrArg CoordinateTriangulation.CoordinateTriangle.second actual),
    original.2.2.trans (congrArg CoordinateTriangulation.CoordinateTriangle.third actual)⟩

/-- A horizontal side keeps the original rectangle-face source and its ordered corner roles. -/
def horizontalSource (mesh : CommonMesh geometry selection points) (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool) :
    SourceEdge (mesh.triangles.map ModelTriangle.triangle).length :=
  let rectangle := (mesh.cells.get cellPosition).partition.rectanglePosition column row
  let face := mesh.coordinateFaceIndex cellPosition rectangle.val high
  if high then ⟨face, 2, 1⟩ else ⟨face, 0, 1⟩

/-- A vertical side keeps the original rectangle-face source and its ordered corner roles. -/
def verticalSource (mesh : CommonMesh geometry selection points) (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool) :
    SourceEdge (mesh.triangles.map ModelTriangle.triangle).length :=
  let rectangle := (mesh.cells.get cellPosition).partition.rectanglePosition column row
  let face := mesh.coordinateFaceIndex cellPosition rectangle.val (!high)
  if high then ⟨face, 1, 2⟩ else ⟨face, 0, 2⟩

/-- A boundary edge of one actual original face belongs to the retained complete mesh edge list. -/
private theorem edge_mem {triangles : List CoordinateTriangulation.CoordinateTriangle}
    (surface : CoordinateTriangulation triangles) (source : Fin triangles.length)
    (edge : OrientedEdge surface.vertices.length) (member : edge ∈ (surface.triangulation.faces source).boundary) :
    edge ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences surface.triangulation.faces :=
  Flatten.mem_flatMap.mpr ⟨surface.triangulation.faces source, OfFn.Basic.mem_ofFn.mpr ⟨source, rfl⟩, member⟩

/-- Every computed horizontal side is an actual original mesh triangle edge, up to its retained reversal. -/
theorem horizontalSource_supported (mesh : CommonMesh geometry selection points) (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool) :
    let edge := (mesh.horizontalSource cellPosition column row high).project mesh.surface.mesh.triangulation.faces
    edge ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces ∨
      edge.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces := by
  cases high with
  | false =>
      refine Or.inl (edge_mem mesh.surface.mesh
        (mesh.horizontalSource cellPosition column row false).source _ ?_)
      change _ ∈ [_, _, _]
      exact List.mem_cons_self
  | true =>
      refine Or.inr (edge_mem mesh.surface.mesh
        (mesh.horizontalSource cellPosition column row true).source _ ?_)
      change _ ∈ [_, _, _]
      exact List.mem_cons_of_mem _ List.mem_cons_self

/-- Every computed vertical side is an actual original mesh triangle edge, up to its retained reversal. -/
theorem verticalSource_supported (mesh : CommonMesh geometry selection points) (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool) :
    let edge := (mesh.verticalSource cellPosition column row high).project mesh.surface.mesh.triangulation.faces
    edge ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces ∨
      edge.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces := by
  cases high with
  | false =>
      refine Or.inr (edge_mem mesh.surface.mesh
        (mesh.verticalSource cellPosition column row false).source _ ?_)
      change _ ∈ [_, _, _]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  | true =>
      refine Or.inl (edge_mem mesh.surface.mesh
        (mesh.verticalSource cellPosition column row true).source _ ?_)
      change _ ∈ [_, _, _]
      exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The computed horizontal source traverses its original adjacent interval at the selected lower or upper height. -/
theorem horizontalSource_coordinates (mesh : CommonMesh geometry selection points)
    (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool) :
    let horizontal := (mesh.cells.get cellPosition).partition.x.intervals[column.val]'column.isLt
    let vertical := (mesh.cells.get cellPosition).partition.y.intervals[row.val]'row.isLt
    let edge := (mesh.horizontalSource cellPosition column row high).project mesh.surface.mesh.triangulation.faces
    mesh.surface.mesh.coordinate edge.start =
        (⟨horizontal.lower, if high then vertical.upper else vertical.lower⟩ : Data.Gaussian.Basic.Canonical) ∧
      mesh.surface.mesh.coordinate edge.finish =
        (⟨horizontal.upper, if high then vertical.upper else vertical.lower⟩ : Data.Gaussian.Basic.Canonical) := by
  let rectangle := (mesh.cells.get cellPosition).partition.rectanglePosition column row
  cases high with
  | false =>
      have actual := mesh.face_coordinates cellPosition rectangle.val false
      exact ⟨actual.1.trans (congrArg (fun box : Box => (lowerTriangle box).first) rectangle.property),
        actual.2.1.trans (congrArg (fun box : Box => (lowerTriangle box).second) rectangle.property)⟩
  | true =>
      have actual := mesh.face_coordinates cellPosition rectangle.val true
      exact ⟨actual.2.2.trans (congrArg (fun box : Box => (upperTriangle box).third) rectangle.property),
        actual.2.1.trans (congrArg (fun box : Box => (upperTriangle box).second) rectangle.property)⟩

/-- The computed vertical source traverses the same original adjacent interval at the selected lower or upper column. -/
theorem verticalSource_coordinates (mesh : CommonMesh geometry selection points)
    (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool) :
    let horizontal := (mesh.cells.get cellPosition).partition.x.intervals[column.val]'column.isLt
    let vertical := (mesh.cells.get cellPosition).partition.y.intervals[row.val]'row.isLt
    let edge := (mesh.verticalSource cellPosition column row high).project mesh.surface.mesh.triangulation.faces
    mesh.surface.mesh.coordinate edge.start =
        (⟨if high then horizontal.upper else horizontal.lower, vertical.lower⟩ : Data.Gaussian.Basic.Canonical) ∧
      mesh.surface.mesh.coordinate edge.finish =
        (⟨if high then horizontal.upper else horizontal.lower, vertical.upper⟩ : Data.Gaussian.Basic.Canonical) := by
  let rectangle := (mesh.cells.get cellPosition).partition.rectanglePosition column row
  cases high with
  | false =>
      have actual := mesh.face_coordinates cellPosition rectangle.val true
      exact ⟨actual.1.trans (congrArg (fun box : Box => (upperTriangle box).first) rectangle.property),
        actual.2.2.trans (congrArg (fun box : Box => (upperTriangle box).third) rectangle.property)⟩
  | true =>
      have actual := mesh.face_coordinates cellPosition rectangle.val false
      exact ⟨actual.2.1.trans (congrArg (fun box : Box => (lowerTriangle box).second) rectangle.property),
        actual.2.2.trans (congrArg (fun box : Box => (lowerTriangle box).third) rectangle.property)⟩

/-- The actual common-mesh builder retains the canonical original coordinate-face indexing factory. -/
theorem surface_factory (mesh : CommonMesh geometry selection points)
    (factory : mesh = CommonMesh.build geometry selection points) :
    mesh.surface.mesh = CoordinateTriangulation.build (mesh.triangles.map ModelTriangle.triangle) := by
  cases factory
  rfl

end CommonMesh

end RectangularInverseModels

end Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh

end
