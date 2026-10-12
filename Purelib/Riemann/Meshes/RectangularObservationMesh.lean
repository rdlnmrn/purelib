module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Content
import Purelib.Geometry.Rational.Box.Gaussian.Corners
import Purelib.Geometry.Rational.Box.Refinement

import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry
import Purelib.Topology.Mesh.CoordinateTriangulation
public import Purelib.Polynomial.Geometry.Grid.Rectangle.Cuts
public import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Geometry.Rectangle.Partition.RectangularMeshRefinement
import Purelib.Tactic.Ring

open Purelib.Riemann

public section

/-!
# Observation rectangles on an existing local model bank

Only geometry is cut: the actual cached coarse-model axes and their owners
are retained. Every returned triangle lies both in its original model box
and in the observation rectangle, and its total coordinate area is exactly
the observation area. Arbitrary rational observation sides are permitted.
-/

section

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian Coordinate)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (cells)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation (boxTriangles)
open Purelib.Topology.Mesh.CoordinateTriangulation (CoordinateTriangle)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Data.List
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration
open Purelib.Riemann.Topology

variable {columns rows : Nat} {geometry : Geometry columns rows}

section

namespace Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts

/-- Represent the retained grid axes by points on the observation rectangle's lower sides. -/
@[expose] def rectanglePoints
    (cuts : GridCuts geometry) (box : Box) : List Gaussian :=
  (cuts.x.map fun x => ⟨x, box.yLower⟩) ++ (cuts.y.map fun y => ⟨box.xLower, y⟩)

end Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.GridCuts

/-- A cell containing an interior point spans the interval when both its endpoints avoid that interval's interior. -/
private theorem axis_refines {lower upper first last point : Coordinate}
    (inside : lower < point ∧ point < upper) (contains : first ≤ point ∧ point ≤ last)
    (firstOutside : first ≤ lower ∨ upper ≤ first) (lastOutside : last ≤ lower ∨ upper ≤ last) :
    first ≤ lower ∧ upper ≤ last := by
  constructor
  · rcases firstOutside with bound | bound
    · exact bound
    · exact (not_lt_of_ge (bound.trans contains.1) inside.2).elim
  · rcases lastOutside with bound | bound
    · exact (not_lt_of_ge (contains.2.trans bound) inside.1).elim
    · exact bound

end Purelib.Riemann.Meshes.RectangularObservationMesh.GridCuts

namespace Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts

open Purelib.Data in
open Purelib.Geometry in
/-- A partition rectangle refines any model box containing one of its interior points.

The partition includes every retained grid-axis cut, preventing the rectangle from crossing the selected model box's
sides. -/
theorem rectangle_refines
    (cuts : GridCuts geometry) {box small : Box} {points : List Gaussian}
    (partition : Geometry.Rectangle.CutPartition box points)
    (includes : ∀ point, point ∈ cuts.rectanglePoints box → point ∈ points) (member : small ∈ partition.boxes)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) {point : Gaussian}
    (inside : small.StrictContains point) (contains : (geometry.box column row).Contains point) :
    small.Refines (geometry.box column row) := by
  rw [partition.boxes_eq] at member
  obtain ⟨x, xMember, rowMember⟩ := List.Flatten.mem_flatMap.mp member
  obtain ⟨y, yMember, rfl⟩ := List.Map.mem_map.mp rowMember
  have xOutside (index : Fin (columns + 2)) := partition.x.cut_outside xMember
    (List.Map.mem_map.mpr ⟨⟨geometry.x.coordinates index, box.yLower⟩,
      includes _ (List.mem_append_left _ (List.Map.mem_map.mpr ⟨_, cuts.x_mem index, rfl⟩)), rfl⟩)
  have yOutside (index : Fin (rows + 2)) := partition.y.cut_outside yMember
    (List.Map.mem_map.mpr ⟨⟨box.xLower, geometry.y.coordinates index⟩,
      includes _ (List.mem_append_right _ (List.Map.mem_map.mpr ⟨_, cuts.y_mem index, rfl⟩)), rfl⟩)
  have horizontal := Meshes.RectangularObservationMesh.GridCuts.axis_refines ⟨inside.1,
    inside.2.1⟩ ⟨contains.1, contains.2.1⟩
    (xOutside column.castSucc) (xOutside column.succ)
  have vertical :=
    Meshes.RectangularObservationMesh.GridCuts.axis_refines inside.2.2 contains.2.2
      (yOutside row.castSucc) (yOutside row.succ)
  exact ⟨horizontal.1, horizontal.2, vertical.1, vertical.2⟩

end Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts

end

namespace Purelib.Riemann.Meshes.RectangularObservationMesh

set_option genInjectivity false in
/-- An ordered list of observation boxes with their original model owners.

Each constructor retains a column, row and refinement proof for one exact box; later triangle occurrences reuse that
owner. -/
inductive ObservationPieces (geometry : Geometry columns rows) : List Box → Type
  /-- The empty box list has no retained model-owner entries. -/ | nil : ObservationPieces geometry []
  /-- Retain one model owner and box-refinement certificate before the remaining pieces. -/ | cons {box : Box} {boxes :
    List Box} (column : Fin (columns + 1)) (row : Fin (rows + 1))
      (refines : box.Refines (geometry.box column row)) (tail : ObservationPieces geometry boxes) :
      ObservationPieces geometry (box :: boxes)

constructive_injectivity ObservationPieces

end Purelib.Riemann.Meshes.RectangularObservationMesh

section

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationPieces

open Purelib.Riemann in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- Locate and retain an original model owner for each observation partition box.

The partition includes every grid cut and lies under the model geometry; locating each box center yields a box-wide
refinement certificate. -/
@[expose] def build (cuts : GridCuts geometry) {box : Box} {points : List Gaussian}
    (partition : Geometry.Rectangle.CutPartition box points)
    (includes : ∀ point, point ∈ cuts.rectanglePoints box → point ∈ points)
    (covers : ∀ point, box.Contains point → Paths.RectangularSegmentSplitting.Geometry.Covers geometry point) :
    (boxes : List Box) → (∀ small, small ∈ boxes → small ∈ partition.boxes) → ObservationPieces geometry boxes
  | [], _ => .nil
  | first :: rest, member =>
      let present := member first List.mem_cons_self
      let proper := partition.proper present
      let center := Geometry.Grid.Rectangle.Cuts.center first
      let inside := covers center ((partition.refines present).contains (Geometry.Grid.Rectangle.Cuts.center_inside
        proper))
      let horizontal := Rectangle.Partition.RectangularUniformGeometry.Axis.locate geometry.x center.re inside.1
        inside.2.1
      let vertical := Rectangle.Partition.RectangularUniformGeometry.Axis.locate geometry.y center.im inside.2.2.1
        inside.2.2.2
      .cons horizontal.index vertical.index
        (cuts.rectangle_refines partition includes present horizontal.index vertical.index
          (Geometry.Grid.Rectangle.Cuts.center_strict proper)
          ⟨horizontal.inside.1, horizontal.inside.2, vertical.inside.1, vertical.inside.2⟩)
        (build cuts partition includes covers rest (fun small present => member small (List.mem_cons_of_mem _ present)))

open Purelib.Geometry
/-- Uniformly subdivide each retained piece and attach its original model owner to the resulting triangles.

Every descendant reuses the same retained column, row and refinement proof.
The head fiber precedes the recursively constructed tail fiber. -/
@[expose] def triangles (depth : Nat) : {boxes : List Box} → ObservationPieces geometry boxes → List (ModelTriangle
  geometry)
  | _, .nil => []
  | box :: _, .cons column row refines tail =>
      Rectangle.Partition.RectangularMeshRefinement.ModelTriangle.fromBoxes geometry column row
        (Rectangle.Partition.PreparedBoxPartitions.cells depth box)
        (fun _ member => (Rectangle.Partition.PreparedBoxPartitions.cells_refine depth box member).trans refines) ++
          tail.triangles depth

/-- Triangulating a concatenated box list concatenates the two triangle lists.

The original box spine contributes two triangles at each head. Constructor
congruence preserves those heads while comparing the retained tail lists. -/
private theorem boxTriangles_append (first last : List Box) : Rectangle.Partition.PreparedBoxTriangulation.boxTriangles
  (first ++ last) = Rectangle.Partition.PreparedBoxTriangulation.boxTriangles first ++
  Rectangle.Partition.PreparedBoxTriangulation.boxTriangles last := by
  induction first with
  | nil => rfl
  | cons box rest ih =>
      change _ :: _ :: Rectangle.Partition.PreparedBoxTriangulation.boxTriangles (rest ++ last) = _
      exact congrArg (List.cons _) (congrArg (List.cons _) ih)

/-- Forgetting model owners yields the exact box triangulation of the refined piece list.

Each retained box contributes its original ordered triangle pair. Concatenating
the mapped head fiber with the unchanged tail preserves that same list. -/
theorem coordinates {boxes : List Box} (pieces : ObservationPieces geometry boxes) (depth : Nat) :
    (pieces.triangles depth).map ModelTriangle.triangle = Rectangle.Partition.PreparedBoxTriangulation.boxTriangles
      (boxes.flatMap (Rectangle.Partition.PreparedBoxPartitions.cells depth)) := by
  induction pieces with
  | nil => rfl
  | cons column row refines tail ih =>
      rewrite [triangles, Map.map_append,
        Rectangle.Partition.RectangularMeshRefinement.ModelTriangle.fromBoxes_coordinates,
        Flatten.flatMap_cons, boxTriangles_append, ih]
      exact Eq.refl _

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationPieces

end

namespace Purelib.Riemann.Meshes.RectangularObservationMesh

open Purelib.Geometry in
set_option genInjectivity false in
/-- A finite observation triangulation retaining its coarse cuts and original model owners.

The cached refined boxes and triangles carry exact construction equations, while the owned surface retains their actual
coordinate realization. -/
structure ObservationMesh (cuts : GridCuts geometry) (box : Box) where
  /-- The retained finite set of partition cut points. -/ points : List Gaussian
  /-- Every retained grid-axis cut is included among the partition points. -/ includes : ∀ point, point ∈
    cuts.rectanglePoints box → point ∈ points
  /-- The certified partition of the observation rectangle. -/ partition :
    Geometry.Rectangle.CutPartition box points
  /-- The retained original model owner for each exact partition box. -/ pieces : ObservationPieces geometry
    partition.boxes
  /-- The uniform spatial refinement depth within each retained piece. -/ depth : Nat
  /-- The cached ordered list of refined boxes. -/ boxes : List Box
  /-- The box cache is exactly the concatenation of the depth-refined partition boxes. -/ boxes_eq : boxes =
    partition.boxes.flatMap (Rectangle.Partition.PreparedBoxPartitions.cells depth)
  /-- The cached triangles with their retained model owners. -/ triangles : List (ModelTriangle geometry)
  /-- The triangle cache is exactly the retained pieces' triangulation at the chosen depth. -/ triangles_eq : triangles
    = pieces.triangles depth
  /-- The retained coordinate triangulation of the exact owned triangle list. -/ surface : OwnedTriangulation triangles

constructive_injectivity ObservationMesh

end Purelib.Riemann.Meshes.RectangularObservationMesh

section

variable {cuts : GridCuts geometry} {box : Box}

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

open Purelib.Riemann in
open Purelib.Geometry in
/-- Partition an observation rectangle and retain its refined owned triangulation.

The rectangle is proper and covered by the model geometry; the supplied points include all existing coarse grid cuts. -/
@[expose] def build (cuts : GridCuts geometry) (box : Box) (proper : box.Proper)
    (covers : ∀ point, box.Contains point → Paths.RectangularSegmentSplitting.Geometry.Covers geometry point)
    (points : List Gaussian) (includes : ∀ point, point ∈ cuts.rectanglePoints box → point ∈ points)
    (depth : Nat) : ObservationMesh cuts box :=
  let partition := Geometry.Rectangle.CutPartition.build box proper points
  let pieces :=
    Meshes.RectangularObservationMesh.ObservationPieces.build cuts partition includes covers partition.boxes
      (fun _ member => member)
  let boxes := partition.boxes.flatMap (Rectangle.Partition.PreparedBoxPartitions.cells depth)
  let triangles := pieces.triangles depth
  ⟨points, includes, partition, pieces, depth, boxes, rfl, triangles, rfl, OwnedTriangulation.build triangles⟩

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

section
open Purelib.Geometry

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

/-- Retriangulate the retained coarse pieces at a new spatial depth.

Reuse the original partition, cut points and model owners without repeating grid location or constructing new analytic
models. -/
@[expose] def atDepth (mesh : ObservationMesh cuts box) (depth : Nat) : ObservationMesh cuts box :=
  let boxes := mesh.partition.boxes.flatMap (Rectangle.Partition.PreparedBoxPartitions.cells depth)
  let triangles := mesh.pieces.triangles depth
  ⟨mesh.points, mesh.includes, mesh.partition, mesh.pieces, depth, boxes, rfl, triangles, rfl, OwnedTriangulation.build
    triangles⟩

/-- Read the cached owned triangles as the exact triangulation of the cached boxes. -/
theorem coordinates (mesh : ObservationMesh cuts box) : mesh.triangles.map ModelTriangle.triangle =
  Rectangle.Partition.PreparedBoxTriangulation.boxTriangles mesh.boxes := by
  rw [mesh.triangles_eq, mesh.pieces.coordinates, mesh.boxes_eq]

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

end

section
open Purelib.Data
open Purelib.Geometry

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

/-- Every cached refined box lies inside the observation rectangle. -/
theorem box_refines (mesh : ObservationMesh cuts box) {small : Box} (member : small ∈ mesh.boxes) : small.Refines box :=
  by
  rw [mesh.boxes_eq] at member
  obtain ⟨parent, present, member⟩ := List.Flatten.mem_flatMap.mp member
  exact (Rectangle.Partition.PreparedBoxPartitions.cells_refine mesh.depth parent member).trans (mesh.partition.refines
    present)

/-- Every cached refined box has positive width and height. -/
theorem box_proper (mesh : ObservationMesh cuts box) {small : Box} (member : small ∈ mesh.boxes) : small.Proper := by
  rw [mesh.boxes_eq] at member
  obtain ⟨parent, present, member⟩ := List.Flatten.mem_flatMap.mp member
  exact Rectangle.Partition.PreparedBoxPartitions.cells_proper mesh.depth (mesh.partition.proper present) member

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

end

section
open Purelib.Geometry

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

/-- Uniform box refinement preserves the summed rational area.

The head fiber has the same area as its original box, and concatenation adds
that area to the structurally retained tail contribution. -/
private theorem refined_content (boxes : List Box) (depth : Nat) :
    Rectangle.Partition.PreparedBoxPartitions.sumCells Rational.Box.Content.boxContent (boxes.flatMap
      (Rectangle.Partition.PreparedBoxPartitions.cells depth)) =
      Rectangle.Partition.PreparedBoxPartitions.sumCells Rational.Box.Content.boxContent boxes := by
  induction boxes with
  | nil => rfl
  | cons box rest ih =>
      rewrite [Flatten.flatMap_cons, Rectangle.Partition.PreparedBoxPartitions.sumCells_append,
        Rectangle.Partition.PreparedBoxPartitions.cells_content, ih]
      exact Eq.refl _

/-- The sum of the retained triangles' coordinate areas is exactly the observation rectangle's area. -/
theorem area_eq (mesh : ObservationMesh cuts box) :
    Rectangle.Partition.PreparedBoxTriangulation.sumTriangleAreas (mesh.triangles.map ModelTriangle.triangle) =
      Rational.Box.Content.boxContent box := by
  rw [mesh.coordinates, Rectangle.Partition.PreparedBoxTriangulation.boxTriangles_areaSum, mesh.boxes_eq,
    refined_content, mesh.partition.area_eq]

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

end

section
open Purelib.Topology
open Purelib.Geometry

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

/-- Every retained coordinate triangle has strictly positive area. -/
theorem positive (mesh : ObservationMesh cuts box) {triangle : Mesh.CoordinateTriangulation.CoordinateTriangle}
    (member : triangle ∈ mesh.triangles.map ModelTriangle.triangle) : 0 <
      Rectangle.Partition.PreparedBoxTriangulation.coordinateArea triangle := by
  rw [mesh.coordinates] at member
  exact Rectangle.Partition.PreparedBoxTriangulation.boxTriangles_positive _ (fun _ member => mesh.box_proper member)
    member

/-- Triangulated boxes refining a parent have all three vertices inside that parent.

Membership identifies an actual head triangle or retained tail occurrence.
The original refinement certificate places that occurrence's three corners in
the same parent box. -/
private theorem boxTriangles_inside (parent : Box) (boxes : List Box)
    (refines : ∀ small, small ∈ boxes → small.Refines parent) {triangle :
      Mesh.CoordinateTriangulation.CoordinateTriangle}
    (member : triangle ∈ Rectangle.Partition.PreparedBoxTriangulation.boxTriangles boxes) :
    parent.Contains triangle.first ∧ parent.Contains triangle.second ∧ parent.Contains triangle.third := by
  induction boxes with
  | nil => cases member
  | cons first rest ih =>
      have within := refines first List.mem_cons_self
      have lowerLeft : parent.Contains (Rational.Box.Gaussian.Corners.lowerLeft first) :=
        within.contains ⟨le_rfl, first.x_valid, le_rfl, first.y_valid⟩
      have upperRight : parent.Contains (Rational.Box.Gaussian.Corners.upperRight first) :=
        within.contains ⟨first.x_valid, le_rfl, first.y_valid, le_rfl⟩
      rcases Membership.mem_cons.mp member with rfl | member
      · exact ⟨lowerLeft, within.contains ⟨first.x_valid, le_rfl, le_rfl, first.y_valid⟩, upperRight⟩
      · rcases Membership.mem_cons.mp member with rfl | member
        · exact ⟨lowerLeft, upperRight, within.contains ⟨le_rfl, first.x_valid, first.y_valid, le_rfl⟩⟩
        · exact ih (fun small present => refines small (List.mem_cons_of_mem _ present)) member

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

end

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

/-- All three actual mesh vertices of every retained face lie in the observation rectangle. -/
theorem face_inside (mesh : ObservationMesh cuts box) (face : Fin (mesh.triangles.map ModelTriangle.triangle).length) :
    let triangle := mesh.surface.mesh.triangulation.faces face
    box.Contains (mesh.surface.mesh.coordinate triangle.first) ∧
    box.Contains (mesh.surface.mesh.coordinate triangle.second) ∧ box.Contains (mesh.surface.mesh.coordinate
      triangle.third) := by
  have coordinates := mesh.surface.mesh.face_coordinates face
  dsimp only
  rw [coordinates.1, coordinates.2.1, coordinates.2.2]
  apply boxTriangles_inside box mesh.boxes (fun _ member => mesh.box_refines member)
  rw [← mesh.coordinates]
  exact List.getElem_mem _

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

section
open Purelib.Geometry

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

/-- Uniform refinement produces four to the depth boxes per original box.

Each original box contributes one fiber with that exact length. Structural
concatenation adds the fiber lengths without changing the retained order. -/
private theorem refined_length (boxes : List Box) (depth : Nat) :
    (boxes.flatMap (Rectangle.Partition.PreparedBoxPartitions.cells depth)).length = boxes.length * 4 ^ depth := by
  induction boxes with
  | nil => exact (Nat.zero_mul _).symm
  | cons box rest ih =>
      rewrite [Flatten.flatMap_cons, Append.length_append, Rectangle.Partition.PreparedBoxPartitions.cells_length, ih,
        List.length_cons]
      ring1

/-- The retained mesh has twice four to its depth triangles per coarse partition box. -/
theorem face_count (mesh : ObservationMesh cuts box) :
    (mesh.triangles.map ModelTriangle.triangle).length = mesh.partition.boxes.length * (2 * 4 ^ mesh.depth) := by
  rw [mesh.coordinates, Rectangle.Partition.PreparedBoxTriangulation.boxTriangles_length, mesh.boxes_eq, refined_length]
  ring1

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

end

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

open Purelib.Approximation in
open Purelib.Data in
open Purelib.Geometry in
/-- Every refined box diagonal is bounded by the observation diagonal scaled by the dyadic quarter-radius. -/
theorem box_diagonal_le (mesh : ObservationMesh cuts box) {small : Box} (member : small ∈ mesh.boxes) :
    small.diagonalSq ≤ Rational.Geometric.Basic.quarterRadius box.diagonalSq mesh.depth := by
  rw [mesh.boxes_eq] at member
  obtain ⟨parent, present, member⟩ := List.Flatten.mem_flatMap.mp member
  rw [Rectangle.Partition.PreparedBoxPartitions.cells_diagonalSq mesh.depth parent member,
    Rational.Geometric.Basic.quarterRadius_eq_mul_pow, Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
  exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Rational.Box.diagonalSq_le_of_refines (mesh.partition.refines present))
    (Rat.Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) mesh.depth)

open Purelib.Topology in
open Purelib.Data in
open Purelib.Geometry in
/-- A common box-diagonal bound controls both triangle displacements from the first vertex.

The displayed triangle occurrence retains its original box membership. Its
corner containment and that box's diagonal estimate bound both displacements. -/
private theorem boxTriangles_movement (boxes : List Box) (distance : Coordinate)
    (bounded : ∀ small, small ∈ boxes → small.diagonalSq ≤ distance)
    {triangle : Mesh.CoordinateTriangulation.CoordinateTriangle} (member : triangle ∈
      Rectangle.Partition.PreparedBoxTriangulation.boxTriangles boxes) :
    Gaussian.Norm.Basic.normSq (triangle.second - triangle.first) ≤ distance ∧
      Gaussian.Norm.Basic.normSq (triangle.third - triangle.first) ≤ distance := by
  induction boxes with
  | nil => cases member
  | cons box rest ih =>
      have within (triangle : Mesh.CoordinateTriangulation.CoordinateTriangle) (present : triangle ∈
        Rectangle.Partition.PreparedBoxTriangulation.boxTriangles [box]) :=
        boxTriangles_inside box [box]
          (fun _ member => (Membership.mem_singleton.mp member) ▸ Rational.Box.refines_refl box) present
      have estimate (triangle : Mesh.CoordinateTriangulation.CoordinateTriangle) (present : triangle ∈
        Rectangle.Partition.PreparedBoxTriangulation.boxTriangles [box]) :=
        let inside := within triangle present
        (⟨(Rational.Box.normSq_sub_le_diagonalSq inside.2.1 inside.1).trans (bounded box
          List.mem_cons_self),
          (Rational.Box.normSq_sub_le_diagonalSq inside.2.2 inside.1).trans (bounded box
            List.mem_cons_self)⟩ :
          Gaussian.Norm.Basic.normSq (triangle.second - triangle.first) ≤ distance ∧
            Gaussian.Norm.Basic.normSq (triangle.third - triangle.first) ≤ distance)
      rcases Membership.mem_cons.mp member with rfl | member
      · exact estimate _ List.mem_cons_self
      · rcases Membership.mem_cons.mp member with rfl | member
        · exact estimate _ (List.mem_cons_of_mem _ List.mem_cons_self)
        · exact ih (fun small present => bounded small (List.mem_cons_of_mem _ present)) member

open Purelib.Approximation in
open Purelib.Data in
/-- Bound both actual face displacements by the observation diagonal's refined quarter-radius.

The estimates apply to the retained surface coordinates and its exact owned triangle list. -/
theorem face_movement_le (mesh : ObservationMesh cuts box)
    (index : Fin (mesh.triangles.map ModelTriangle.triangle).length) :
    let triangle := mesh.surface.mesh.triangulation.faces index
    Gaussian.Norm.Basic.normSq (mesh.surface.mesh.coordinate triangle.second - mesh.surface.mesh.coordinate
      triangle.first) ≤
        Rational.Geometric.Basic.quarterRadius box.diagonalSq mesh.depth ∧
      Gaussian.Norm.Basic.normSq (mesh.surface.mesh.coordinate triangle.third - mesh.surface.mesh.coordinate
        triangle.first) ≤
        Rational.Geometric.Basic.quarterRadius box.diagonalSq mesh.depth := by
  have coordinates := mesh.surface.mesh.face_coordinates index
  dsimp only
  rw [coordinates.1, coordinates.2.1, coordinates.2.2]
  apply boxTriangles_movement mesh.boxes _ (fun _ member => mesh.box_diagonal_le member)
  rw [← mesh.coordinates]
  exact List.getElem_mem _

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

end
end

end
