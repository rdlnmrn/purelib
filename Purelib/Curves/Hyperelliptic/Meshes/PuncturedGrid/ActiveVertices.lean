module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
public import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Pairwise
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Topology.Mesh.CornerWalks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryCounts
import Purelib.Riemann.Meshes.GridLiftedTriangleStars
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.ClearGridCoverage
import Purelib.Polynomial.Geometry.Grid.Axis.Full
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.GridLiftedCornerConnections
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Riemann.Integration.PuncturedVertexStars
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Data.Gaussian.Components.Basic
import Init.Data.List.OfFn
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Topology.Polygon.Stokes
meta import Mathlib.Tactic.Linter.Lint

public section

/-!
# Exact enumeration of actual surface vertices

The canonical Cartesian grid has no repeated coordinates. Transfer its two
sheet indices into any retained vertex cache, then certify that this lists
exactly the vertices used by actual triangles. Duplicate unused cache slots
are not counted. No root preparation or geometric classification is repeated
by the executable enumeration; the incidence proofs use the retained lifts.
-/

namespace Purelib

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Data.Gaussian

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.Axis.Full

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.Polynomial.Geometry.Grid.FramedClearGrid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Riemann.Integration.PuncturedVertexStars

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.GridLiftedCornerConnections.FramedPuncturedGrid.RegularIncident

open Purelib.Riemann.Meshes.GridLiftedTriangleStars

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.CornerWalks

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Mesh.CoordinateTriangulation (vertexAt)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Interval VerticalLine HorizontalLine)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Topology.Mesh.CornerWalks.OrientedTriangle (ContainsVertex)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)

namespace Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices

/-- The adjacent-interval list of a nonempty ordered line list has one fewer entry. -/
private theorem adjacent_cons_length {Alpha : Type u} {key : Alpha → Fraction.Rational}
    (first : Alpha) (rest : List Alpha) (ordered : (first :: rest).Pairwise (fun x y => key x < key y)) :
    (Interval.adjacent (first :: rest) ordered).length = rest.length := by
  induction rest generalizing first with
  | nil => rfl
  | cons next tail ih => exact congrArg Nat.succ (ih next (List.pairwise_cons.mp ordered).2)

end Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices

namespace Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices

/-- A retained nonempty ordered span has exactly one more line than adjacent intervals. -/
private theorem span_length {Alpha : Type u} {key : Alpha → Fraction.Rational} {entries : List Alpha}
    {lower upper : Fraction.Rational}
    (span : Interval.Span (key := key) entries lower upper)
    (ordered : entries.Pairwise (fun x y => key x < key y)) :
    entries.length = (Interval.adjacent entries ordered).length + 1 := by
  rcases span with ⟨first, rest, rfl, _, _⟩
  rw [adjacent_cons_length, List.length_cons]

end Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices

namespace Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame

/-- The original framed grid has one more vertical line than horizontal coordinate intervals. -/
theorem vertical_length
    {polynomial : ClearPath.GaussianPolynomial} {ambient : Geometry.Rational.Box}
    {grid : ClearGrid polynomial ambient} (frame : AmbientFrame grid) :
    grid.vertical.length = grid.xIntervals.length + 1 :=
      Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices.span_length frame.xSpan grid.vertical_ordered

end Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame

namespace Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame

/-- The original framed grid has one more horizontal line than vertical coordinate intervals. -/
theorem horizontal_length
    {polynomial : ClearPath.GaussianPolynomial} {ambient : Geometry.Rational.Box}
    {grid : ClearGrid polynomial ambient} (frame : AmbientFrame grid) :
    grid.horizontal.length = grid.yIntervals.length + 1 :=
      Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices.span_length frame.ySpan grid.horizontal_ordered

end Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient}

namespace Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices

/-- Strictly ordered horizontal coordinates produce distinct Gaussian points on one retained vertical line. -/
private theorem column_nodup (vertical : ClearGrid.VerticalLine polynomial ambient)
    (horizontal : List (ClearGrid.HorizontalLine polynomial ambient))
    (ordered : horizontal.Pairwise (fun first last => first.coordinate < last.coordinate)) :
    (horizontal.map (fun line => Components.Basic.point vertical.coordinate line.coordinate)).Nodup :=
  Pairwise.pairwise_map.mpr (List.Pairwise.imp
    (fun apart same => ne_of_lt apart (congrArg Data.Gaussian.Basic.im same)) ordered)

end Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices

namespace Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices

/-- Strictly ordered original coordinate lines produce a duplicate-free Cartesian point list.

The original ordered horizontal and vertical lists separate each point pair.
Their Cartesian enumeration preserves the coordinate order and has no repeats. -/
private theorem coordinates_nodup (vertical : List (ClearGrid.VerticalLine polynomial ambient))
    (horizontal : List (ClearGrid.HorizontalLine polynomial ambient))
    (xOrdered : vertical.Pairwise (fun first last => first.coordinate < last.coordinate))
    (yOrdered : horizontal.Pairwise (fun first last => first.coordinate < last.coordinate)) :
    (vertical.flatMap (fun x => horizontal.map (fun y => Components.Basic.point x.coordinate y.coordinate))).Nodup := by
  induction vertical with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      rw [Flatten.flatMap_cons]
      refine Nodup.nodup_append (column_nodup head horizontal
        yOrdered)
        (ih (List.pairwise_cons.mp xOrdered).2) ?_
      intro first firstMember last lastMember equal
      obtain ⟨firstY, _, firstEq⟩ := Map.mem_map.mp firstMember
      obtain ⟨lastX, lastXMember, lastMember⟩ := Flatten.mem_flatMap.mp lastMember
      obtain ⟨lastY, _, lastEq⟩ := Map.mem_map.mp lastMember
      have same := congrArg Data.Gaussian.Basic.re (firstEq.trans (equal.trans lastEq.symm))
      exact ne_of_lt ((List.pairwise_cons.mp xOrdered).1 lastX lastXMember) same

end Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices

namespace RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

/-- The canonical vertex bank's retained coordinate list has no duplicates. -/
theorem build_nodup
    (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) :
    (VertexBank.build grid).coordinates.Nodup :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices.coordinates_nodup grid.vertical grid.horizontal
    grid.vertical_ordered grid.horizontal_ordered

end RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

namespace RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

/-- The canonical lifted vertex count is twice the product of the original coordinate-line counts. -/
theorem build_count
    (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) :
    (VertexBank.build grid).count =
      2 * (grid.vertical.length * grid.horizontal.length) := by
  unfold VertexBank.count
    VertexBank.build
  rw [Flatten.length_flatMap_map]

end RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

namespace Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices

/-- Reading a duplicate-free finite coordinate list is injective on its original finite indices. -/
private theorem vertexAt_injective (coordinates : List Data.Gaussian.Basic.Canonical) (unique : coordinates.Nodup) :
    Function.Injective (CoordinateTriangulation.vertexAt coordinates) := by
  intro first last same
  apply Fin.ext
  rcases Nat.lt_trichotomy first.val last.val with before | equal | after
  · exact (Pairwise.pairwise_getElem unique _ _ first.isLt last.isLt before same).elim
  · exact equal
  · exact (Pairwise.pairwise_getElem unique _ _ last.isLt first.isLt after same.symm).elim

end Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices

namespace RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

/-- With a unique coordinate bank, coordinate and sheet determine the literal retained index. This is deliberately not
asserted for arbitrary duplicate-containing caches. -/
theorem eq_of_coordinate_sheet
    (vertices : LiftedVertices.VertexBank grid) (unique : vertices.coordinates.Nodup)
    {first last : Fin vertices.count} (coordinates : vertices.coordinate first = vertices.coordinate last)
    (sheets : vertices.sheet first = vertices.sheet last) : first = last :=
  (SheetIndex.encode_decode first).symm.trans
    ((congrArg₂ SheetIndex.encode
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices.vertexAt_injective vertices.coordinates unique
        coordinates) sheets).trans
      (SheetIndex.encode_decode last))

end RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

namespace RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

/-- A duplicate-free retained vertex bank reads each original coordinate and sheet back to its exact index. -/
theorem index_coordinate
    (vertices : LiftedVertices.VertexBank grid) (unique : vertices.coordinates.Nodup)
    (index : Fin vertices.count) :
    vertices.index (vertices.coordinate index) (vertices.coordinate_onGrid index) (vertices.sheet index) = index :=
  vertices.eq_of_coordinate_sheet unique (vertices.coordinate_index _ _ _) (vertices.sheet_index _ _ _)

end RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

namespace RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

/-- Transfer the unique Cartesian enumeration into the actual cache. The two root sheets remain separate even if that
cache has repeated coordinates. -/
@[expose] def canonicalIndex
    (vertices : LiftedVertices.VertexBank grid) (index : Fin (VertexBank.build grid).count) : Fin vertices.count :=
  vertices.index ((VertexBank.build grid).coordinate index)
    ((VertexBank.build grid).coordinate_onGrid index)
    ((VertexBank.build grid).sheet index)

end RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

namespace RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

/-- Transferring the canonical Cartesian sheet indices into the retained bank is injective. -/
theorem canonicalIndex_injective
    (vertices : LiftedVertices.VertexBank grid) : Function.Injective vertices.canonicalIndex := by
  intro first last same
  apply (VertexBank.build grid).eq_of_coordinate_sheet
    (RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank.build_nodup grid)
  · exact (vertices.coordinate_index _ _ _).symm.trans
      ((congrArg vertices.coordinate same).trans (vertices.coordinate_index _ _ _))
  · exact (vertices.sheet_index _ _ _).symm.trans
      ((congrArg vertices.sheet same).trans (vertices.sheet_index _ _ _))

end RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

namespace Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices

/-- Equal original coordinates on the same sheet have equal retained bank indices. -/
private theorem index_congr_coordinates (vertices : LiftedVertices.VertexBank grid) {first last :
  Data.Gaussian.Basic.Canonical}
    (equal : first = last) (firstOn : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid first) (lastOn :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex grid last) (sheet :
      Fin 2) :
    vertices.index first firstOn sheet = vertices.index last lastOn sheet := by
  cases equal
  rfl

end Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices

namespace RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

/-- Every retained index fixed by coordinate-and-sheet readback occurs in the canonical enumeration. -/
theorem canonicalIndex_covers
    (vertices : LiftedVertices.VertexBank grid) (vertex : Fin vertices.count)
    (readback : vertices.index (vertices.coordinate vertex) (vertices.coordinate_onGrid vertex) (vertices.sheet vertex)
      = vertex) :
    ∃ index, vertices.canonicalIndex index = vertex := by
  let canonical := VertexBank.build grid
  let index := canonical.index (vertices.coordinate vertex) (vertices.coordinate_onGrid vertex) (vertices.sheet vertex)
  refine ⟨index, ?_⟩
  unfold VertexBank.canonicalIndex
  have coordinateEq : canonical.coordinate index = vertices.coordinate vertex := canonical.coordinate_index _ _ _
  have sheetEq : canonical.sheet index = vertices.sheet vertex := canonical.sheet_index _ _ _
  change vertices.index (canonical.coordinate index) _ (canonical.sheet index) = vertex
  rw [sheetEq]
  exact (Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices.index_congr_coordinates vertices coordinateEq _ _
    _).trans readback

end RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    VertexBank base.bank.grid}
  {edges : RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

namespace Curves.Hyperelliptic.Meshes.PuncturedGrid

namespace ActiveVertices.BranchCellBank.LiftedMesh

/-- An original retained vertex index occurs in at least one actual mesh triangle. -/
@[expose] def ActiveVertex
    (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces) (vertex : Fin vertices.count) : Prop :=
  ∃ index, OrientedTriangle.ContainsVertex
    (mesh.triangulation.faces index) vertex

end ActiveVertices.BranchCellBank.LiftedMesh

namespace ActiveVertices.BranchCellBank.LiftedMesh

/-- Every canonical sheet index is used by an actual retained regular face, including vertices on the exterior and
around removed branch cells. -/
theorem index_active
    (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces) (point : Data.Gaussian.Basic.Canonical)
    (onGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid point) (sheet : Fin 2) :
    ActiveVertex
      mesh (vertices.index point onGrid sheet) := by
  let regular := (VertexStar.build base point onGrid).regularIncident
  let lifted := regular.lift mesh sheet
  exact ⟨lifted.value.located.occurrence.triangle
      (Lifted.cornerUpper lifted),
    Lifted.corner_contains lifted onGrid⟩

end ActiveVertices.BranchCellBank.LiftedMesh

namespace ActiveVertices.BranchCellBank.LiftedMesh

/-- An actual triangle vertex reads back to its exact retained coordinate-and-sheet index. -/
theorem active_index_readback
    (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces) (vertex : Fin vertices.count)
    (active : ActiveVertex mesh
      vertex) :
    vertices.index (vertices.coordinate vertex) (vertices.coordinate_onGrid vertex) (vertices.sheet vertex) = vertex :=
      by
  obtain ⟨index, contains⟩ := active
  exact (FramedPuncturedGrid.triangleAtVertex
    mesh index vertex contains).vertex_eq

end ActiveVertices.BranchCellBank.LiftedMesh

namespace ActiveVertices.BranchCellBank.LiftedMesh

/-- A retained vertex is used by the actual mesh precisely when coordinate-and-sheet lookup fixes its index. -/
theorem active_iff_readback
    (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces) (vertex : Fin vertices.count) :
    ActiveVertex mesh vertex ↔
      vertices.index (vertices.coordinate vertex) (vertices.coordinate_onGrid vertex) (vertices.sheet vertex) = vertex
        :=
  ⟨active_index_readback mesh vertex,
    fun same => same ▸ index_active
      mesh _ _ _⟩

end ActiveVertices.BranchCellBank.LiftedMesh

set_option genInjectivity false in
/-- A certified enumeration of the vertices used by a retained lifted mesh.

The duplicate-free list contains exactly the original mesh triangle vertices.
Its count is the geometric coordinate-line product, independent of unused cache slots. -/
structure ActiveVertices
    (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces) where
  /-- The retained duplicate-free enumeration of actual triangle vertex indices. -/ indices : List (Fin vertices.count)
  /-- No original active vertex index is repeated in the enumeration. -/ unique : indices.Nodup
  /-- The enumeration contains exactly the vertex indices used by actual original mesh triangles. -/ active_iff : ∀
    vertex, vertex ∈ indices ↔
    Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices.BranchCellBank.LiftedMesh.ActiveVertex mesh vertex
  /-- The enumeration count is twice the product of the original coordinate-line counts. -/ length_eq : indices.length =
    2 * (base.bank.grid.vertical.length * base.bank.grid.horizontal.length)

constructive_injectivity ActiveVertices

namespace ActiveVertices.BranchCellBank.LiftedMesh

/-- Enumerate lifted vertices using the retained Cartesian sheet indices.

The original Cartesian sheet indices are transferred into the retained
vertex bank. Incidence and readback witnesses certify that exact selected list. -/
@[expose] def activeVertices
    (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces) :
      ActiveVertices mesh where
  indices := List.ofFn vertices.canonicalIndex
  unique := BoundaryCounts.nodup_ofFn_injective _ vertices.canonicalIndex_injective
  active_iff vertex := ⟨fun member => by
      obtain ⟨index, same⟩ := OfFn.Basic.mem_ofFn.mp member
      exact same ▸ index_active mesh
        _ _ _,
    fun active => OfFn.Basic.mem_ofFn.mpr (vertices.canonicalIndex_covers vertex
      (active_index_readback mesh
        vertex active))⟩
  length_eq := OfFn.Basic.length_ofFn.trans (RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank.build_count _)

end ActiveVertices.BranchCellBank.LiftedMesh

namespace ActiveVertices

/-- The actual active vertex count is twice the product of the original interval counts plus one in each direction. -/
theorem length_eq_intervals
    {mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces}
    (enumeration : ActiveVertices
      mesh) :
    enumeration.indices.length = 2 * ((base.bank.grid.xIntervals.length + 1) * (base.bank.grid.yIntervals.length + 1))
      := by
  rw [enumeration.length_eq, base.bank.frame.vertical_length, base.bank.frame.horizontal_length]

end ActiveVertices

end Curves.Hyperelliptic.Meshes.PuncturedGrid
end Purelib
