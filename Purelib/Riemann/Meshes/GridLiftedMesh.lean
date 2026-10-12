module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Content
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.EdgeCancellation
import Purelib.Topology.Mesh.IndexedQuadrilaterals
public import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Incidence-certified meshes of the actual two-sheeted punctured grid

Each regular face contributes both root-lifted quadrilaterals, hence four
positively oriented triangles.  All faces use one shared vertex bank and one
shared transport bank.  Their exact finite Stokes theorem therefore applies
to sheet-dependent primitive values, not values on a collapsed base grid.
The remaining boundary is computed here; its cut-surface A/B identification
and the construction of compatible analytic primitives are separate steps.
-/

namespace Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace PuncturedFaces)
open Purelib.Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral (firstTriangle secondTriangle)
open Purelib.Topology.Mesh.EdgeCancellation (triangulateFaces)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

open Purelib.Data.List in
/-- Enumerating the original triangle list by its exact bounded indices returns that same ordered list. -/
private theorem triangleList_ofFn {count : Nat} : (triangles : List (OrientedTriangle count)) →
    List.ofFn (fun index : Fin triangles.length => triangles[index.val]) = triangles
  | [] => rfl
  | triangle :: triangles => by
      rw [OfFn.Basic.ofFn_succ]
      exact congrArg (List.cons triangle) (triangleList_ofFn triangles)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

open Purelib.RootIsolation in
set_option genInjectivity false in
/-- Both retained sheet lifts for each original regular face in list order.

Each step keeps the original zero-sheet and one-sheet quadrilaterals and the exact tail of regular faces. -/
inductive LiftedFaces (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid) (edges :
  SquareRoot.Grid.RootEdgeBank frames) :
    List (RegularFace bank) → Type
  /-- The empty original regular-face list has no retained sheet lifts. -/ | nil : LiftedFaces vertices edges []
  /-- Retain both exact sheet lifts of the original head face and the lifted tail. -/ | cons {face : RegularFace bank}
    {faces : List (RegularFace bank)}
      (zero : LiftedFace vertices edges face 0) (one : LiftedFace vertices edges face 1)
      (tail : LiftedFaces vertices edges faces) : LiftedFaces vertices edges (face :: faces)

constructive_injectivity LiftedFaces

namespace LiftedFaces

variable {vertices : VertexBank bank.grid} {edges :
  RootEdgeBank frames}

open Purelib.RootIsolation in
/-- Construct both original sheet lifts of each regular face in the retained list. -/
@[expose] def build (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid) (edges :
  SquareRoot.Grid.RootEdgeBank frames) :
    (faces : List (RegularFace bank)) → LiftedFaces vertices edges faces
  | [] => .nil
  | face :: faces => .cons (LiftedFace.build vertices edges face 0) (LiftedFace.build vertices edges face 1) (build
    vertices edges faces)

/-- List the two triangles of each original zero-sheet and one-sheet quadrilateral in face order. -/
@[expose] def triangles : {faces : List (RegularFace bank)} → LiftedFaces vertices edges faces → List (OrientedTriangle
  vertices.count)
  | _, .nil => []
  | _, .cons zero one tail => zero.quad.firstTriangle :: zero.quad.secondTriangle ::
      one.quad.firstTriangle :: one.quad.secondTriangle :: tail.triangles

/-- Concatenate both retained quadrilateral boundaries for each original regular face. -/
@[expose] def boundaries : {faces : List (RegularFace bank)} → LiftedFaces vertices edges faces → List (OrientedEdge
  vertices.count)
  | _, .nil => []
  | _, .cons zero one tail => zero.quad.boundary ++ one.quad.boundary ++ tail.boundaries

open Purelib.RootIsolation in
/-- Concatenate the exact root-edge-bank lifts of both sheet boundary walks in original face order. -/
@[expose] def actualBoundaries (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid) (edges :
  SquareRoot.Grid.RootEdgeBank frames) :
    List (RegularFace bank) → List (OrientedEdge vertices.count)
  | [] => []
  | face :: faces => edges.indexedEdges vertices face.boundary 0 ++ edges.indexedEdges vertices face.boundary 1 ++
      actualBoundaries vertices edges faces

/-- The retained quadrilateral boundaries equal the exact original lifted boundary walks. -/
theorem boundaries_eq_actual : {faces : List (RegularFace bank)} → (lifts : LiftedFaces vertices edges faces) →
    lifts.boundaries = actualBoundaries vertices edges faces
  | _, .nil => rfl
  | _, .cons zero one tail => by rw [boundaries, zero.boundary_eq, one.boundary_eq, tail.boundaries_eq_actual]; rfl

/-- Both sheet lifts contribute exactly four retained triangles per original regular face. -/
theorem triangles_length : {faces : List (RegularFace bank)} → (lifts : LiftedFaces vertices edges faces) →
    lifts.triangles.length = 4 * faces.length
  | _, .nil => rfl
  | _, .cons _ _ tail => by simp only [triangles, List.length_cons, tail.triangles_length]; omega

open Purelib.Data.Rat in
open Purelib.Integration.Energy in
open Purelib.RootIsolation in
/-- The coordinate area of a retained indexed triangle using the original vertex bank. -/
@[expose] def triangleArea (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid) (triangle : OrientedTriangle
  vertices.count) : Fraction.Rational :=
  AffineTriangle.coordinateTriangleArea (vertices.coordinate triangle.first)
    (vertices.coordinate triangle.second) (vertices.coordinate triangle.third)

open Purelib.Data.Rat in
open Purelib.RootIsolation in
/-- Sum coordinate areas in the original retained triangle-list order. -/
@[expose] def areaSum (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid) : List (OrientedTriangle
  vertices.count) → Fraction.Rational
  | [] => 0
  | triangle :: triangles => triangleArea vertices triangle + areaSum vertices triangles

open Purelib.Algebra in
open Purelib.RootIsolation in
/-- The original triangle-list area sum equals its exact bounded-index finite sum. -/
theorem areaSum_eq_sumFin (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid) (triangles : List
  (OrientedTriangle vertices.count)) :
    areaSum vertices triangles = FiniteSum.Fin.sumFin (fun index : Fin triangles.length => triangleArea vertices
      triangles[index.val]) := by
  induction triangles with
  | nil => rfl
  | cons triangle triangles ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      exact congrArg (fun rest => triangleArea vertices triangle + rest) ih

open Purelib in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Geometry.Rectangle.Partition in
/-- The total retained lifted triangle area equals twice the content of the original regular cells.

Each original cell contributes two half-area triangles on each of its two sheet lifts, with the retained cell order
unchanged. -/
theorem area_eq : {faces : List (RegularFace bank)} → (lifts : LiftedFaces vertices edges faces) →
    areaSum vertices lifts.triangles =
      2 * PreparedBoxPartitions.sumCells Box.Content.boxContent (faces.map fun face => face.cell.box)
  | _, .nil => by change (0 : Fraction.Rational) = 2 * 0; ring1
  | _, .cons zero one tail => by
      simp only [triangles, areaSum, triangleArea,
        Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral.firstTriangle,
        Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral.secondTriangle]
      rw [zero.firstTriangle_area, zero.secondTriangle_area, one.firstTriangle_area, one.secondTriangle_area,
        tail.area_eq]
      have halves (area : Fraction.Rational) : area / 2 + area / 2 = area := by
        calc
          _ = area / 2 * 2 := by ring1
          _ = area := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
      simp only [List.map_cons, PreparedBoxPartitions.sumCells]
      calc
        _ = (Box.Content.boxContent _ / 2 + Box.Content.boxContent _ / 2) +
            (Box.Content.boxContent _ / 2 + Box.Content.boxContent _ / 2) +
            2 * PreparedBoxPartitions.sumCells Box.Content.boxContent _ := by ring1
        _ = _ := by rw [halves]; ring1

open Purelib.Data.List in
/-- Every triangle in the original retained lifted face list has strictly positive coordinate area.

Structural membership selects the original head triangle or an unchanged retained tail occurrence. Each selected sheet
lift supplies the coordinate-area certificate for that exact triangle. -/
theorem triangle_positive : {faces : List (RegularFace bank)} → (lifts : LiftedFaces vertices edges faces) →
    ∀ triangle ∈ lifts.triangles, 0 < triangleArea vertices triangle
  | _, .nil, _, member => (List.not_mem_nil member).elim
  | _, .cons zero one tail, triangle, member => by
      rcases Membership.mem_cons.mp member with rfl | member
      · exact zero.firstTriangle_positive
      rcases Membership.mem_cons.mp member with rfl | member
      · exact zero.secondTriangle_positive
      rcases Membership.mem_cons.mp member with rfl | member
      · exact one.firstTriangle_positive
      rcases Membership.mem_cons.mp member with rfl | member
      · exact one.secondTriangle_positive
      exact tail.triangle_positive triangle member

open Purelib in
open Purelib.Data.List in
/-- The original retained triangle boundary occurrences have the same total area as the lifted face boundary walks.

The two retained triangles on each sheet cancel their shared diagonal algebraically. The same ordered outer edges and
the unchanged lifted tail supply the original boundary sum. -/
theorem triangleEdges_area (primitive : Fin vertices.count → PrimitivePoint) :
    {faces : List (RegularFace bank)} → (lifts : LiftedFaces vertices edges faces) →
      edgeListArea primitive (lifts.triangles.flatMap OrientedTriangle.boundary) =
        edgeListArea primitive (actualBoundaries vertices edges faces)
  | _, .nil => rfl
  | _, .cons zero one tail => by
      have zeroArea := zero.wedge_eq_boundary primitive
      have oneArea := one.wedge_eq_boundary primitive
      rw [← triangleBoundaryArea_eq_wedgeArea, ← triangleBoundaryArea_eq_wedgeArea] at zeroArea oneArea
      simp only [triangles, Flatten.flatMap_cons, OrientedTriangle.boundary,
        Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral.firstTriangle,
        Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral.secondTriangle, List.cons_append, List.nil_append,
          edgeListArea] at zeroArea oneArea ⊢
      change _ = edgeListArea primitive (edges.indexedEdges vertices _ 0 ++ edges.indexedEdges vertices _ 1 ++ _)
      rw [edgeListArea_append, edgeListArea_append]
      have rest := tail.triangleEdges_area primitive
      simp only [triangleBoundaryArea] at zeroArea oneArea
      rw [rest]
      rw [← zeroArea, ← oneArea]
      ring1

end LiftedFaces

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.RootIsolation in
set_option genInjectivity false in
/-- A triangulation retaining both original face lifts, their exact triangle list and doubled cell-area cache.

The triangulation is indexed by the stored list length, and its face equation preserves the original triangle at every
bounded index. -/
structure LiftedMesh (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid) (edges :
  SquareRoot.Grid.RootEdgeBank frames) (faces : PuncturedFaces bank) where
  /-- Both retained original sheet lifts of the exact regular-face list. -/ lifts : LiftedFaces vertices edges
    faces.regulars
  /-- The cached original ordered lifted triangle list. -/ triangles : List (OrientedTriangle vertices.count)
  /-- The cache equals the exact triangle list of the retained lifts. -/ triangles_eq : triangles = lifts.triangles
  /-- The triangulation indexed by the original cached triangle-list length. -/ triangulation : Triangulation
    vertices.count triangles.length
  /-- Each triangulation face equals the original cached triangle at that exact index. -/ faces_eq : ∀ index,
    triangulation.faces index = triangles[index.val]
  /-- The retained total coordinate-area cache. -/ area : Fraction.Rational
  /-- The cached area equals twice the content sum of the original regular cells. -/ area_eq : area = 2 *
    PreparedBoxPartitions.sumCells Box.Content.boxContent (faces.regulars.map fun face => face.cell.box)

constructive_injectivity LiftedMesh

namespace LiftedMesh

variable {vertices : VertexBank bank.grid} {edges :
  RootEdgeBank frames} {faces : PuncturedFaces bank}

open Purelib in
open Purelib.Data in
open Purelib.Geometry.Rational in
open Purelib.Geometry.Rectangle.Partition in
/-- Build the retained triangulation directly from the original lifted faces and their exact triangle list.

A vector of the stored triangles drives triangulation, while the area cache retains the exact doubled content of the
original regular cells. -/
@[expose] def ofLifts (lifts : LiftedFaces vertices edges faces.regulars) : LiftedMesh vertices edges faces :=
  let triangles := lifts.triangles
  let indexed := Vector.Basic.vectorOfFn fun index : Fin triangles.length => triangles[index.val]
  { lifts := lifts
    triangles := triangles
    triangles_eq := rfl
    triangulation := Topology.Mesh.EdgeCancellation.triangulateFaces indexed
    faces_eq := fun index => Vector.Basic.vectorOfFn_apply _ index
    area := 2 * PreparedBoxPartitions.sumCells Box.Content.boxContent (faces.regulars.map fun face => face.cell.box)
    area_eq := rfl }

open Purelib.RootIsolation in
/-- Construct the original lifted mesh from both sheet lifts of every retained regular face.

The original vertex bank, root-edge bank and punctured-face owner are preserved through the exact lifted-face
construction. -/
@[expose] def build (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid) (edges :
  SquareRoot.Grid.RootEdgeBank frames) (faces : PuncturedFaces bank) :
    LiftedMesh vertices edges faces :=
  ofLifts (LiftedFaces.build vertices edges faces.regulars)

/-- The retained lifted mesh has exactly four triangles per original regular face. -/
theorem faceCount (mesh : LiftedMesh vertices edges faces) : mesh.triangles.length = 4 * faces.regulars.length := by
  rw [mesh.triangles_eq]
  exact mesh.lifts.triangles_length

/-- Every indexed face of the retained triangulation has strictly positive coordinate area. -/
theorem face_positive (mesh : LiftedMesh vertices edges faces) (index : Fin mesh.triangles.length) :
    0 < LiftedFaces.triangleArea vertices (mesh.triangulation.faces index) := by
  rw [mesh.faces_eq]
  apply mesh.lifts.triangle_positive
  rw [← mesh.triangles_eq]
  exact List.getElem_mem _

open Purelib.Algebra in
/-- The original indexed triangulation area sum equals the retained doubled-cell-area cache. -/
theorem areaSum_eq (mesh : LiftedMesh vertices edges faces) :
    FiniteSum.Fin.sumFin (fun index => LiftedFaces.triangleArea vertices (mesh.triangulation.faces index)) = mesh.area
      := by
  calc
    _ = FiniteSum.Fin.sumFin (fun index : Fin mesh.triangles.length => LiftedFaces.triangleArea vertices
      mesh.triangles[index.val]) :=
      FiniteSum.Fin.sumFin_congr (fun index => congrArg (LiftedFaces.triangleArea vertices) (mesh.faces_eq index))
    _ = LiftedFaces.areaSum vertices mesh.triangles := (LiftedFaces.areaSum_eq_sumFin _ _).symm
    _ = _ := by rw [mesh.triangles_eq, mesh.lifts.area_eq, mesh.area_eq]

open Purelib.Data.List in
/-- The retained triangulation's triangle edge occurrences equal the original lifted triangle-list boundaries. -/
theorem triangleEdges_eq (mesh : LiftedMesh vertices edges faces) :
    triangleEdgeOccurrences mesh.triangulation.faces = mesh.lifts.triangles.flatMap OrientedTriangle.boundary := by
  have listed : List.ofFn mesh.triangulation.faces = mesh.triangles :=
    (OfFn.Basic.ofFn_congr mesh.faces_eq).trans (triangleList_ofFn mesh.triangles)
  exact congrArg (fun triangles => triangles.flatMap OrientedTriangle.boundary) (listed.trans mesh.triangles_eq)

/-- The retained triangulation's wedge sum equals the area of its exact remaining boundary. -/
theorem wedge_eq_boundary (mesh : LiftedMesh vertices edges faces) (primitive : Fin vertices.count → PrimitivePoint) :
    triangleWedgeSum primitive mesh.triangulation.faces = edgeListArea primitive mesh.triangulation.boundary :=
  mesh.triangulation.wedgeSum_eq_boundaryArea primitive

/-- The retained mesh boundary area equals the original lifted regular-face boundary-walk area. -/
theorem boundary_eq_faceWalks (mesh : LiftedMesh vertices edges faces) (primitive : Fin vertices.count → PrimitivePoint)
  :
    edgeListArea primitive mesh.triangulation.boundary =
      edgeListArea primitive (LiftedFaces.actualBoundaries vertices edges faces.regulars) := by
  rw [← mesh.wedge_eq_boundary, triangleWedgeSum_eq_edgeListArea, mesh.triangleEdges_eq]
  exact mesh.lifts.triangleEdges_area primitive

end LiftedMesh

end Purelib.Riemann.Meshes.GridLiftedMesh
