module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Geometry.Rational.Box.Content
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Polynomial.Clearance.Box.Region

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Mesh.CoordinateTriangulation
public import Purelib.Riemann.Meshes.PuncturedGridBoundary
public import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Data.List.Attach
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Refined, incidence-certified meshes of the punctured branch grid

Only classified regular faces are triangulated.  Every retained leaf carries
its actual regular parent and inherits that parent's computed clearance.
Shared coordinate indices and exact edge cancellation identify the mesh
boundary with the subdivided exterior and clockwise branch-hole boundaries.

This is the base excision mesh.  Removed faces may meet the outer perimeter;
the incidence identity does not assert separate interior boundary components.
`FramedPuncturedGrid` supplies the enclosing frame and strictly interior holes.
Two-sheet gluing and a cut-surface primitive assignment remain separate;
no global primitive is asserted here.
-/

namespace Purelib.Riemann.Meshes.PuncturedGridMesh

open Purelib
open Purelib.Geometry.Rational
open Purelib.Geometry.Rectangle.Partition
open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace BranchHole PuncturedFaces)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (EdgeValues sumValues sumValues_congr)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
  (sumBoxBoundaries rectangleBoundary horizontalBoundary verticalBoundary)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation (boxTriangles)
open _root_.Purelib.Topology.Mesh (CoordinateTriangulation)
open Purelib.Integration.Energy.AffineTriangle (coordinateTriangleArea)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
  (cells cells_refine cells_proper sumCells)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeListArea)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}

set_option genInjectivity false in
/-- A proper refined box retaining its original regular parent face.

The exact box refinement keeps the original polynomial clearance owner available at every retained leaf. -/
structure RegularLeaf (bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher) where
  /-- The retained original regular face owning this leaf. -/ parent : RegularFace bank
  /-- The retained proper refining leaf box. -/ box : Box
  /-- The leaf box refines its exact original parent cell. -/ refines : box.Refines parent.cell.box
  /-- The retained leaf box has strictly ordered coordinate bounds. -/ proper : box.Proper

constructive_injectivity RegularLeaf

namespace RegularLeaf

open Purelib.Polynomial.Clearance.Box

/-- Restrict the original regular face clearance to its retained refining leaf box. -/
@[expose] def clearance (leaf : RegularLeaf bank) : Region.RegionClearance curve.polynomial leaf.box :=
  leaf.parent.clearance.restrict leaf.refines

/-- The leaf clearance retains exactly its original parent clearance bound. -/
theorem clearance_bound (leaf : RegularLeaf bank) : leaf.clearance.bound = leaf.parent.clearance.bound := rfl

/-- Subdivide the original regular face into proper dyadic leaves retaining that exact parent.

Each attached cell membership supplies the original refinement and properness certificates for the stored leaf box. -/
@[expose] def refine (face : RegularFace bank) (depth : Nat) : List (RegularLeaf bank) :=
  (PreparedBoxPartitions.cells depth face.cell.box).attach.map fun child =>
    ⟨face, child.val, PreparedBoxPartitions.cells_refine depth face.cell.box child.property,
      PreparedBoxPartitions.cells_proper depth face.cell.box_proper child.property⟩

/-- The retained refined leaf boxes equal the exact original dyadic cell list.

The original attached cells retain their membership and refinement certificates. The owned structural map-composition
law reads their unchanged box projections in the same order. -/
theorem refine_boxes (face : RegularFace bank) (depth : Nat) :
    ((refine face depth).map RegularLeaf.box) = PreparedBoxPartitions.cells depth face.cell.box := by
  rw [refine, Purelib.Data.List.Map.map_map]
  exact Data.List.attach_map_subtype_val _

end RegularLeaf

/-- Concatenate the retained dyadic leaves of each original regular face in order.

Each face contributes its exact refinement block at the supplied depth. Structural recursion retains the ordered face
spine and appends the unchanged remaining-face refinement. -/
@[expose] def refinedLeaves (depth : Nat) : List (RegularFace bank) → List (RegularLeaf bank)
  | [] => []
  | face :: faces => RegularLeaf.refine face depth ++ refinedLeaves depth faces

/-- The retained leaf boxes equal the concatenation of the original regular-face dyadic cell lists.

The original recursive leaf concatenation preserves each face and its ordered dyadic cells. Structural map-append
readbacks transport the retained remaining-face equality. -/
theorem refinedLeaves_boxes (depth : Nat) (faces : List (RegularFace bank)) :
    (refinedLeaves depth faces).map RegularLeaf.box = faces.flatMap (fun face => PreparedBoxPartitions.cells depth
      face.cell.box) := by
  induction faces with
  | nil => rfl
  | cons face faces ih => rw [refinedLeaves, Purelib.Data.List.Map.map_append, RegularLeaf.refine_boxes, ih]; rfl

/-- Dyadic refinement produces four to the retained depth cells per original regular face.

Each original regular face contributes exactly four to the retained depth cells. Structural concatenation and direct
natural arithmetic preserve every original occurrence. -/
private theorem refined_length (depth : Nat) (faces : List (RegularFace bank)) :
    (faces.flatMap (fun face => PreparedBoxPartitions.cells depth face.cell.box)).length = 4 ^ depth * faces.length :=
      by
  induction faces with
  | nil => exact (Nat.mul_zero _).symm
  | cons face faces ih =>
      simp only [Purelib.Data.List.Flatten.flatMap_cons, Purelib.Data.List.Append.length_append,
        PreparedBoxPartitions.cells_length, ih, List.length_cons]
      rw [Nat.mul_add, Nat.mul_one]
      omega

/-- The refined original cell list has exactly the original regular faces' total content. -/
private theorem refined_content (depth : Nat) (faces : List (RegularFace bank)) :
    PreparedBoxPartitions.sumCells Box.Content.boxContent (faces.flatMap (fun face => PreparedBoxPartitions.cells depth
      face.cell.box)) =
      PreparedBoxPartitions.sumCells Box.Content.boxContent (faces.map (fun face => face.cell.box)) := by
  induction faces with
  | nil => rfl
  | cons face faces ih =>
      rw [Purelib.Data.List.Flatten.flatMap_cons,
        PreparedBoxPartitions.sumCells_append,
        PreparedBoxPartitions.cells_content, ih]
      rfl

/-- The refined cell boundary sum equals the sum of the original faces' depth-subdivided boundaries. -/
private theorem refined_boundary (primitive : Basic.Canonical → PrimitivePoint) (depth : Nat) (faces : List (RegularFace
  bank)) :
    PreparedBoxBoundary.sumBoxBoundaries primitive (faces.flatMap (fun face => PreparedBoxPartitions.cells depth
      face.cell.box)) =
      Geometry.Grid.CellBoundary.sumValues (fun face => PreparedBoxBoundary.rectangleBoundary primitive depth
        face.cell.box) faces := by
  induction faces with
  | nil => rfl
  | cons face faces ih =>
      rw [Purelib.Data.List.Flatten.flatMap_cons, PreparedBoxBoundary.sumBoxBoundaries_append,
        PreparedBoxBoundary.sumBoxBoundaries_cells, ih]
      rfl

set_option genInjectivity false in
/-- A coordinate triangulation of retained regular leaves with exact cell-list and area equations.

The original punctured-face owner and refinement depth remain indices. The mesh uses the exact triangles of its stored
leaf boxes. -/
structure PuncturedMesh (faces : PuncturedFaces bank) (depth : Nat) where
  /-- The retained ordered original regular leaves. -/ leaves : List (RegularLeaf bank)
  /-- The leaf boxes equal the exact original depth-refined regular-face cells. -/ boxes_eq : leaves.map RegularLeaf.box
    = faces.regulars.flatMap (fun face => PreparedBoxPartitions.cells depth face.cell.box)
  /-- The coordinate triangulation of the exact retained leaf-box triangles. -/ mesh :
    Topology.Mesh.CoordinateTriangulation (PreparedBoxTriangulation.boxTriangles (leaves.map
    RegularLeaf.box))
  /-- The cached original total coordinate area. -/ area : Fraction.Rational
  /-- The cache equals the exact content sum of the stored leaf boxes. -/ area_eq : area =
    PreparedBoxPartitions.sumCells Box.Content.boxContent (leaves.map RegularLeaf.box)

constructive_injectivity PuncturedMesh

namespace PuncturedMesh

open Purelib.Data.List
open Purelib.Integration.Energy
open Purelib.Algebra

variable {faces : PuncturedFaces bank} {depth : Nat}

/-- Construct the punctured coordinate mesh from the original regular faces at the retained dyadic depth.

The original refined leaves determine the stored triangles; the area cache uses their parents' exact total content with
its refinement equality retained. -/
@[expose] def build (faces : PuncturedFaces bank) (depth : Nat) : PuncturedMesh faces depth :=
  let leaves := refinedLeaves depth faces.regulars
  { leaves := leaves
    boxes_eq := refinedLeaves_boxes depth faces.regulars
    mesh := Topology.Mesh.CoordinateTriangulation.build (PreparedBoxTriangulation.boxTriangles
      (leaves.map RegularLeaf.box))
    area := PreparedBoxPartitions.sumCells Box.Content.boxContent (faces.regulars.map (fun face => face.cell.box))
    area_eq := by rw [refinedLeaves_boxes, refined_content] }

/-- The retained punctured mesh has four to the depth leaves per original regular face.

The stored box-list readback retains the exact original refined regular-face cells. Taking its length with the owned
structural map law transports the finite count. -/
theorem leafCount (surface : PuncturedMesh faces depth) : surface.leaves.length = 4 ^ depth * faces.regulars.length :=
  by
  have lengths := congrArg List.length surface.boxes_eq
  rw [Purelib.Data.List.Map.length_map, refined_length] at lengths
  exact lengths

/-- The retained punctured mesh has two triangles for every original refined leaf.

The original box triangulation contributes two triangles per retained leaf. Its exact length readback combines with the
retained leaf-count certificate. -/
theorem faceCount (surface : PuncturedMesh faces depth) :
    (PreparedBoxTriangulation.boxTriangles (surface.leaves.map RegularLeaf.box)).length = 2 * (4 ^ depth *
      faces.regulars.length) := by
  rw [PreparedBoxTriangulation.boxTriangles_length, Purelib.Data.List.Map.length_map, surface.leafCount]

/-- The retained mesh area equals the original regular faces' total content. -/
theorem area_eq_regular (surface : PuncturedMesh faces depth) :
    surface.area = PreparedBoxPartitions.sumCells Box.Content.boxContent (faces.regulars.map (fun face =>
      face.cell.box)) := by
  rw [surface.area_eq, surface.boxes_eq, refined_content]

/-- Every original retained mesh triangle has strictly positive coordinate area. -/
theorem faceArea_positive (surface : PuncturedMesh faces depth)
    (index : Fin (PreparedBoxTriangulation.boxTriangles (surface.leaves.map RegularLeaf.box)).length) :
    0 < AffineTriangle.coordinateTriangleArea
      (surface.mesh.coordinate (surface.mesh.triangulation.faces index).first)
      (surface.mesh.coordinate (surface.mesh.triangulation.faces index).second)
      (surface.mesh.coordinate (surface.mesh.triangulation.faces index).third) := by
  have coordinates := surface.mesh.face_coordinates index
  rw [coordinates.1, coordinates.2.1, coordinates.2.2]
  apply PreparedBoxTriangulation.boxTriangles_positive _ ?_ (List.getElem_mem _)
  intro box member
  obtain ⟨leaf, _, equal⟩ := Map.mem_map.mp member
  rw [← equal]
  exact leaf.proper

/-- The exact indexed sum of retained triangle areas equals the original mesh area cache. -/
theorem areaSum_eq (surface : PuncturedMesh faces depth) :
    FiniteSum.Fin.sumFin (fun index => AffineTriangle.coordinateTriangleArea
      (surface.mesh.coordinate (surface.mesh.triangulation.faces index).first)
      (surface.mesh.coordinate (surface.mesh.triangulation.faces index).second)
      (surface.mesh.coordinate (surface.mesh.triangulation.faces index).third)) = surface.area := by
  calc
    _ = FiniteSum.Fin.sumFin (fun index : Fin (PreparedBoxTriangulation.boxTriangles (surface.leaves.map
      RegularLeaf.box)).length =>
        PreparedBoxTriangulation.coordinateArea ((PreparedBoxTriangulation.boxTriangles (surface.leaves.map
          RegularLeaf.box))[index.val]'index.isLt)) := by
      apply FiniteSum.Fin.sumFin_congr
      intro index
      have coordinates := surface.mesh.face_coordinates index
      rw [coordinates.1, coordinates.2.1, coordinates.2.2]
      rfl
    _ = PreparedBoxTriangulation.sumTriangleAreas (PreparedBoxTriangulation.boxTriangles (surface.leaves.map
      RegularLeaf.box)) :=
      (PreparedBoxTriangulation.sumTriangleAreas_eq_sumFin _).symm
    _ = _ := (PreparedBoxTriangulation.boxTriangles_areaSum _).trans surface.area_eq.symm

/-- The original horizontal and vertical subdivided primitive boundary values at the retained depth. -/
@[expose] def primitiveEdges (primitive : Basic.Canonical → PrimitivePoint) (depth : Nat) : EdgeValues :=
  ⟨fun left right y => PreparedBoxBoundary.horizontalBoundary primitive depth left right y,
    fun x bottom top => PreparedBoxBoundary.verticalBoundary primitive depth bottom top x⟩

/-- The retained triangulation boundary area equals the original regular-cell boundary sum.

Exact face-coordinate readbacks identify the original triangle wedges, and finite subdivision identities recover each
original cell boundary. -/
theorem boundary_eq_regular (surface : PuncturedMesh faces depth) (primitive : Basic.Canonical → PrimitivePoint) :
    edgeListArea (fun vertex => primitive (surface.mesh.coordinate vertex)) surface.mesh.triangulation.boundary =
      Geometry.Grid.CellBoundary.sumValues (fun face => (primitiveEdges primitive depth).cellBoundary face.cell)
        faces.regulars := by
  rw [← surface.mesh.wedgeSum_eq_boundaryArea]
  calc
    _ = FiniteSum.Fin.sumFin (fun index : Fin (PreparedBoxTriangulation.boxTriangles (surface.leaves.map
      RegularLeaf.box)).length =>
        PreparedBoxBoundary.coordinateWedge primitive ((PreparedBoxTriangulation.boxTriangles (surface.leaves.map
          RegularLeaf.box))[index.val]'index.isLt)) := by
      apply FiniteSum.Fin.sumFin_congr
      intro index
      have coordinates := surface.mesh.face_coordinates index
      change triangleWedgeArea
        (primitive (surface.mesh.coordinate (surface.mesh.triangulation.faces index).first))
        (primitive (surface.mesh.coordinate (surface.mesh.triangulation.faces index).second))
        (primitive (surface.mesh.coordinate (surface.mesh.triangulation.faces index).third)) = _
      rewrite [coordinates.1, coordinates.2.1, coordinates.2.2]
      exact Eq.refl _
    _ = PreparedBoxBoundary.sumCoordinateWedges primitive (PreparedBoxTriangulation.boxTriangles (surface.leaves.map
      RegularLeaf.box)) :=
      (PreparedBoxBoundary.sumCoordinateWedges_eq_sumFin _ _).symm
    _ = PreparedBoxBoundary.sumBoxBoundaries primitive (surface.leaves.map RegularLeaf.box) :=
      PreparedBoxBoundary.sumCoordinateWedges_boxTriangles _ _
    _ = _ := by rw [surface.boxes_eq, refined_boundary]; rfl

/-- The retained punctured mesh boundary equals the original exterior plus inward-oriented hole boundary values.

The exact original regular-face boundary identity preserves the separate oriented exterior and hole contributions. -/
theorem boundary_eq_exterior_sub_holes (surface : PuncturedMesh faces depth) (primitive : Basic.Canonical →
  PrimitivePoint) :
    edgeListArea (fun vertex => primitive (surface.mesh.coordinate vertex)) surface.mesh.triangulation.boundary =
      (primitiveEdges primitive depth).perimeter bank.grid +
        Geometry.Grid.CellBoundary.sumValues (fun hole => (primitiveEdges primitive depth).walk hole.inwardBoundary)
          faces.holes := by
  rw [surface.boundary_eq_regular]
  have regular := Geometry.Grid.CellBoundary.sumValues_congr (fun face : RegularFace bank => (primitiveEdges primitive
    depth).walk face.boundary)
    (fun face => (primitiveEdges primitive depth).cellBoundary face.cell) faces.regulars
    (fun face _ => Geometry.Grid.CellBoundary.Cell.boundaryWalk_value face.cell face.member _)
  rw [← regular]
  exact faces.boundary_eq_exterior_sub_holes _

end PuncturedMesh

end Purelib.Riemann.Meshes.PuncturedGridMesh
