module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedBoundary
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
public import Purelib.Riemann.Meshes.GridLiftedFaceSelection
public import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.RootIsolation.SquareRoot.Grid.Boundary.Values
import Init.Data.List.Lemmas
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Tactic.Ring

public section

/-!
# The actual two-sheeted annulus and its closed boundary tours

Select the existing lifted faces, retaining their original root transports
and global vertex indices. The outer Newton-band tour closes after two laps;
the inward hole tour is the actual cached branch-hole boundary. Their areas
account exactly for the selected triangle area for sheet-dependent primitive
values. This does not yet estimate the analytic primitive or period errors.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary

open Purelib.Data.List

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.Riemann
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.GridLiftedMesh
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank
open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
open Purelib.Topology.Chain
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace BranchHole)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid (band_x_lines band_y_lines)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces (triangleArea)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_congr)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
    {index : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}

/-- The original Newton-band lower-left anchor belongs to the retained grid. -/
theorem anchor_onGrid (_annulus : Faces.AnnularFaces grid index) :
    Polynomial.Geometry.Grid.FromStates.ContainsVertex grid.shrunk.prepared.grid (grid.bands.box index).anchor :=
  ⟨(NewtonGrid.band_x_lines grid index).1,
    (NewtonGrid.band_y_lines grid index).1⟩

/-- Traverse the original Newton-band boundary twice in the same orientation. -/
@[expose] def doubleBoundary (annulus : Faces.AnnularFaces grid index) :
    Walks.Walk grid.shrunk.prepared.grid
      (point (grid.bands.box index).xLower (grid.bands.box index).yLower)
      (point (grid.bands.box index).xLower (grid.bands.box index).yLower) :=
  annulus.boundary.append annulus.boundary

/-- One original Newton-band boundary tour exchanges the two retained root sheets. -/
theorem boundary_swap (annulus : Faces.AnnularFaces grid index) {frames : RootIsolation.SquareRoot.Grid.RootFrames
  grid.shrunk.prepared.grid}
    (edges : RootEdgeBank frames) (sheet : Fin 2) :
    RootEdgeBank.target edges annulus.boundary sheet = BranchCutLifts.otherSheet sheet :=
    RootEdgeBank.target_odd edges annulus.boundary
      (Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.anchor_onGrid annulus) 0
      (annulus.boundary_winding.trans (by decide)) sheet

/-- Two original Newton-band tours return to the retained starting sheet. -/
theorem doubleBoundary_return (annulus : Faces.AnnularFaces grid index) {frames :
    RootIsolation.SquareRoot.Grid.RootFrames
  grid.shrunk.prepared.grid}
    (edges : RootEdgeBank frames) (sheet : Fin 2) :
    RootEdgeBank.target edges (Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary annulus) sheet =
      sheet := by
  rw [Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary, RootEdgeBank.target_append edges,
    Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.boundary_swap,
    Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.boundary_swap,
    BranchCutLifts.otherSheet_other]

/-- Find the original branch-labelled hole by finite traversal, retaining its list membership and exact branch index. -/
@[expose] def findHole (index : Data.Index branches) :
    ∀ (holes : List (PuncturedGridFaces.BranchHole grid.shrunk.prepared.toBranchCellBank)), (∃ hole ∈ holes, hole.index
      = index) →
      { hole : PuncturedGridFaces.BranchHole grid.shrunk.prepared.toBranchCellBank // hole ∈ holes ∧ hole.index = index
        }
  | [], found => False.elim (by obtain ⟨_, member, _⟩ := found; cases member)
  | hole :: tail, found =>
      if same : hole.index = index then ⟨hole, List.mem_cons_self, same⟩
      else
        let rest := Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.findHole index tail (by
          obtain ⟨other, member, equal⟩ := found
          rcases Membership.mem_cons.mp member with rfl | member
          · exact (same equal).elim
          · exact ⟨other, member, equal⟩)
        ⟨rest.val, List.mem_cons_of_mem _ rest.property.1, rest.property.2⟩

set_option genInjectivity false in
/-- All runtime lists and loop anchors are retained. Generated caches can provide these same geometric and indexed
readbacks without replaying lookup.

The selected triangles, complementary triangles, actual hole and boundary tours retain the original annulus and lifted
grid. The stored equations link each cache to that same selection. -/
structure Lifted (annulus : Faces.AnnularFaces grid index) (lifted : Meshes.LiftedPuncturedGrid grid.punctured) where
  /-- The retained lifts of exactly the original annular regular faces. -/ selected : GridLiftedMesh.LiftedFaces
    lifted.vertices lifted.edges annulus.faces
  /-- The cached oriented triangle list of the selected original lifted annulus. -/ triangles : List
    (Stokes.OrientedTriangle lifted.vertices.count)
  /-- The cached annular triangle list is exactly the retained selected lifts' triangle list. -/ triangles_eq :
    triangles = selected.triangles
  /-- Every cached annular triangle belongs to the original complete lifted mesh. -/ triangles_mem : ∀ triangle ∈
    triangles, triangle ∈ lifted.mesh.triangles
  /-- The cached original lifted triangles outside the selected annulus. -/ complement : List (Stokes.OrientedTriangle
    lifted.vertices.count)
  /-- The selected annulus and retained complement partition every finite triangle-value sum of the original lifted
    mesh. -/ partition : ∀ value : Stokes.OrientedTriangle lifted.vertices.count → Data.Gaussian.Basic.Canonical,
    CellBoundary.sumValues value triangles + CellBoundary.sumValues value complement = CellBoundary.sumValues value
      lifted.mesh.triangles
  /-- The retained original branch hole enclosed by this Newton band. -/ hole : PuncturedGridFaces.BranchHole
    grid.shrunk.prepared.toBranchCellBank
  /-- The retained branch hole belongs to the original face bank. -/ hole_mem : hole ∈ grid.faces.holes
  /-- The retained hole has exactly the original selected branch index. -/ hole_index : hole.index = index
  /-- The cached indexed edge word of the original two-lap Newton-band tour. -/ outer : List (Stokes.OrientedEdge
    lifted.vertices.count)
  /-- The outer word is exactly the original double boundary lifted from sheet zero. -/ outer_eq : outer =
    lifted.edges.indexedEdges lifted.vertices
    (Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary annulus) 0
  /-- The cached indexed edge word of the original clockwise branch-hole tour. -/ inner : List (Stokes.OrientedEdge
    lifted.vertices.count)
  /-- The inner word is exactly the retained hole's original lifted boundary. -/ inner_eq : inner = hole.liftedBoundary
    lifted.vertices lifted.edges
  /-- The retained original indexed sheet-zero anchor of the outer tour. -/ outerAnchor : Fin lifted.vertices.count
  /-- The outer anchor is exactly the original Newton-band lower-left vertex index on sheet zero. -/ outerAnchor_eq :
    outerAnchor = lifted.vertices.index (grid.bands.box index).anchor
    (Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.anchor_onGrid annulus) 0
  /-- The retained original indexed sheet-zero anchor of the inner tour. -/ innerAnchor : Fin lifted.vertices.count
  /-- The inner anchor is exactly the original hole anchor vertex index on sheet zero. -/ innerAnchor_eq : innerAnchor =
    lifted.vertices.index hole.cell.box.anchor (hole.cell.anchor_mem hole.member) 0

constructive_injectivity Lifted

namespace Lifted

variable {annulus : Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index} {lifted :
  Purelib.Riemann.Meshes.LiftedPuncturedGrid grid.punctured}

/-- Select and cache the original annular lifted faces around the supplied original labelled hole.

The triangle complement, exact indexed boundary words and original sheet-zero anchors are retained with their readback
certificates. -/
@[expose] def ofHole (annulus : Faces.AnnularFaces grid index) (lifted : Meshes.LiftedPuncturedGrid grid.punctured)
    (hole : PuncturedGridFaces.BranchHole grid.shrunk.prepared.toBranchCellBank) (member : hole ∈ grid.faces.holes)
    (label : hole.index = index) : Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted :=
  let box := grid.bands.box index
  let keep := fun face : PuncturedGridFaces.RegularFace grid.shrunk.prepared.toBranchCellBank => decide
    (face.cell.box.Refines box)
  let selection := GridLiftedFaceSelection.select keep lifted.mesh.lifts
  let selected := GridLiftedFaceSelection.reindex selection.selected
    (selection.kept_eq.trans annulus.faces_eq.symm)
  { selected := selected
    triangles := selected.triangles
    triangles_eq := rfl
    triangles_mem := fun triangle member => by
      rw [GridLiftedFaceSelection.reindex_triangles] at member
      rw [lifted.mesh.triangles_eq]
      exact GridLiftedFaceSelection.select_triangle_mem keep lifted.mesh.lifts triangle member
    complement := selection.rejected.triangles
    partition := fun value => by
      rw [GridLiftedFaceSelection.reindex_triangles, lifted.mesh.triangles_eq]
      exact GridLiftedFaceSelection.select_sum keep value lifted.mesh.lifts
    hole := hole
    hole_mem := member
    hole_index := label
    outer := lifted.edges.indexedEdges lifted.vertices
      (Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary annulus) 0
    outer_eq := rfl
    inner := hole.liftedBoundary lifted.vertices lifted.edges
    inner_eq := rfl
    outerAnchor := lifted.vertices.index (grid.bands.box index).anchor
      (Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.anchor_onGrid annulus) 0
    outerAnchor_eq := rfl
    innerAnchor := lifted.vertices.index hole.cell.box.anchor (hole.cell.anchor_mem hole.member) 0
    innerAnchor_eq := rfl }

/-- Locate the original labelled branch hole and cache its lifted annulus and exact boundary tours. -/
@[expose] def build (annulus : Faces.AnnularFaces grid index) (lifted : Meshes.LiftedPuncturedGrid grid.punctured) :
  Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted :=
  let found := Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.findHole index grid.faces.holes
    (grid.faces.hole_complete index)
  Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted.ofHole annulus lifted found.val found.property.1
    found.property.2

/-- Constructing from an original retained hole preserves exactly the selected lifted-face triangle list. -/
theorem ofHole_triangles (annulus : Faces.AnnularFaces grid index) (lifted : Meshes.LiftedPuncturedGrid grid.punctured)
    (hole : PuncturedGridFaces.BranchHole grid.shrunk.prepared.toBranchCellBank) (member : hole ∈ grid.faces.holes)
    (label : hole.index = index) :
    (Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted.ofHole annulus lifted hole member label).triangles
      =
      (GridLiftedFaceSelection.select
        (fun face => decide (face.cell.box.Refines (grid.bands.box index))) lifted.mesh.lifts).selected.triangles :=
  GridLiftedFaceSelection.reindex_triangles _ _

/-- The retained lifted annulus has four oriented triangles per original regular face. -/
theorem triangleCount (region : Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted) :
  region.triangles.length = 4 * annulus.faces.length := by
  rw [region.triangles_eq]
  exact region.selected.triangles_length

/-- Every retained annular triangle has strictly positive original geometric area. -/
theorem triangle_positive (region : Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted)
  (triangle : Stokes.OrientedTriangle lifted.vertices.count)
    (member : triangle ∈ region.triangles) : 0 < LiftedFaces.triangleArea lifted.vertices triangle := by
  rw [region.triangles_eq] at member
  exact region.selected.triangle_positive triangle member

/-- The original two-lap outer indexed edge word closes at its retained sheet-zero anchor. -/
theorem outer_closed (region : Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish region.outer region.outerAnchor region.outerAnchor
      := by
  rw [region.outer_eq, region.outerAnchor_eq]
  exact lifted.edges.indexedEdges_closed lifted.vertices
    (Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary annulus)
    (Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.anchor_onGrid annulus) 0
    (Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary_return annulus lifted.edges 0)

/-- The original inner indexed edge word closes at its retained sheet-zero anchor. -/
theorem inner_closed (region : Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish region.inner region.innerAnchor region.innerAnchor
      := by
  rw [region.inner_eq, region.innerAnchor_eq]
  exact region.hole.liftedBoundary_closed lifted.vertices lifted.edges

/-- The retained outer indexed word has twice the original Newton-band boundary edge count.

Both indexed boundary copies retain their original walk and sheet transitions. Their displayed list lengths add to twice
the original edge count. -/
theorem outer_length (region : Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted) :
  region.outer.length = 2 * annulus.boundary.edgeCount :=
  (congrArg List.length (region.outer_eq.trans
    (lifted.edges.indexedEdges_append lifted.vertices annulus.boundary annulus.boundary 0))).trans
      ((Append.length_append _ _).trans
        ((congrArg₂ (· + ·)
          (RootEdgeBank.indexedEdges_length lifted.edges lifted.vertices annulus.boundary 0)
          (RootEdgeBank.indexedEdges_length lifted.edges lifted.vertices annulus.boundary (RootEdgeBank.target
            lifted.edges annulus.boundary 0))).trans
            (Nat.two_mul _).symm))

/-- The original lifted branch-hole boundary has eight indexed edges. -/
theorem inner_length (region : Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted) :
  region.inner.length = 8 := by
  rw [region.inner_eq]
  exact region.hole.liftedBoundary_length lifted.vertices lifted.edges

/-- The retained two-lap outer area equals the original two-sheet Newton-band boundary area. -/
theorem outer_area (region : Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted) (primitive
  : Fin lifted.vertices.count → Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive region.outer = lifted.edges.twoSheetArea lifted.vertices primitive annulus.boundary :=
      by
  have second := congrArg (fun sheet => lifted.edges.indexedEdges lifted.vertices annulus.boundary sheet)
    (Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.boundary_swap annulus lifted.edges 0)
  exact (congrArg (Stokes.edgeListArea primitive) (region.outer_eq.trans
    (lifted.edges.indexedEdges_append lifted.vertices annulus.boundary annulus.boundary 0))).trans
      ((Stokes.edgeListArea_append _ _ _).trans
        (congrArg (fun rest => Stokes.edgeListArea primitive (lifted.edges.indexedEdges lifted.vertices annulus.boundary
          0) +
          Stokes.edgeListArea primitive rest) second))

/-- The retained inner area equals the original two-sheet inward branch-hole boundary area. -/
theorem inner_area (region : Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted) (primitive
  : Fin lifted.vertices.count → Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive region.inner = lifted.edges.twoSheetArea lifted.vertices primitive
      region.hole.inwardBoundary := by
  rw [region.inner_eq]
  exact region.hole.liftedBoundary_area lifted.vertices lifted.edges primitive

/-- Actual selected surface triangles equal the outer two-lap tour plus the clockwise two-lap hole tour, for independent
values on the two sheets. -/
theorem triangleEdges_area (region : Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted)
  (primitive : Fin lifted.vertices.count → Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive (region.triangles.flatMap OrientedTriangle.boundary) =
      Stokes.edgeListArea primitive region.outer + Stokes.edgeListArea primitive region.inner := by
  let values := RootEdgeBank.edgeValues lifted.edges lifted.vertices primitive
  have walks {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk grid.shrunk.prepared.grid start finish) :
      values.walk walk = lifted.edges.twoSheetArea lifted.vertices primitive walk :=
    RootEdgeBank.edgeValues_walk lifted.edges lifted.vertices primitive
      (fun point member => (BranchCellBank.referenceAt grid.shrunk.prepared.toBranchCellBank point member).toLoop) walk
  have holeValue : values.walk region.hole.inwardBoundary =
      -values.cellBoundary (grid.shrunk.prepared.toBranchCellBank.cell index) := by
    rw [region.hole.inwardBoundary_value, region.hole.cell_eq, region.hole_index]
  have balance := annulus.boundary_balance values
  have balance : CellBoundary.sumValues (fun face => values.walk face.boundary) annulus.faces =
      values.walk annulus.boundary + values.walk region.hole.inwardBoundary := by
    rw [holeValue, ← balance]
    ring1
  rw [region.triangles_eq, region.selected.triangleEdges_area primitive, LiftedFaces.actualBoundaries_area]
  calc
    _ = CellBoundary.sumValues (fun face => values.walk face.boundary) annulus.faces :=
      CellBoundary.sumValues_congr _ _ _ (fun face _ => (walks face.boundary).symm)
    _ = values.walk annulus.boundary + values.walk region.hole.inwardBoundary := balance
    _ = _ := congrArg₂ (· + ·) ((walks annulus.boundary).trans (region.outer_area primitive).symm)
      ((walks region.hole.inwardBoundary).trans (region.inner_area primitive).symm)

/-- The concatenated original triangle-boundary area equals the finite sum of the individual original triangle areas. -/
theorem triangleEdges_sum {count : Nat} (primitive : Fin count → Stokes.PrimitivePoint)
    (triangles : List (Stokes.OrientedTriangle count)) :
    Stokes.edgeListArea primitive (triangles.flatMap OrientedTriangle.boundary) =
      CellBoundary.sumValues (fun triangle => Stokes.edgeListArea primitive triangle.boundary) triangles := by
  induction triangles with
  | nil => rfl
  | cons triangle tail ih =>
      rw [Flatten.flatMap_cons, Stokes.edgeListArea_append, ih]
      rfl

/-- Delete exactly this annulus from the original lifted mesh.

The remaining cached triangles plus the two actual boundary tours account for the full original primitive area, even
when individual readings are signed. -/
theorem complement_area (region : Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted)
  (primitive : Fin lifted.vertices.count → Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive (region.complement.flatMap OrientedTriangle.boundary) +
      Stokes.edgeListArea primitive region.outer + Stokes.edgeListArea primitive region.inner =
        Stokes.edgeListArea primitive lifted.mesh.triangulation.boundary := by
  have partition := region.partition (fun triangle => Stokes.edgeListArea primitive triangle.boundary)
  rw [← Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted.triangleEdges_sum primitive region.triangles, ←
    Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted.triangleEdges_sum primitive region.complement,
    ← Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted.triangleEdges_sum primitive
      lifted.mesh.triangles, region.triangleEdges_area primitive,
    lifted.mesh.triangles_eq, lifted.mesh.lifts.triangleEdges_area primitive,
    ← lifted.mesh.boundary_eq_faceWalks primitive] at partition
  exact (show _ = (Stokes.edgeListArea primitive region.outer + Stokes.edgeListArea primitive region.inner) +
    Stokes.edgeListArea primitive (region.complement.flatMap OrientedTriangle.boundary) by ring1).trans partition

/-- The thin grid-hole term is exchanged for the enclosing Newton-band term by an exact change of the retained surface,
not by assuming either boundary area vanishes.

This is the physical-boundary excision identity. -/
theorem excision_area (region : Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted)
  (primitive : Fin lifted.vertices.count → Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive lifted.mesh.triangulation.boundary - Stokes.edgeListArea primitive region.inner =
      Stokes.edgeListArea primitive (region.complement.flatMap OrientedTriangle.boundary) + Stokes.edgeListArea
        primitive region.outer := by
  rw [← region.complement_area primitive]
  ring1

end Lifted
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary

end
