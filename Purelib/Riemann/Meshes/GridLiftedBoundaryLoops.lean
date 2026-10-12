module
import Purelib.Riemann.Meshes.FramedPuncturedGrid
public import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Roots.Walk
import Purelib.Polynomial.Geometry.Grid.FromStates
public import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.RootIsolation.SquareRoot.Grid.Boundary.Values
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Riemann.Meshes.GridLiftedBoundary
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Closed lifted boundary tours

A clockwise branch-hole tour closes after two laps, not one.  The exterior
has one two-lap tour in odd degree and two one-lap tours in even degree.
All endpoint and sheet identities use the shared actual root transports.
These closed indexed lists realize the exterior-and-holes boundary-area
identity; they are not yet a symplectic cut-polygon boundary word.
-/

open Purelib.Data.List
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Geometry.Rational (Box)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_append sumValues_map sumValues_congr)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeListArea edgeListArea_append)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)

open
  Purelib.Riemann.RootContinuation

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

variable {polynomial : GaussianPolynomial} {ambient :
  Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient} {frames : RootFrames grid}

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The indexed lift of appended walks concatenates their edge lists at the transported middle sheet. -/
theorem indexedEdges_append (edges : SquareRoot.Grid.RootEdgeBank frames) (vertices :
  SquareRoot.Grid.LiftedVertices.VertexBank grid) :
    {start middle finish : Gaussian.Basic.Canonical} → (left : Geometry.Grid.Walks.Walk grid start middle) → (right :
      Geometry.Grid.Walks.Walk grid middle finish) → (sheet : Fin 2) →
      edges.indexedEdges vertices (left.append right) sheet =
        edges.indexedEdges vertices left sheet ++ edges.indexedEdges vertices right
          (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges left sheet)
  | _, _, _, .nil _, _, _ => rfl
  | _, _, _, .cons edge tail, right, sheet =>
      congrArg (List.cons (edges.indexedEdge vertices edge sheet))
        (edges.indexedEdges_append vertices tail right ((edges.edge edge).forward.target sheet))

open Purelib.Topology
open Purelib.Data
open Purelib.Polynomial
open Purelib.RootIsolation
/-- The indexed lifted walk has exactly the retained start and transported finish vertices. -/
theorem indexedEdges_endpoints (edges : SquareRoot.Grid.RootEdgeBank frames) (vertices :
  SquareRoot.Grid.LiftedVertices.VertexBank grid) :
    {start finish : Gaussian.Basic.Canonical} → (walk : Geometry.Grid.Walks.Walk grid start finish) →
    (first : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid start) → (last :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex grid finish) → (sheet : Fin 2) →
      Chain.PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (edges.indexedEdges vertices walk sheet)
        (vertices.index start first sheet) (vertices.index finish last (SquareRoot.Grid.EdgeBank.RootEdgeBank.target
          edges walk sheet))
  | _, _, .nil _, _, _, _ => .nil _
  | _, _, .cons edge tail, _, last, sheet =>
      .cons (edges.indexedEdges_endpoints vertices tail edge.vertices.2 last ((edges.edge edge).forward.target sheet))

/-- A walk whose sheet transport returns has a closed indexed lift. -/
theorem indexedEdges_closed (edges : SquareRoot.Grid.RootEdgeBank frames) (vertices :
  SquareRoot.Grid.LiftedVertices.VertexBank grid) {base : Gaussian.Basic.Canonical}
    (walk : Geometry.Grid.Walks.Walk grid base base) (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid
      base)
      (sheet : Fin 2)
    (returned : SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges walk sheet = sheet) :
    Chain.PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (edges.indexedEdges vertices walk sheet)
      (vertices.index base member sheet) (vertices.index base member sheet) :=
  (edges.indexedEdges_endpoints vertices walk member member sheet).castFinish
    (congrArg (vertices.index base member) returned)

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.BranchHole

variable {bank : BranchCellBank curve branches higher} {frames :
  RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

open Purelib.Polynomial in
/-- Traverse the retained inward branch-hole boundary twice.

Both laps use the same original inward walk, retaining its anchor, ordered
edges and endpoint witnesses. -/
@[expose] def doubleBoundary (hole : BranchHole bank) : Geometry.Grid.Walks.Walk bank.grid hole.cell.box.anchor
  hole.cell.box.anchor :=
  hole.inwardBoundary.append hole.inwardBoundary

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.RootIsolation in
/-- Two inward branch-hole laps return each original sheet to itself. -/
theorem doubleBoundary_return (hole : BranchHole bank) (edges : SquareRoot.Grid.RootEdgeBank frames) (sheet
  : Fin 2) :
    SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges hole.doubleBoundary sheet = sheet := by
  rw [Meshes.PuncturedGridFaces.BranchHole.doubleBoundary, SquareRoot.Grid.EdgeBank.RootEdgeBank.target_append edges,
    RootContinuation.GridRootWalks.BranchCellBank.BranchHole.sharedTransport_swap
    hole edges,
    RootContinuation.GridRootWalks.BranchCellBank.BranchHole.sharedTransport_swap
    hole edges,
    Hyperelliptic.Branches.BranchCutLifts.otherSheet_other]

open Purelib.RootIsolation in
/-- The actual indexed branch-hole tour formed by two inward laps from sheet zero.

The original root-edge bank transports the sheet along both retained laps.
The vertex bank supplies each original indexed endpoint. -/
@[expose] def liftedBoundary (hole : BranchHole bank) (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid)
  (edges : SquareRoot.Grid.RootEdgeBank frames) :
    List (OrientedEdge vertices.count) := edges.indexedEdges vertices hole.doubleBoundary 0

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.RootIsolation in
/-- The lifted hole boundary concatenates one inward lap on each original sheet. -/
theorem liftedBoundary_eq (hole : BranchHole bank) (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid)
  (edges : SquareRoot.Grid.RootEdgeBank frames) :
    hole.liftedBoundary vertices edges =
      edges.indexedEdges vertices hole.inwardBoundary 0 ++ edges.indexedEdges vertices hole.inwardBoundary 1 := by
  rw [Meshes.PuncturedGridFaces.BranchHole.liftedBoundary, Meshes.PuncturedGridFaces.BranchHole.doubleBoundary,
    edges.indexedEdges_append,
    RootContinuation.GridRootWalks.BranchCellBank.BranchHole.sharedTransport_swap
    hole edges]
  rfl

open Purelib.Topology in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The actual two-lap lifted hole tour is closed at its retained anchor vertex. -/
theorem liftedBoundary_closed (hole : BranchHole bank) (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid)
  (edges : SquareRoot.Grid.RootEdgeBank frames) :
    Chain.PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (hole.liftedBoundary vertices edges)
      (vertices.index hole.cell.box.anchor (Geometry.Grid.ClearGrid.Cell.anchor_mem hole.cell hole.member) 0)
      (vertices.index hole.cell.box.anchor (Geometry.Grid.ClearGrid.Cell.anchor_mem hole.cell hole.member) 0) :=
  edges.indexedEdges_closed vertices hole.doubleBoundary (Geometry.Grid.ClearGrid.Cell.anchor_mem hole.cell hole.member)
    0 (hole.doubleBoundary_return edges 0)

open Purelib.RootIsolation
/-- The retained lifted branch-hole tour contains exactly eight oriented edges.

Each original inward lap contributes four edges. Concatenation retains both
ordered laps on their original sheets. -/
theorem liftedBoundary_length (hole : BranchHole bank) (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid)
  (edges : SquareRoot.Grid.RootEdgeBank frames) :
    (hole.liftedBoundary vertices edges).length = 8 := by
  rw [hole.liftedBoundary_eq, Append.length_append, edges.indexedEdges_length, edges.indexedEdges_length]
  rfl

/-- The lifted hole tour area equals the actual two-sheet inward boundary area. -/
theorem liftedBoundary_area (hole : BranchHole bank) (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid)
  (edges : SquareRoot.Grid.RootEdgeBank frames)
    (primitive : Fin vertices.count → PrimitivePoint) :
    edgeListArea primitive (hole.liftedBoundary vertices edges) = edges.twoSheetArea vertices primitive
      hole.inwardBoundary := by
  rw [hole.liftedBoundary_eq, edgeListArea_append]
  rfl

end Purelib.Riemann.Meshes.PuncturedGridFaces.BranchHole

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

variable {base : FramedPuncturedGrid curve branches higher}

section
open Purelib.Curves
open Purelib.RootIsolation
/-- An even-degree exterior lap returns its original sheet. -/
theorem exterior_return_even (lifted : LiftedPuncturedGrid base) (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (sheet : Fin 2) : SquareRoot.Grid.EdgeBank.RootEdgeBank.target lifted.edges base.bank.exterior sheet = sheet :=
  SquareRoot.Grid.EdgeBank.RootEdgeBank.target_even lifted.edges
    (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank _
    ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩).toLoop
    base.bank.exterior ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩ (genus + 1)
    (by have winding := base.bank.exterior_winding; omega) sheet

/-- An odd-degree exterior lap swaps the two retained sheets. -/
theorem exterior_swap_odd (lifted : LiftedPuncturedGrid base) (degree : curve.polynomial.natDegree = 2 * genus + 1)
    (sheet : Fin 2) : SquareRoot.Grid.EdgeBank.RootEdgeBank.target lifted.edges base.bank.exterior sheet =
      Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet :=
  SquareRoot.Grid.EdgeBank.RootEdgeBank.target_odd lifted.edges base.bank.exterior ⟨base.bank.frame.xLower,
    base.bank.frame.yLower⟩ genus
    (by have winding := base.bank.exterior_winding; omega) sheet

/-- Two odd-degree exterior laps return the original sheet. -/
theorem exterior_double_return_odd (lifted : LiftedPuncturedGrid base) (degree : curve.polynomial.natDegree = 2 * genus
  + 1)
    (sheet : Fin 2) : SquareRoot.Grid.EdgeBank.RootEdgeBank.target lifted.edges (base.bank.exterior.append
      base.bank.exterior) sheet = sheet := by
  rw [SquareRoot.Grid.EdgeBank.RootEdgeBank.target_append lifted.edges, lifted.exterior_swap_odd degree,
    lifted.exterior_swap_odd degree,
    Hyperelliptic.Branches.BranchCutLifts.otherSheet_other]

end

/-- Select the actual closed exterior tours from the curve's degree shape.

Odd degree uses one two-lap tour; even degree uses two one-lap tours with the existing root transports and indexed
vertices. -/
@[expose] def exteriorBoundaries (lifted : LiftedPuncturedGrid base) : List (List (OrientedEdge lifted.vertices.count))
  :=
  match curve.degreeShape with
  | .odd _ => [lifted.edges.indexedEdges lifted.vertices (base.bank.exterior.append base.bank.exterior) 0]
  | .even _ => [lifted.edges.indexedEdges lifted.vertices base.bank.exterior 0,
      lifted.edges.indexedEdges lifted.vertices base.bank.exterior 1]

open Purelib.Riemann in
open Purelib.Topology in
/-- Every retained exterior tour closes at an actual indexed vertex.

Odd degree retains one two-lap tour; even degree retains one tour on each
sheet. Their original transport return certificates identify the anchors. -/
theorem exteriorBoundaries_closed (lifted : LiftedPuncturedGrid base) : ∀ boundary ∈ lifted.exteriorBoundaries,
    ∃ anchor, Chain.PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish boundary anchor anchor := by
  intro boundary member
  cases shape : curve.degreeShape with
  | odd degree =>
      rw [Meshes.LiftedPuncturedGrid.exteriorBoundaries, shape] at member
      have equal := Membership.mem_singleton.mp member
      cases equal
      exact ⟨_, lifted.edges.indexedEdges_closed lifted.vertices _ ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩ 0
        (lifted.exterior_double_return_odd degree 0)⟩
  | even degree =>
      rw [Meshes.LiftedPuncturedGrid.exteriorBoundaries, shape] at member
      rcases Membership.mem_cons.mp member with equal | member
      · cases equal
        exact ⟨_, lifted.edges.indexedEdges_closed lifted.vertices _ ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩ 0
          (lifted.exterior_return_even degree 0)⟩
      · have equal := Membership.mem_singleton.mp member
        cases equal
        exact ⟨_, lifted.edges.indexedEdges_closed lifted.vertices _ ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩ 1
          (lifted.exterior_return_even degree 1)⟩

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The retained exterior tours sum to the actual two-sheet exterior area. -/
theorem exteriorBoundaries_area (lifted : LiftedPuncturedGrid base) (primitive : Fin lifted.vertices.count →
  PrimitivePoint) :
    Geometry.Grid.CellBoundary.sumValues (edgeListArea primitive) lifted.exteriorBoundaries =
      lifted.edges.twoSheetArea lifted.vertices primitive base.bank.exterior := by
  cases shape : curve.degreeShape with
  | odd degree =>
      simp only [Meshes.LiftedPuncturedGrid.exteriorBoundaries, shape, Geometry.Grid.CellBoundary.sumValues]
      rw [lifted.edges.indexedEdges_append, lifted.exterior_swap_odd degree,
        Hyperelliptic.Branches.BranchCutLifts.otherSheet_zero, edgeListArea_append]
      change _ + _ + 0 = _ + _
      ring1
  | even _ =>
      simp only [Meshes.LiftedPuncturedGrid.exteriorBoundaries, shape, Geometry.Grid.CellBoundary.sumValues,
        SquareRoot.Grid.RootEdgeBank.twoSheetArea]
      ring1

/-- The retained exterior tours followed by the original ordered branch-hole tours.

The degree shape selects the original exterior tours. Each retained hole
then contributes its indexed doubled tour in the original hole-list order. -/
@[expose] def boundaryLoops (lifted : LiftedPuncturedGrid base) : List (List (OrientedEdge lifted.vertices.count)) :=
  lifted.exteriorBoundaries ++ base.faces.holes.map (fun hole => hole.liftedBoundary lifted.vertices lifted.edges)

open Purelib.Riemann in
/-- The boundary-loop count is the number of holes plus one or two exterior tours according to degree parity.

Every original hole contributes one retained doubled tour. The exterior
contributes one or two tours according to its original degree-shape branch. -/
theorem boundaryLoops_length (lifted : LiftedPuncturedGrid base) :
    lifted.boundaryLoops.length = base.faces.holes.length +
      (match curve.degreeShape with | .odd _ => 1 | .even _ => 2) := by
  rw [Meshes.LiftedPuncturedGrid.boundaryLoops, Append.length_append, Map.length_map]
  cases shape : curve.degreeShape <;> simp only [Meshes.LiftedPuncturedGrid.exteriorBoundaries, shape, List.length_cons,
    List.length_nil] <;> omega

open Purelib.Topology in
open Purelib.Data in
/-- Every retained boundary loop is closed at its actual indexed anchor.

The original ordered list first contains the exterior tours and then one
lifted tour per retained branch hole. Each occurrence uses its original closure. -/
theorem boundaryLoops_closed (lifted : LiftedPuncturedGrid base) : ∀ boundary ∈ lifted.boundaryLoops,
    ∃ anchor, Chain.PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish boundary anchor anchor := by
  intro boundary member
  rcases Membership.mem_append.mp member with exterior | holeMember
  · exact lifted.exteriorBoundaries_closed boundary exterior
  · rcases List.Map.mem_map.mp holeMember with ⟨hole, _, equal⟩
    cases equal
    exact ⟨_, hole.liftedBoundary_closed lifted.vertices lifted.edges⟩

open Purelib.Riemann in
open Purelib.Polynomial in
/-- The mesh boundary area equals the sum of the actual closed indexed tours.

The equality preserves the exterior and hole occurrences with their original orientation and root transport. -/
theorem boundary_eq_closedLoops (lifted : LiftedPuncturedGrid base) (primitive : Fin lifted.vertices.count →
  PrimitivePoint) :
    edgeListArea primitive lifted.mesh.triangulation.boundary = Geometry.Grid.CellBoundary.sumValues (edgeListArea
      primitive) lifted.boundaryLoops := by
  rw [lifted.boundary_eq_exterior_and_holes, Meshes.LiftedPuncturedGrid.boundaryLoops,
    Geometry.Grid.CellBoundary.sumValues_append, lifted.exteriorBoundaries_area,
    Geometry.Grid.CellBoundary.sumValues_map]
  exact congrArg (fun holes => lifted.edges.twoSheetArea lifted.vertices primitive base.bank.exterior + holes)
    (Geometry.Grid.CellBoundary.sumValues_congr _ _ _ (fun hole _ => (hole.liftedBoundary_area lifted.vertices
      lifted.edges primitive).symm))

end Purelib.Riemann.Meshes.LiftedPuncturedGrid
