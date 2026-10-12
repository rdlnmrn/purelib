module
import Purelib.Data.List.Append
import Purelib.Data.List.Reverse
import Purelib.Data.List.Membership
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
import Purelib.Data.List.Pairwise
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalBoundaryChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.VertexLiftChoices
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops

open Purelib

@[expose] public section

/-!
# Simple root-lifted boundary walks

A base walk visiting each source coordinate once has a simple lift. Its two
initial sheets give disjoint lifted source indices: the same coordinate can
only occur at the same position, where the actual edge transports are
injective. Thus a branch-hole double tour visits each lifted corner once.
-/

section

open Purelib.Data.List

open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Polynomial.Geometry.Grid.Walks.Walk (reverseOnto reverse)
open _root_.Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient}

section
open Purelib.Data
open Purelib.Polynomial

namespace Purelib.Polynomial.Geometry.Grid.Walks.Walk

/-- List the starting coordinate of every edge in a grid walk. -/
def startCoordinates : {start finish : Gaussian.Basic.Canonical} →
  Geometry.Grid.Walks.Walk grid start finish → List Gaussian.Basic.Canonical
  | _, _, .nil _ => []
  | start, _, .cons _ tail => start :: startCoordinates tail

/-- List the finishing coordinate of every edge in a grid walk. -/
def finishCoordinates : {start finish : Gaussian.Basic.Canonical} →
  Geometry.Grid.Walks.Walk grid start finish → List Gaussian.Basic.Canonical
  | _, _, .nil _ => []
  | _, _, .cons (middle := middle) _ tail => middle :: finishCoordinates tail

end Purelib.Polynomial.Geometry.Grid.Walks.Walk

end

open Purelib.Polynomial.Geometry.Grid.Walks.Walk (startCoordinates finishCoordinates)

section
open Purelib.Data
open Purelib.Polynomial

namespace Purelib.Polynomial.Geometry.Grid.Walks.Walk

/-- Concatenating grid walks concatenates their lists of starting coordinates. -/
theorem startCoordinates_append : ∀ {start middle finish :
  Gaussian.Basic.Canonical}
    (first : Geometry.Grid.Walks.Walk grid start middle) (last : Geometry.Grid.Walks.Walk grid middle finish),
    (first.append last).startCoordinates = first.startCoordinates ++ last.startCoordinates
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons _ tail, last => congrArg (List.cons _) (tail.startCoordinates_append last)

/-- Reversing a walk onto another reverses its finishing coordinates before the other starting coordinates.

The original walk retains the same ordered coordinates and sheet transports.
Structural list certificates preserve their displayed reversal, concatenation
and membership witnesses without changing the retained vertices. -/
theorem startCoordinates_reverseOnto : ∀ {start middle finish :
  Gaussian.Basic.Canonical}
    (first : Geometry.Grid.Walks.Walk grid start middle) (last : Geometry.Grid.Walks.Walk grid start finish),
    (first.reverseOnto last).startCoordinates = first.finishCoordinates.reverse ++ last.startCoordinates
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons edge tail, last => by
      rw [Geometry.Grid.Walks.Walk.reverseOnto, tail.startCoordinates_reverseOnto]
      simp only [Geometry.Grid.Walks.Walk.finishCoordinates, Reverse.reverse_cons,
        Geometry.Grid.Walks.Walk.startCoordinates, Append.append_assoc,
        List.cons_append, List.nil_append, -eq_self, -iff_self]
      rfl

/-- The reversed walk starts at the original finishing coordinates in reverse order.

The original walk retains the same ordered coordinates and sheet transports.
Structural list certificates preserve their displayed reversal, concatenation
and membership witnesses without changing the retained vertices. -/
theorem startCoordinates_reverse {start finish :
  Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid start finish) :
    walk.reverse.startCoordinates = walk.finishCoordinates.reverse := by
  rw [Geometry.Grid.Walks.Walk.reverse, walk.startCoordinates_reverseOnto]
  exact Append.append_nil _

/-- Transporting endpoint equalities preserves the starting-coordinate list. -/
theorem startCoordinates_castEndpoints {start finish first last :
  Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid start finish)
    (startEq : start = first) (finishEq : finish = last) :
    (walk.castEndpoints startEq finishEq).startCoordinates = walk.startCoordinates := by
  cases startEq
  cases finishEq
  rfl

end Purelib.Polynomial.Geometry.Grid.Walks.Walk

end

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient} {frames : RootIsolation.SquareRoot.Grid.RootFrames grid}

section
open Purelib.Data
open Purelib.Polynomial
open Purelib.RootIsolation

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

/-- Projecting indexed lifted edge starts gives the base walk's starting coordinates. -/
theorem indexedStarts_coordinates (edges :
  SquareRoot.Grid.RootEdgeBank frames) (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid) :
    ∀ {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid start finish) (sheet : Fin 2),
      ((edges.indexedEdges vertices walk sheet).map OrientedEdge.start).map vertices.coordinate = walk.startCoordinates
  | _, _, .nil _, _ => rfl
  | _, _, .cons edge tail, sheet => by
      simp only [SquareRoot.Grid.RootEdgeBank.indexedEdges, List.map_cons,
        SquareRoot.Grid.RootEdgeBank.indexedEdge, vertices.coordinate_index,
        Geometry.Grid.Walks.Walk.startCoordinates]
      exact congrArg (List.cons _) (edges.indexedStarts_coordinates vertices tail _)

/-- The coordinate of an indexed lifted start belongs to the base walk's starting-coordinate list. -/
theorem indexedStart_coordinate_mem (edges :
  SquareRoot.Grid.RootEdgeBank frames) (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid)
    {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid start finish) (sheet : Fin 2)
    {vertex : Fin vertices.count} (member : vertex ∈ (edges.indexedEdges vertices walk sheet).map OrientedEdge.start) :
    vertices.coordinate vertex ∈ walk.startCoordinates := by
  rw [← edges.indexedStarts_coordinates vertices walk sheet]
  exact List.Map.mem_map_of_mem member

/-- Distinct starting coordinates imply distinct starting vertices in a fixed-sheet lift. -/
theorem indexedStarts_nodup (edges :
  SquareRoot.Grid.RootEdgeBank frames) (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid)
    {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid start finish) (sheet : Fin 2)
      (simple : walk.startCoordinates.Nodup) :
    ((edges.indexedEdges vertices walk sheet).map OrientedEdge.start).Nodup := by
  rw [← edges.indexedStarts_coordinates vertices walk sheet] at simple
  exact List.Pairwise.imp (fun different same => different (congrArg vertices.coordinate same))
    (List.Pairwise.pairwise_map.mp simple)

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

end

section
open Purelib.Riemann
open Purelib.Data
open Purelib.Polynomial
open Purelib.RootIsolation

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

/-- Lifts from different initial sheets have disjoint starting vertices on a simple base walk.

The starting coordinates are distinct, and the actual retained edge transports are injective using the supplied
winding-one reference loops. -/
theorem indexedStarts_disjoint (edges :
  SquareRoot.Grid.RootEdgeBank frames) (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point) :
    ∀ {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid start finish) (_ :
      walk.startCoordinates.Nodup)
      (first last : Fin 2), first ≠ last →
      ∀ left ∈ (edges.indexedEdges vertices walk first).map OrientedEdge.start,
        ∀ right ∈ (edges.indexedEdges vertices walk last).map OrientedEdge.start, left ≠ right
  | _, _, .nil _, _, _, _, _, _, member, _, _ => (List.not_mem_nil member).elim
  | start, _, .cons edge tail, simple, first, last, different, left, leftMember, right, rightMember => by
      have parts : start ∉ tail.startCoordinates ∧ tail.startCoordinates.Nodup := by
        cases simple with
        | cons apart distinct => exact ⟨fun member => apart _ member rfl, distinct⟩
      rcases Membership.mem_cons.mp leftMember with leftEq | leftTail
      · rcases Membership.mem_cons.mp rightMember with rightEq | rightTail
        · intro same
          exact different (vertices.index_same_sheet _ edge.vertices.1 first last (leftEq.symm.trans (same.trans
            rightEq)))
        · intro same
          have coordinate : vertices.coordinate (edges.indexedEdge vertices edge first).start = _ :=
            vertices.coordinate_index _ edge.vertices.1 first
          have member := edges.indexedStart_coordinate_mem vertices tail _ rightTail
          rw [← same, leftEq, coordinate] at member
          exact parts.1 member
      · rcases Membership.mem_cons.mp rightMember with rightEq | rightTail
        · intro same
          have coordinate : vertices.coordinate (edges.indexedEdge vertices edge last).start = _ :=
            vertices.coordinate_index _ edge.vertices.1 last
          have member := edges.indexedStart_coordinate_mem vertices tail _ leftTail
          rw [same, rightEq, coordinate] at member
          exact parts.1 member
        · exact edges.indexedStarts_disjoint vertices reference tail parts.2 _ _
            (fun same => different (((edges.edge edge).bijection (reference _ edge.vertices.1)
              (reference _ edge.vertices.2)).forward_injective same)) left leftTail right rightTail

/-- Concatenating both sheet lifts preserves distinct starting vertices for a simple base walk.

The original walk retains the same ordered coordinates and sheet transports.
Structural list certificates preserve their displayed reversal, concatenation
and membership witnesses without changing the retained vertices. -/
theorem twoSheetStarts_nodup (edges :
  SquareRoot.Grid.RootEdgeBank frames) (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)
    {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid start finish) (simple :
      walk.startCoordinates.Nodup) :
    (((edges.indexedEdges vertices walk 0) ++ (edges.indexedEdges vertices walk 1)).map OrientedEdge.start).Nodup := by
  rw [Map.map_append]
  exact List.Nodup.nodup_append (edges.indexedStarts_nodup vertices walk 0 simple)
    (edges.indexedStarts_nodup vertices walk 1 simple)
    (edges.indexedStarts_disjoint vertices reference walk simple 0 1 (by decide))

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

end

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher} {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.BranchHole

/-- The inward hole boundary starts at its four corners in clockwise order. -/
theorem inwardBoundary_starts (hole : BranchHole bank) :
    hole.inwardBoundary.startCoordinates =
      [hole.cell.box.anchor, point hole.cell.box.xLower hole.cell.box.yUpper,
        point hole.cell.box.xUpper hole.cell.box.yUpper, point hole.cell.box.xUpper hole.cell.box.yLower] := rfl

open Purelib.Data in
/-- The inward boundary of a proper branch-hole box has distinct starting coordinates. -/
theorem inwardBoundary_simple (hole : BranchHole bank) :
  hole.inwardBoundary.startCoordinates.Nodup := by
  rw [hole.inwardBoundary_starts]
  change ([GridSide.bottom, .left, .top, .right].map (fun side => side.start hole.cell.box)).Nodup
  exact Data.List.Nodup.nodup_map_of_injective
    (fun _ _ equal => GridSide.start_injective hole.cell.box_proper equal) (by decide)

open Purelib.Curves in
open Purelib.RootIsolation in
/-- The actual two-sheet hole boundary has no repeated starting vertices.

The simple rectangular base walk and winding-one reference transports separate the two lifted sheets. -/
theorem liftedBoundary_simple (hole : BranchHole bank)
  (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid)
    (edges : SquareRoot.Grid.RootEdgeBank frames) : ((hole.liftedBoundary vertices edges).map
      OrientedEdge.start).Nodup := by
  rw [hole.liftedBoundary_eq]
  exact edges.twoSheetStarts_nodup vertices (fun point member =>
    (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt bank point member).toLoop)
    hole.inwardBoundary hole.inwardBoundary_simple

open Purelib.RootIsolation in
/-- Every starting vertex on the lifted hole boundary has its coordinate inside the hole box.

The original walk retains the same ordered coordinates and sheet transports.
Structural list certificates preserve their displayed reversal, concatenation
and membership witnesses without changing the retained vertices. -/
theorem liftedBoundary_start_inside (hole : BranchHole bank)
  (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid)
    (edges : SquareRoot.Grid.RootEdgeBank frames) {vertex : Fin vertices.count}
    (member : vertex ∈ (hole.liftedBoundary vertices edges).map OrientedEdge.start) :
    hole.cell.box.Contains (vertices.coordinate vertex) := by
  rw [hole.liftedBoundary_eq, Map.map_append] at member
  have inside : vertices.coordinate vertex ∈ hole.inwardBoundary.startCoordinates :=
    (Membership.mem_append.mp member).elim (edges.indexedStart_coordinate_mem vertices hole.inwardBoundary 0)
      (edges.indexedStart_coordinate_mem vertices hole.inwardBoundary 1)
  rw [hole.inwardBoundary_starts] at inside
  rcases Membership.mem_cons.mp inside with same | inside
  · rw [same]; exact hole.cell.box.contains_anchor
  · rcases Membership.mem_cons.mp inside with same | inside
    · rw [same]; exact ⟨le_rfl, hole.cell.box.x_valid, hole.cell.box.y_valid, le_rfl⟩
    · rcases Membership.mem_cons.mp inside with same | inside
      · rw [same]; exact ⟨hole.cell.box.x_valid, le_rfl, hole.cell.box.y_valid, le_rfl⟩
      · rw [Membership.mem_singleton.mp inside]
        exact ⟨hole.cell.box.x_valid, le_rfl, le_rfl, hole.cell.box.y_valid⟩

end Purelib.Riemann.Meshes.PuncturedGridFaces.BranchHole

end
