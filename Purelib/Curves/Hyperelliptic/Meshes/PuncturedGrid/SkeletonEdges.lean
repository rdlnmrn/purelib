module
public import Purelib.Data.List.Cartesian
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Pairwise
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
public import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryCounts
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.RootIsolation.SquareRoot.Grid.EdgeCoherence
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Init.Data.List.OfFn
import Init.GetElem
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
meta import Mathlib.Tactic.Linter.Lint
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Duplicate-free enumeration of the actual lifted grid skeleton

Enumerate both sheets of every positive horizontal and vertical grid edge.
Endpoint coordinates and the retained source sheet prove uniqueness. These
are the actual cached root transports, not edges in a replacement sheet
model. Every enumerated edge belongs to the retained mesh up to reversal.
-/

section

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Data.Gaussian

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Riemann.Meshes

open Purelib.Riemann.Paths

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Interval)
open Purelib.Polynomial.Geometry.Grid.ClearGrid.Interval
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryCounts (nodup_ofFn_injective)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Interval VerticalLine HorizontalLine)
open Purelib.Polynomial.Geometry.Grid.Walks (Edge)
open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk Lookup)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges

/-- Enumerate each original grid-index pair on both retained sheets.

The nested Cartesian products preserve the index order and the original
two-sheet enumeration without reconstructing any root transport. -/
@[expose] def slots (first last : Nat) : List ((Fin first × Fin last) × Fin 2) :=
  Cartesian.productList (Cartesian.productList (List.ofFn (fun index : Fin first => index)) (List.ofFn (fun index : Fin
    last => index)))
    (List.ofFn (fun sheet : Fin 2 => sheet))

/-- Every original grid-index pair and sheet occurs in the finite slot enumeration. -/
theorem slots_mem {first last : Nat} (slot : (Fin first × Fin last) × Fin 2) : slot ∈
  slots first last :=
  Cartesian.productList_mem.mpr ⟨Cartesian.productList_mem.mpr ⟨OfFn.Basic.mem_ofFn.mpr ⟨_, rfl⟩,
    OfFn.Basic.mem_ofFn.mpr ⟨_, rfl⟩⟩,
    OfFn.Basic.mem_ofFn.mpr ⟨_, rfl⟩⟩

/-- The slot enumeration has twice the product of the two original finite index counts. -/
theorem slots_length (first last : Nat) : (slots first
  last).length = 2 * (first * last) := by
  rw [slots, Cartesian.productList_length,
    Cartesian.productList_length, OfFn.Basic.length_ofFn,
    OfFn.Basic.length_ofFn, OfFn.Basic.length_ofFn, Nat.mul_comm]

/-- The original grid-index and sheet slot enumeration has no repeated entry. -/
theorem slots_nodup (first last : Nat) : (slots first
  last).Nodup :=
  Cartesian.productList_nodup _ _ (Cartesian.productList_nodup _ _ (BoundaryCounts.nodup_ofFn_injective _ (fun _ _ same
    => same))
    (BoundaryCounts.nodup_ofFn_injective _ (fun _ _ same => same))) (BoundaryCounts.nodup_ofFn_injective _ (fun _ _ same
      => same))

/-- Equal keys in a strictly ordered original finite list identify their exact retained indices. -/
private theorem key_index_injective {Alpha : Type} {key : Alpha → Fraction.Rational} (entries : List Alpha)
    (ordered : entries.Pairwise (fun first last => key first < key last))
    {first last : Fin entries.length} (same : key entries[first.val] = key entries[last.val]) : first = last := by
  apply Fin.ext
  rcases Nat.lt_trichotomy first.val last.val with before | equal | after
  · exact (ne_of_lt (Pairwise.pairwise_getElem ordered _ _ first.isLt last.isLt before) same).elim
  · exact equal
  · exact (ne_of_lt (Pairwise.pairwise_getElem ordered _ _ last.isLt first.isLt after) same.symm).elim

/-- The lower endpoints of the original adjacent intervals remain strictly ordered. -/
private theorem adjacent_lower_ordered {Alpha : Type} {key : Alpha → Fraction.Rational} (entries : List Alpha)
    (ordered : entries.Pairwise (fun first last => key first < key last)) :
    (Interval.adjacent entries ordered).Pairwise (fun first last => key first.lower < key last.lower) :=
  List.Pairwise.imp (fun {first _} before => first.ordered.trans_le before) (Interval.adjacent_pairwise entries ordered)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges

/-- The original horizontal interval, horizontal line and retained source sheet selecting one lifted horizontal edge. -/
abbrev HorizontalSlot (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) := (Fin grid.xIntervals.length ×
  Fin
  grid.horizontal.length) × Fin 2
/-- The original vertical interval, vertical line and retained source sheet selecting one lifted vertical edge. -/
abbrev VerticalSlot (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) := (Fin grid.yIntervals.length × Fin
  grid.vertical.length) × Fin 2

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

/-- Read the actual retained root transport edge selected by the original horizontal interval, line and sheet. -/
@[expose] def horizontalEdge (edges :
  RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid) (slot :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.HorizontalSlot grid) :
    Stokes.OrientedEdge vertices.count :=
  edges.indexedEdge vertices (.horizontal grid.xIntervals[slot.1.1.val] (List.getElem_mem _)
    grid.horizontal[slot.1.2.val] (List.getElem_mem _)) slot.2

/-- Read the actual retained root transport edge selected by the original vertical interval, line and sheet. -/
@[expose] def verticalEdge (edges :
  RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid) (slot :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.VerticalSlot grid) :
    Stokes.OrientedEdge vertices.count :=
  edges.indexedEdge vertices (.vertical grid.yIntervals[slot.1.1.val] (List.getElem_mem _)
    grid.vertical[slot.1.2.val] (List.getElem_mem _)) slot.2

/-- The retained horizontal edge endpoints have the exact original grid coordinates. -/
theorem horizontalEdge_coordinates (edges :
  RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid) (slot :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.HorizontalSlot grid) :
    vertices.coordinate (edges.horizontalEdge vertices slot).start =
        Components.Basic.point grid.xIntervals[slot.1.1.val].lower.coordinate grid.horizontal[slot.1.2.val].coordinate ∧
      vertices.coordinate (edges.horizontalEdge vertices slot).finish =
        Components.Basic.point grid.xIntervals[slot.1.1.val].upper.coordinate grid.horizontal[slot.1.2.val].coordinate
          := by
  constructor <;>
    simp only [horizontalEdge, RootEdgeBank.indexedEdge,
      vertices.coordinate_index, -eq_self, -iff_self] <;> rfl

/-- The retained vertical edge endpoints have the exact original grid coordinates. -/
theorem verticalEdge_coordinates (edges :
  RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid) (slot :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.VerticalSlot grid) :
    vertices.coordinate (edges.verticalEdge vertices slot).start =
        Components.Basic.point grid.vertical[slot.1.2.val].coordinate grid.yIntervals[slot.1.1.val].lower.coordinate ∧
      vertices.coordinate (edges.verticalEdge vertices slot).finish =
        Components.Basic.point grid.vertical[slot.1.2.val].coordinate grid.yIntervals[slot.1.1.val].upper.coordinate :=
          by
  constructor <;>
    simp only [verticalEdge, RootEdgeBank.indexedEdge,
      vertices.coordinate_index, -eq_self, -iff_self] <;> rfl

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

section

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

/-- The actual lifted horizontal edge determines its original interval, line and source sheet. -/
theorem horizontalEdge_injective (edges :
  RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid) :
    Function.Injective (edges.horizontalEdge vertices) := by
  intro first last same
  have points := (edges.horizontalEdge_coordinates vertices first).1.symm.trans
    ((congrArg (fun edge => vertices.coordinate edge.start) same).trans (edges.horizontalEdge_coordinates vertices
      last).1)
  have intervals := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.key_index_injective grid.xIntervals
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.adjacent_lower_ordered _ grid.vertical_ordered)
    (congrArg Data.Gaussian.Basic.re points)
  have lines := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.key_index_injective grid.horizontal
    grid.horizontal_ordered
    (congrArg Data.Gaussian.Basic.im points)
  have sheets := congrArg (fun edge => vertices.sheet edge.start) same
  simp only [horizontalEdge, RootEdgeBank.indexedEdge,
    vertices.sheet_index] at sheets
  exact Prod.ext (Prod.ext intervals lines) sheets

/-- The actual lifted vertical edge determines its original interval, line and source sheet. -/
theorem verticalEdge_injective (edges :
  RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid) :
    Function.Injective (edges.verticalEdge vertices) := by
  intro first last same
  have points := (edges.verticalEdge_coordinates vertices first).1.symm.trans
    ((congrArg (fun edge => vertices.coordinate edge.start) same).trans (edges.verticalEdge_coordinates vertices
      last).1)
  have intervals := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.key_index_injective grid.yIntervals
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.adjacent_lower_ordered _ grid.horizontal_ordered)
    (congrArg Data.Gaussian.Basic.im points)
  have lines := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.key_index_injective grid.vertical
    grid.vertical_ordered
    (congrArg Data.Gaussian.Basic.re points)
  have sheets := congrArg (fun edge => vertices.sheet edge.start) same
  simp only [verticalEdge, RootEdgeBank.indexedEdge,
    vertices.sheet_index] at sheets
  exact Prod.ext (Prod.ext intervals lines) sheets

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

end

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges

open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank in
/-- Positive coordinate direction is independent of the arbitrary cache's integer ordering and is incompatible with the
reverse of another such edge. -/
@[expose] def PositiveAxis (vertices : LiftedVertices.VertexBank grid) (edge : Stokes.OrientedEdge vertices.count) :
  Prop :=
  ((vertices.coordinate edge.start).re < (vertices.coordinate edge.finish).re ∧
    (vertices.coordinate edge.start).im = (vertices.coordinate edge.finish).im) ∨
  ((vertices.coordinate edge.start).re = (vertices.coordinate edge.finish).re ∧
    (vertices.coordinate edge.start).im < (vertices.coordinate edge.finish).im)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

/-- Every enumerated horizontal lifted edge points in the original positive coordinate direction. -/
theorem horizontalEdge_positive (edges :
  RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid) (slot :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.HorizontalSlot grid) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.PositiveAxis vertices (edges.horizontalEdge vertices
      slot) := by
  unfold Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.PositiveAxis
  rw [(edges.horizontalEdge_coordinates vertices slot).1, (edges.horizontalEdge_coordinates vertices slot).2]
  exact Or.inl ⟨grid.xIntervals[slot.1.1.val].ordered, rfl⟩

/-- Every enumerated vertical lifted edge points in the original positive coordinate direction. -/
theorem verticalEdge_positive (edges :
  RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid) (slot :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.VerticalSlot grid) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.PositiveAxis vertices (edges.verticalEdge vertices
      slot) := by
  unfold Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.PositiveAxis
  rw [(edges.verticalEdge_coordinates vertices slot).1, (edges.verticalEdge_coordinates vertices slot).2]
  exact Or.inr ⟨rfl, grid.yIntervals[slot.1.1.val].ordered⟩

/-- Enumerate both sheets of every original positive horizontal and vertical grid edge.

Each occurrence uses the cached root transport and vertex bank of the original grid. -/
@[expose] def skeleton (edges :
  RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid) : List (Stokes.OrientedEdge
  vertices.count) :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.slots grid.xIntervals.length grid.horizontal.length).map
    (edges.horizontalEdge vertices) ++
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.slots grid.yIntervals.length grid.vertical.length).map
      (edges.verticalEdge vertices)

/-- The retained skeleton count is twice the sum of the original horizontal and vertical grid-edge counts. -/
theorem skeleton_length (edges :
  RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid) :
    (edges.skeleton vertices).length =
      2 * (grid.xIntervals.length * grid.horizontal.length + grid.yIntervals.length * grid.vertical.length) := by
  rw [skeleton, Append.length_append, Map.length_map,
    Map.length_map, Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.slots_length,
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.slots_length, Nat.mul_add]

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

section

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

/-- A retained skeleton edge is exactly a horizontal or vertical original slot occurrence. -/
theorem skeleton_mem (edges :
  RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid) (edge : Stokes.OrientedEdge
  vertices.count) :
    edge ∈ edges.skeleton vertices ↔
      (∃ slot, edges.horizontalEdge vertices slot = edge) ∨ (∃ slot, edges.verticalEdge vertices slot = edge) := by
  constructor
  · intro member
    rcases Membership.mem_append.mp member with member | member
    · obtain ⟨slot, _, equal⟩ := Map.mem_map.mp member
      exact Or.inl ⟨slot, equal⟩
    · obtain ⟨slot, _, equal⟩ := Map.mem_map.mp member
      exact Or.inr ⟨slot, equal⟩
  · intro member
    rcases member with ⟨slot, equal⟩ | ⟨slot, equal⟩
    · exact Membership.mem_append.mpr (Or.inl (Map.mem_map.mpr ⟨slot,
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.slots_mem slot, equal⟩))
    · exact Membership.mem_append.mpr (Or.inr (Map.mem_map.mpr ⟨slot,
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.slots_mem slot, equal⟩))

/-- Every retained skeleton edge points in one positive original coordinate direction. -/
theorem skeleton_positive (edges :
  RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid)
    {edge : Stokes.OrientedEdge vertices.count} (member : edge ∈ edges.skeleton vertices) :
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.PositiveAxis vertices edge := by
  rcases (edges.skeleton_mem vertices edge).mp member with ⟨slot, rfl⟩ | ⟨slot, rfl⟩
  · exact edges.horizontalEdge_positive vertices slot
  · exact edges.verticalEdge_positive vertices slot

/-- The actual lifted grid skeleton enumeration contains no repeated oriented edge. -/
theorem skeleton_nodup (edges :
  RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid) : (edges.skeleton vertices).Nodup := by
  refine Nodup.nodup_append
    (Data.List.Nodup.nodup_map_of_injective (edges.horizontalEdge_injective vertices)
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.slots_nodup _ _))
    (Data.List.Nodup.nodup_map_of_injective (edges.verticalEdge_injective vertices)
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonEdges.slots_nodup _ _)) ?_
  intro first firstMember last lastMember same
  obtain ⟨firstSlot, _, firstEq⟩ := Map.mem_map.mp firstMember
  obtain ⟨lastSlot, _, lastEq⟩ := Map.mem_map.mp lastMember
  have x := congrArg (fun edge => ((vertices.coordinate edge.start).re, (vertices.coordinate edge.finish).re))
    (firstEq.trans (same.trans lastEq.symm))
  rw [(edges.horizontalEdge_coordinates vertices firstSlot).1, (edges.horizontalEdge_coordinates vertices firstSlot).2,
    (edges.verticalEdge_coordinates vertices lastSlot).1, (edges.verticalEdge_coordinates vertices lastSlot).2] at x
  exact ne_of_lt grid.xIntervals[firstSlot.1.1.val].ordered ((congrArg Prod.fst x).trans (congrArg Prod.snd x).symm)

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

end

section
open Purelib.Polynomial.Geometry.Grid.ClearGrid.Interval

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

/-- Every original positive horizontal grid edge on either retained sheet occurs in the skeleton. -/
theorem horizontal_mem_skeleton (edges :
  RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid)
    (interval : ClearGrid.Interval (VerticalLine.coordinate (polynomial := polynomial) (ambient := ambient)))
    (adjacent : interval ∈ grid.xIntervals) (line : ClearGrid.HorizontalLine polynomial ambient) (member : line ∈
      grid.horizontal)
    (sheet : Fin 2) : edges.indexedEdge vertices (.horizontal interval adjacent line member) sheet ∈ edges.skeleton
      vertices := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp adjacent
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp member
  exact (edges.skeleton_mem vertices _).mpr (Or.inl ⟨((⟨i, hi⟩, ⟨j, hj⟩), sheet), rfl⟩)

/-- Every original positive vertical grid edge on either retained sheet occurs in the skeleton. -/
theorem vertical_mem_skeleton (edges :
  RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid)
    (interval : ClearGrid.Interval (HorizontalLine.coordinate (polynomial := polynomial) (ambient := ambient)))
    (adjacent : interval ∈ grid.yIntervals) (line : ClearGrid.VerticalLine polynomial ambient) (member : line ∈
      grid.vertical)
    (sheet : Fin 2) : edges.indexedEdge vertices (.vertical interval adjacent line member) sheet ∈ edges.skeleton
      vertices := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp adjacent
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp member
  exact (edges.skeleton_mem vertices _).mpr (Or.inr ⟨((⟨i, hi⟩, ⟨j, hj⟩), sheet), rfl⟩)

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

end

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

/-- Arbitrary reversals select the appropriate source sheet using the proved inverse of the same retained root-edge
transport. -/
theorem indexedEdge_skeleton (edges :
  RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      OwnerLoopMonodromy.WindingOneLoop polynomial point) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} (edge : Walks.Edge grid start finish) (sheet : Fin 2),
      edges.indexedEdge vertices edge sheet ∈ edges.skeleton vertices ∨
        (edges.indexedEdge vertices edge sheet).reverse ∈ edges.skeleton vertices
  | _, _, .horizontal interval adjacent line member, sheet =>
      Or.inl (edges.horizontal_mem_skeleton vertices interval adjacent line member sheet)
  | _, _, .vertical interval adjacent line member, sheet =>
      Or.inl (edges.vertical_mem_skeleton vertices interval adjacent line member sheet)
  | _, _, .reverse original, sheet => by
      let connection := edges.edge original
      have reversed := edges.indexedEdge_reverse vertices original (reference _ original.vertices.1)
        (reference _ original.vertices.2) (connection.backward.target sheet)
      have returned : connection.forward.target (connection.backward.target sheet) = sheet :=
        (connection.bijection (reference _ original.vertices.1) (reference _ original.vertices.2)).forward_backward
          sheet
      rw [returned] at reversed
      rw [reversed, OrientedEdge.reverse_reverse]
      exact (edges.indexedEdge_skeleton vertices reference original (connection.backward.target sheet)).symm

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

namespace Purelib.Curves.Hyperelliptic.Branches.BranchCellBank.LiftedMesh

open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank in
/-- Every retained skeleton edge belongs to an original lifted triangle, up to reversal. -/
theorem skeleton_supported (mesh :
  GridLiftedMesh.LiftedMesh vertices edges base.faces) {edge : Stokes.OrientedEdge vertices.count}
    (member : edge ∈ edges.skeleton vertices) :
    edge ∈ Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨
      edge.reverse ∈ Stokes.triangleEdgeOccurrences mesh.triangulation.faces := by
  rcases (edges.skeleton_mem vertices edge).mp member with ⟨slot, rfl⟩ | ⟨slot, rfl⟩
  · exact SkeletonFaceAssignments.indexedEdge_supported mesh _ _
  · exact SkeletonFaceAssignments.indexedEdge_supported mesh _ _

end Purelib.Curves.Hyperelliptic.Branches.BranchCellBank.LiftedMesh

end
