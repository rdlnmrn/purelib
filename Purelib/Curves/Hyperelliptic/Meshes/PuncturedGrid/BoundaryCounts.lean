module
import Purelib.Data.List.Flatten
import Purelib.Data.List.Append
import Purelib.Data.List.OfFn.Nodup
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Pairwise
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Polynomial.Geometry.Grid.WindowSize
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint

/-!
# Exact counts on the retained punctured cover

Every isolated branch occurs exactly once in the retained hole list. Count
the actual closed lifted boundary tours and their edge occurrences, as well
as the actual triangles and sewn cut perimeter. These are counts of the
constructed data, not a replacement abstract cell model. Identifying the
normal-form handle count still requires the vertex and incidence argument.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryCounts
public section
open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Data.List
open Purelib.Polynomial.Geometry.Grid.FramedClearGrid
open Purelib.Polynomial.Geometry.Grid.FramedClearGrid
open Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame
open Purelib.Polynomial.Geometry.Grid.WindowSize
open Purelib.Polynomial.Geometry.Grid.WindowSize
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.PuncturedGridFaces
open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
open _root_.Purelib.RootIsolation.SquareRoot.Grid renaming RootEdgeBank -> RootEdgeBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole PuncturedFaces)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)

/-- An injective finite-indexed enumeration has no repeated list entries.

Injectivity distinguishes every original finite index. The ordered table
therefore contains no repeated entries. -/
theorem nodup_ofFn_injective {Alpha : Type u} {size : Nat}
    (value : Fin size → Alpha) (injective : Function.Injective value) : (List.ofFn value).Nodup :=
  OfFn.Nodup.nodup_ofFn_of_injective injective

end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryCounts

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces
public section
open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Data.List
open Purelib.Polynomial.Geometry.Grid.FramedClearGrid
open Purelib.Polynomial.Geometry.Grid.FramedClearGrid
open Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame
open Purelib.Polynomial.Geometry.Grid.WindowSize
open Purelib.Polynomial.Geometry.Grid.WindowSize
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.PuncturedGridFaces
open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
open _root_.Purelib.RootIsolation.SquareRoot.Grid renaming RootEdgeBank -> RootEdgeBank

variable {genus : Nat}
  {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {branches : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher}

/-- Completeness and pairwise branch separation count the actual hole list; the producer's list order and choice of
checked grid are immaterial.

The count follows the retained finite enumeration and ordered boundary fibers. No edge occurrence or original branch
index is replaced or omitted. -/
theorem holes_length (faces : PuncturedGridFaces.PuncturedFaces bank) :
    faces.holes.length = branches.siteCount := by
  let indices := faces.holes.map BranchHole.index
  let all := List.ofFn (fun index : BranchIsolation.Data.Index branches => index)
  have unique : indices.Nodup := Pairwise.pairwise_map.mpr faces.holes_pairwise
  have allUnique : all.Nodup := Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryCounts.nodup_ofFn_injective _ (fun _ _
    same => same)
  have forward : ∀ index ∈ indices, index ∈ all := fun index _ => OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩
  have backward : ∀ index ∈ all, index ∈ indices := by
    intro index _
    obtain ⟨hole, member, equal⟩ := faces.hole_complete index
    exact Map.mem_map.mpr ⟨hole, member, equal⟩
  have same := Nat.le_antisymm (Nodup.nodup_length_le_of_mem unique allUnique forward)
    (Nodup.nodup_length_le_of_mem allUnique unique backward)
  change (faces.holes.map BranchHole.index).length = all.length at same
  rw [Map.length_map, OfFn.Basic.length_ofFn] at same
  exact same

/-- The retained branch-hole count equals the original curve polynomial degree. -/
theorem holes_degree (faces : PuncturedGridFaces.PuncturedFaces bank) :
    faces.holes.length = curve.polynomial.natDegree :=
  faces.holes_length.trans branches.count_eq

/-- The retained regular-face count plus the polynomial degree is the original grid-cell count. -/
theorem regulars_degree (faces : PuncturedGridFaces.PuncturedFaces bank) :
    faces.regulars.length + curve.polynomial.natDegree = bank.grid.cells.length := by
  rw [← faces.holes_degree]
  exact faces.length_eq

end
end Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces

namespace Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame
public section
open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Data.List
open Purelib.Polynomial.Geometry.Grid.FramedClearGrid
open Purelib.Polynomial.Geometry.Grid.FramedClearGrid
open Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame
open Purelib.Polynomial.Geometry.Grid.WindowSize
open Purelib.Polynomial.Geometry.Grid.WindowSize
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.PuncturedGridFaces
open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
open _root_.Purelib.RootIsolation.SquareRoot.Grid renaming RootEdgeBank -> RootEdgeBank

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial}
  {ambient : Geometry.Rational.Box}
  {grid : ClearGrid polynomial ambient}

open _root_.Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame (Axes)
open _root_.Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame.Axes (horizontal vertical)
open _root_.Purelib.Polynomial.Geometry.Grid.WindowSize.Walk
  (append_edgeCount reverse_edgeCount castEndpoints_edgeCount horizontalIncreasing_edgeCount
    verticalIncreasing_edgeCount)

/-- The framed grid perimeter has twice the sum of the original horizontal and vertical interval counts. -/
theorem boundary_edgeCount (frame : AmbientFrame grid) :
    frame.boundary.edgeCount = 2 * (grid.xIntervals.length + grid.yIntervals.length) := by
  simp only [AmbientFrame.boundary,
    WindowSize.Walk.append_edgeCount,
    WindowSize.Walk.reverse_edgeCount,
    Axes.horizontal,
    Axes.vertical,
    WindowSize.Walk.castEndpoints_edgeCount,
    WindowSize.Walk.horizontalIncreasing_edgeCount,
    WindowSize.Walk.verticalIncreasing_edgeCount,
    (frame.axes).x_edges, (frame.axes).y_edges]
  omega

end
end Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid
public section
open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Data.List
open Purelib.Polynomial.Geometry.Grid.FramedClearGrid
open Purelib.Polynomial.Geometry.Grid.FramedClearGrid
open Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame
open Purelib.Polynomial.Geometry.Grid.WindowSize
open Purelib.Polynomial.Geometry.Grid.WindowSize
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.PuncturedGridFaces
open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
open _root_.Purelib.RootIsolation.SquareRoot.Grid renaming RootEdgeBank -> RootEdgeBank

variable {genus : Nat}
  {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {branches : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}

/-- The actual lifted boundary-loop count equals the branch degree plus the parity-dependent exterior-loop count. -/
theorem boundaryLoops_count (lifted : LiftedPuncturedGrid base) :
    lifted.boundaryLoops.length = curve.polynomial.natDegree +
      (match curve.degreeShape with | .odd _ => 1 | .even _ => 2) := by
  rw [lifted.boundaryLoops_length, base.faces.holes_degree]
  rfl

/-- An odd-degree genus-g curve has exactly 2g+2 retained lifted boundary loops. -/
theorem boundaryLoops_count_odd (lifted : LiftedPuncturedGrid base)
    (degree : curve.polynomial.natDegree = 2 * genus + 1) :
    lifted.boundaryLoops.length = 2 * genus + 2 := by
  rw [lifted.boundaryLoops_count]
  cases curve.degreeShape with
  | odd _ => simp only; omega
  | even opposite => omega

/-- An even-degree genus-g curve has exactly 2g+4 retained lifted boundary loops. -/
theorem boundaryLoops_count_even (lifted : LiftedPuncturedGrid base)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    lifted.boundaryLoops.length = 2 * genus + 4 := by
  rw [lifted.boundaryLoops_count]
  cases curve.degreeShape with
  | odd opposite => omega
  | even _ => simp only; omega

/-- The actual lifted exterior boundary occurrences total twice the original exterior edge count.

The count follows the retained finite enumeration and ordered boundary fibers. No edge occurrence or original branch
index is replaced or omitted. -/
theorem exteriorBoundaries_edgeCount (lifted : LiftedPuncturedGrid base) :
    lifted.exteriorBoundaries.flatten.length = 2 * base.bank.exterior.edgeCount := by
  cases shape : curve.degreeShape <;>
    simp only [exteriorBoundaries, shape, List.flatten_cons, List.flatten_nil, Append.length_append,
      List.length_nil, RootEdgeBank.indexedEdges_length,
      Polynomial.Geometry.Grid.WindowSize.Walk.append_edgeCount] <;> omega

/-- Each original branch-hole boundary contributes eight retained lifted edge occurrences.

The count follows the retained finite enumeration and ordered boundary fibers. No edge occurrence or original branch
index is replaced or omitted. -/
private theorem hole_edges_length (lifted : LiftedPuncturedGrid base) :
    (holes : List (PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)) →
    (holes.flatMap (fun hole => hole.liftedBoundary lifted.vertices lifted.edges)).length = 8 * holes.length
  | [] => rfl
  | hole :: holes => by
      rw [Flatten.flatMap_cons, Append.length_append, hole.liftedBoundary_length, hole_edges_length lifted holes]
      simp only [List.length_cons]
      omega

/-- Counts the actual two laps at each branch hole and both sheets of the entire subdivided exterior, regardless of its
one/two-loop decomposition.

The count follows the retained finite enumeration and ordered boundary fibers. No edge occurrence or original branch
index is replaced or omitted. -/
theorem boundaryLoops_edgeCount (lifted : LiftedPuncturedGrid base) :
    lifted.boundaryLoops.flatten.length = 2 * base.bank.exterior.edgeCount + 8 * curve.polynomial.natDegree := by
  rw [boundaryLoops, Flatten.flatten_append, Append.length_append, lifted.exteriorBoundaries_edgeCount]
  change _ + (base.faces.holes.flatMap (fun hole => hole.liftedBoundary lifted.vertices lifted.edges)).length = _
  rw [hole_edges_length, base.faces.holes_degree]

/-- The retained lifted triangles and omitted branch cells account for all original grid cells. -/
theorem triangle_count_balance (lifted : LiftedPuncturedGrid base) :
    lifted.mesh.triangles.length + 4 * curve.polynomial.natDegree =
      4 * (base.bank.grid.xIntervals.length * base.bank.grid.yIntervals.length) := by
  have cells := base.faces.regulars_degree
  rw [Polynomial.Geometry.Grid.WindowSize.cells_length base.bank.grid] at cells
  rw [lifted.faceCount]
  omega

/-- The canonical cut perimeter has four edges per original regular face plus two sewing endpoints. -/
theorem cut_boundary_count (lifted : LiftedPuncturedGrid base) :
    lifted.cutPolygon.patch.cut.boundary.length = 4 * base.faces.regulars.length + 2 := by
  rw [lifted.cutPolygon.boundaryCount, lifted.faceCount]

end
end Purelib.Riemann.Meshes.LiftedPuncturedGrid
