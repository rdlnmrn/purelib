module
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Riemann.RootContinuation.NewtonSelectedSideGeometry
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Polynomial.Dense.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-! Hole-adjacent regular sides omitted by annular selection lie on the
original band's boundary, even when the hole touches that boundary. -/
section
open Purelib.Geometry.Rational (Box)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry (SideBoundary)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision AnnularEntry)
open Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters.AllHoleExcision (fineMask)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Rational in
open Purelib.Geometry.Rectangle.Partition in
/-- A matched neighboring rectangle side lies on the same original band boundary with reversed endpoints. -/
theorem matched {first next
  band : Box} {side : GridSide}
    (boundary : Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary first band side) (matching : side.Matches first
      next) :
    Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary next band side.opposite := by
  cases side <;>
    simp only [-eq_self, -iff_self, Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary, GridSide.opposite,
      GridSide.kind,
      RectangularEdgeUniqueness.RectangleEdge.coordinates] at boundary ⊢ <;>
    simp only [-eq_self, -iff_self, GridSide.Matches] at matching <;>
    rcases matching with ⟨a, b, c⟩ <;>
    simp only [-eq_self, -iff_self, ← a, ← b, ← c] <;>
    exact ⟨boundary.2.1, boundary.1, boundary.2.2.reverse⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary

section
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {lifted : LiftedPuncturedGrid grid.punctured}

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision

open Purelib.Curves.Hyperelliptic in
/-- Retain the original annular entry at the exact classified hole index.

The original excision's hole-list equation transports the bounded index and certifies both entry membership and exact
hole identity. -/
@[expose] def entryForHole
    (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (hole : Fin grid.faces.holes.length) :
    {entry : Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted // entry ∈ excision.entries ∧
      entry.hole = (grid.faces.holes[hole.val]'hole.isLt)} := by
  have length : excision.entries.length = grid.faces.holes.length := by
    simpa only [-eq_self, -iff_self, Purelib.Data.List.Map.length_map] using congrArg List.length excision.holes_eq
  have bound : hole.val < excision.entries.length := hole.isLt.trans_le length.ge
  refine ⟨excision.entries[hole.val]'bound, List.getElem_mem bound, ?_⟩
  have equal := List.getElem_of_eq excision.holes_eq (i := hole.val) (by
    simpa only [-eq_self, -iff_self, Purelib.Data.List.Map.length_map] using bound)
  have mappedBound : hole.val < (excision.entries.map AnnularEntry.hole).length := by
    rw [Purelib.Data.List.Map.length_map]
    exact bound
  exact (Purelib.Data.List.Map.getElem_map AnnularEntry.hole excision.entries hole.val bound mappedBound).symm.trans
    equal

end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision

namespace Purelib.Riemann.RootContinuation.NewtonOmittedHoleGeometry.BranchCellBank.NewtonGrid.AllHoleExcision

/-- A retained list member accepted by the predicate makes the original finite any-test true. -/
private theorem any_kept {Item : Type} (keep : Item → Bool) (entries : List Item)
    (entry : Item) (member : entry ∈ entries) (kept : keep entry = true) : entries.any keep = true := by
  induction entries with
  | nil => cases member
  | cons head tail ih =>
    rcases Purelib.Data.List.Membership.mem_cons.mp member with equal | member
    · subst entry
      change (keep head || tail.any keep) = true
      rw [kept]
      rfl
    · change (keep head || tail.any keep) = true
      rw [ih member]
      exact Bool.or_true _

end Purelib.Riemann.RootContinuation.NewtonOmittedHoleGeometry.BranchCellBank.NewtonGrid.AllHoleExcision

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision

open Purelib.Curves.Hyperelliptic in
/-- An omitted regular side adjacent to an original hole lies on that hole's retained band boundary.

The exact excision entry and neighbor match identify the original hole, while the retained band-line geometry turns
discarded selection into a boundary certificate. -/
theorem omittedHole_boundary
    (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
    (position : Fin grid.faces.regulars.length) (hole : Fin grid.faces.holes.length) (side : GridSide)
    (matching : side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
      (grid.faces.holes[hole.val]'hole.isLt).cell.box)
    (discarded : fineMask excision position = false) :
    Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary (grid.faces.regulars[position.val]'position.isLt).cell.box
      (grid.bands.box (excision.entryForHole hole).val.hole.index) side := by
  let found := excision.entryForHole hole
  have outside : ¬(grid.faces.regulars[position.val]'position.isLt).cell.box.Refines
      (grid.bands.box found.val.hole.index) := by
    intro inside
    have kept := Riemann.RootContinuation.NewtonOmittedHoleGeometry.BranchCellBank.NewtonGrid.AllHoleExcision.any_kept
      (fun entry : Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted =>
      entry.keep (grid.faces.regulars[position.val]'position.isLt)) excision.entries found.val
      found.property.1 (decide_eq_true inside)
    exact Bool.noConfusion (discarded.symm.trans kept)
  have inside := grid.hole_refines_band (grid.faces.holes[hole.val]'hole.isLt)
  rw [← found.property.2] at inside
  have matched : side.opposite.Matches found.val.hole.cell.box
      (grid.faces.regulars[position.val]'position.isLt).cell.box := by
    rw [found.property.2]
    exact matching.reverse
  have boundary := grid.selected_interface_boundary found.val.hole.index found.val.hole.cell
    (grid.faces.regulars[position.val]'position.isLt).cell
    (grid.faces.regulars[position.val]'position.isLt).member side.opposite matched inside outside
  have result := boundary.matched matched
  cases side <;> exact result

end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision

end
end
