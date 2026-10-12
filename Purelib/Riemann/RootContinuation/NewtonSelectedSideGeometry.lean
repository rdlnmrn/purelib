module
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Data.List.Membership

public section

/-! Selected/unselected interfaces lie on the retained Newton-band boundary.
Only containment is needed for the grid hole; no strict gap is assumed. -/
section

open Purelib.Data.List
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry (SideBoundary)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell Interval)
open Purelib.Polynomial.Geometry.Grid.Incidence.Interval (coordinate_side)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision AnnularEntry)

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary

open Purelib.Curves in
open Purelib.Geometry in
/-- A contained rectangle side on the band's matching coordinate lies on that band side.

The certificate retains both original endpoints and their orientation. -/
theorem of_exterior {face
  band : Rational.Box} {side : GridSide} (inside : face.Refines band)
    (exterior : side.Exterior face band) : Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary face
      band side := by
  have x := face.x_valid
  have y := face.y_valid
  cases side with
  | bottom =>
    exact ⟨⟨inside.1, x.trans inside.2.1, inside.2.2.1, y.trans inside.2.2.2⟩,
      ⟨inside.1.trans x, inside.2.1, inside.2.2.1, y.trans inside.2.2.2⟩,
      Or.inr (Or.inr (Or.inl ⟨exterior, exterior⟩))⟩
  | right =>
    exact ⟨⟨inside.1.trans x, inside.2.1, inside.2.2.1, y.trans inside.2.2.2⟩,
      ⟨inside.1.trans x, inside.2.1, inside.2.2.1.trans y, inside.2.2.2⟩,
      Or.inr (Or.inl ⟨exterior, exterior⟩)⟩
  | top =>
    exact ⟨⟨inside.1.trans x, inside.2.1, inside.2.2.1.trans y, inside.2.2.2⟩,
      ⟨inside.1, x.trans inside.2.1, inside.2.2.1.trans y, inside.2.2.2⟩,
      Or.inr (Or.inr (Or.inr ⟨exterior, exterior⟩))⟩
  | left =>
    exact ⟨⟨inside.1, x.trans inside.2.1, inside.2.2.1.trans y, inside.2.2.2⟩,
      ⟨inside.1, x.trans inside.2.1, inside.2.2.1, y.trans inside.2.2.2⟩,
      Or.inl ⟨exterior, exterior⟩⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary

end

section
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {index :
    Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}

namespace Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid

open Purelib.Polynomial.Geometry.Grid.Incidence.Interval in
open Purelib.Curves in
open Purelib.Polynomial in
/-- A transition from a selected cell to an unselected neighbor lies on the exact band coordinate.

The retained grid lines prevent the neighboring cell from straddling the band boundary. -/
theorem
  selected_interface_exterior
  (grid : NewtonGrid preparation target radius)
    (index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches)
    (first next : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) (nextMember
      : next ∈ grid.punctured.bank.grid.cells)
    (side : GridSide) (matching : side.Matches first.box next.box)
    (inside : first.box.Refines (grid.bands.box index))
    (outside : ¬next.box.Refines (grid.bands.box index)) : side.Exterior first.box (grid.bands.box index) := by
  have intervals := Geometry.Grid.CellBoundary.Cell.intervals_mem next nextMember
  cases side with
  | right =>
    rcases coordinate_side _ grid.punctured.bank.grid.vertical_ordered intervals.1
      (grid.band_x_lines index).2 with before | after
    · exact le_antisymm inside.2.1 (before.trans_eq matching.2.2.symm)
    · exact False.elim (outside ⟨(inside.1.trans first.box.x_valid).trans_eq matching.2.2, after,
        inside.2.2.1.trans_eq matching.1, matching.2.1.symm.trans_le inside.2.2.2⟩)
  | left =>
    rcases coordinate_side _ grid.punctured.bank.grid.vertical_ordered intervals.1
      (grid.band_x_lines index).1 with before | after
    · exact False.elim (outside ⟨before, matching.2.2.symm.trans_le (first.box.x_valid.trans inside.2.1),
        inside.2.2.1.trans_eq matching.1, matching.2.1.symm.trans_le inside.2.2.2⟩)
    · exact le_antisymm (matching.2.2.trans_le after) inside.1
  | top =>
    rcases coordinate_side _ grid.punctured.bank.grid.horizontal_ordered intervals.2
      (grid.band_y_lines index).2 with before | after
    · exact le_antisymm inside.2.2.2 (before.trans_eq matching.2.2.symm)
    · exact False.elim (outside ⟨inside.1.trans_eq matching.1, matching.2.1.symm.trans_le inside.2.1,
        (inside.2.2.1.trans first.box.y_valid).trans_eq matching.2.2, after⟩)
  | bottom =>
    rcases coordinate_side _ grid.punctured.bank.grid.horizontal_ordered intervals.2
      (grid.band_y_lines index).1 with before | after
    · exact False.elim (outside ⟨inside.1.trans_eq matching.1, matching.2.1.symm.trans_le inside.2.1,
        before, matching.2.2.symm.trans_le (first.box.y_valid.trans inside.2.2.2)⟩)
    · exact le_antisymm (matching.2.2.trans_le after) inside.2.2.1

open Purelib.Curves in
open Purelib.Polynomial in
/-- Certify the oriented side boundary of a selected-to-unselected cell transition. -/
theorem
  selected_interface_boundary
  (grid : NewtonGrid preparation target radius)
    (index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches)
    (first next : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) (nextMember
      : next ∈ grid.punctured.bank.grid.cells)
    (side : GridSide) (matching : side.Matches first.box next.box)
    (inside : first.box.Refines (grid.bands.box index))
    (outside : ¬next.box.Refines (grid.bands.box index)) :
      Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary first.box (grid.bands.box index) side :=
  Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary.of_exterior inside
    (grid.selected_interface_exterior index first next nextMember side matching inside outside)

end Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid

namespace Purelib.Riemann.RootContinuation.NewtonSelectedSideGeometry.BranchCellBank.NewtonGrid

/-- Extract a retained satisfying list entry from a successful Boolean search.

Structural recursion returns the original entry together with its membership and predicate certificates. -/
@[expose] def selected_entry {Item : Type} (keep : Item → Bool) :
    (entries : List Item) → entries.any keep = true → {entry : Item // entry ∈ entries ∧ keep entry = true}
  | [], selected => nomatch selected
  | head :: tail, selected =>
    if kept : keep head = true then ⟨head, List.mem_cons_self, kept⟩
    else
      let found := selected_entry keep tail (by
        change (keep head || tail.any keep) = true at selected
        have no := Bool.eq_false_iff.mpr kept
        simpa only [no, Bool.false_or] using selected)
      ⟨found.val, List.mem_cons_of_mem _ found.property.1, found.property.2⟩

/-- A retained satisfying member makes the finite Boolean search succeed.

The displayed occurrence supplies its own successful Boolean test; structural recursion retains that occurrence through
the original finite search. -/
theorem any_of_member {Item : Type} (keep : Item → Bool) (entries : List Item)
    (entry : Item) (member : entry ∈ entries) (kept : keep entry = true) : entries.any keep = true := by
  induction entries with
  | nil => exact (List.not_mem_nil member).elim
  | cons head tail ih =>
    change (keep head || tail.any keep) = true
    rcases Membership.mem_cons.mp member with equal | member
    · rw [← equal, kept]; rfl
    · rw [ih member]
      cases keep head <;> rfl

end Purelib.Riemann.RootContinuation.NewtonSelectedSideGeometry.BranchCellBank.NewtonGrid

section
variable {lifted : LiftedPuncturedGrid grid.punctured}

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Geometry in
/-- Every selected regular face is strictly inside the fixed ambient box.

Its retained Newton band lies strictly inside an original branch cell, and the original cell refines the ambient. -/
theorem selected_strict_ambient
  (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
    (position : Fin grid.faces.regulars.length)
    (selected : RootContinuation.NewtonSelectedPerimeters.AllHoleExcision.fineMask excision position = true) :
    (grid.faces.regulars[position.val]'position.isLt).cell.box.StrictInterior (Hyperelliptic.Branches.Cuts.Ambient
      curve) := by
  let found := Riemann.RootContinuation.NewtonSelectedSideGeometry.BranchCellBank.NewtonGrid.selected_entry (fun entry :
    Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted =>
    entry.keep (grid.faces.regulars[position.val]'position.isLt)) excision.entries selected
  exact Geometry.Rational.Box.Refinement.StrictInterior.of_refines
    (Geometry.Rational.Box.Refinement.StrictInterior.Boxes.trans_refines
      (grid.bands.strict_original found.val.hole.index)
      (original.cell found.val.hole.index).box_refines)
    (of_decide_eq_true found.property.2)

open Purelib.Riemann
open Purelib.Curves
/-- A selected regular face has no side on the ambient exterior boundary. -/
theorem selected_not_exterior
  (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
    (position : Fin grid.faces.regulars.length) (side : GridSide)
    (selected : RootContinuation.NewtonSelectedPerimeters.AllHoleExcision.fineMask excision position = true) :
    ¬side.Exterior (grid.faces.regulars[position.val]'position.isLt).cell.box (Hyperelliptic.Branches.Cuts.Ambient
      curve) := by
  have strict := excision.selected_strict_ambient position selected
  intro exterior
  cases side with
  | bottom => exact (ne_of_lt strict.bottom) exterior.symm
  | right => exact (ne_of_lt strict.right) exterior
  | top => exact (ne_of_lt strict.top) exterior
  | left => exact (ne_of_lt strict.left) exterior.symm

/-- Locate the retained annular entry owning a selected-to-unselected regular interface.

Return its original list membership and exact band-side certificate, preserving the existing path and root choices. -/
@[expose] def interfaceBand
  (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
    (first next : Fin grid.faces.regulars.length) (side : GridSide)
    (matching : side.Matches (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[next.val]'next.isLt).cell.box)
    (selected : RootContinuation.NewtonSelectedPerimeters.AllHoleExcision.fineMask excision first = true)
    (discarded : RootContinuation.NewtonSelectedPerimeters.AllHoleExcision.fineMask excision next = false) :
    {entry : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted // entry ∈ excision.entries ∧
      Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary
        (grid.faces.regulars[first.val]'first.isLt).cell.box (grid.bands.box entry.hole.index) side} := by
  let found := Riemann.RootContinuation.NewtonSelectedSideGeometry.BranchCellBank.NewtonGrid.selected_entry (fun entry :
    Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted =>
    entry.keep (grid.faces.regulars[first.val]'first.isLt)) excision.entries selected
  have inside : (grid.faces.regulars[first.val]'first.isLt).cell.box.Refines (grid.bands.box found.val.hole.index) :=
    of_decide_eq_true found.property.2
  have outside : ¬(grid.faces.regulars[next.val]'next.isLt).cell.box.Refines (grid.bands.box found.val.hole.index) := by
    intro included
    have kept : found.val.keep (grid.faces.regulars[next.val]'next.isLt) = true := decide_eq_true included
    have present := Riemann.RootContinuation.NewtonSelectedSideGeometry.BranchCellBank.NewtonGrid.any_of_member (fun
      entry : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted =>
      entry.keep (grid.faces.regulars[next.val]'next.isLt)) excision.entries found.val found.property.1 kept
    exact Bool.noConfusion (discarded.symm.trans present)
  exact ⟨found.val, found.property.1, grid.selected_interface_boundary found.val.hole.index
    (grid.faces.regulars[first.val]'first.isLt).cell (grid.faces.regulars[next.val]'next.isLt).cell
    (grid.faces.regulars[next.val]'next.isLt).member side matching inside outside⟩

end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision

end

end
end
