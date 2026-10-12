module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.ClearGridCoverage
public import Purelib.Riemann.Meshes.AnalyticGridFaces
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# The actual common grid with its branch faces removed

Split the retained analytic face list into regular faces and branch holes.
The indexed spine preserves every original cell exactly once; regular faces
retain their full-box clearance and holes retain their actual winding-one
state.  No regularity of a branch face or flat sheet gauge is assumed.
-/

namespace Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Polynomial.Geometry.Grid.FromStates (BranchState)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Riemann.Meshes.AnalyticGridFaces (AnalyticFace AnalyticKind analyticFaces analyticFaces_cells)
open Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification (FaceKind)
open Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification.FaceKind (branch_unique)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding (selected_winding_four)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

open Purelib.Curves in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- A retained grid face with zero winding and whole-box polynomial clearance.

The actual cell and membership proof belong to the original branch-cell bank's grid. -/
structure RegularFace (bank : Hyperelliptic.Branches.BranchCellBank curve branches higher) where
  /-- The actual regular cell in the retained common grid. -/ cell : Geometry.Grid.ClearGrid.Cell curve.polynomial
    (Hyperelliptic.Branches.Cuts.Ambient curve)
  /-- The regular cell belongs to the original grid's cell list. -/ member : cell ∈ bank.grid.cells
  /-- The defining polynomial has zero quadrupled boundary winding on this cell. -/ winding_zero :
    Winding.Box.Basic.quadrupledBoxWinding curve.polynomial cell.box = 0
  /-- The defining polynomial is certified clear throughout this actual cell box. -/ clearance :
    Clearance.Box.Region.RegionClearance curve.polynomial cell.box

constructive_injectivity RegularFace

open Purelib.Curves in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- A retained branch cell with its original label and certified winding-one state.

The cell belongs to the common grid, equals the bank's selected cell for that label, and has the same box as the
retained state. -/
structure BranchHole (bank : Hyperelliptic.Branches.BranchCellBank curve branches higher) where
  /-- The retained finite branch label. -/ index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches
  /-- The actual branch-hole cell of the common grid. -/ cell : Geometry.Grid.ClearGrid.Cell curve.polynomial
    (Hyperelliptic.Branches.Cuts.Ambient curve)
  /-- The hole cell belongs to the original grid's cell list. -/ member : cell ∈ bank.grid.cells
  /-- The actual hole cell equals the bank's selected cell for its retained label. -/ cell_eq : cell = bank.cell index
  /-- The retained winding-one root state in the original ambient box. -/ state : Geometry.Grid.FromStates.BranchState
    curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)
  /-- The retained root state and hole cell have the same actual box. -/ box_eq : state.box = cell.box

constructive_injectivity BranchHole

namespace RegularFace

open Purelib.Curves in
/-- A zero-winding regular face is distinct from every selected branch cell. -/
theorem unassigned {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher} (face : RegularFace bank)
    (index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches) : face.cell ≠ bank.cell index := by
  intro equal
  have zero := face.winding_zero
  rw [equal, Hyperelliptic.Branches.BranchCellWinding.selected_winding_four bank index] at zero
  exact (by decide : (4 : Int) ≠ 0) zero

end RegularFace

open Purelib.Curves in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- An ordered classification spine indexed by the exact original cell list.

Each constructor retains either a certified regular face or a branch hole while preserving that cell at the head of the
original list. -/
inductive FaceSplit (bank : Hyperelliptic.Branches.BranchCellBank curve branches higher) :
    List (Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) → Type
  /-- The empty cell list has an empty classification spine. -/ | nil : FaceSplit bank []
  /-- Prepend a retained regular face to the exact classified cell tail. -/ | regular {cells : List
    (Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve))}
      (face : RegularFace bank) (tail : FaceSplit bank cells) : FaceSplit bank (face.cell :: cells)
  /-- Prepend a retained branch hole to the exact classified cell tail. -/ | hole {cells : List
    (Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve))}
      (face : BranchHole bank) (tail : FaceSplit bank cells) : FaceSplit bank (face.cell :: cells)

constructive_injectivity FaceSplit

namespace FaceSplit

open Purelib.Data.List

variable {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher}

/-- Convert retained analytic face models to an ordered regular-or-hole classification.

The conversion preserves each actual cell, grid membership and the existing clearance or ramified-state evidence. -/
@[expose] def ofAnalytic : (faces : List (AnalyticFace bank)) → FaceSplit bank (faces.map AnalyticFace.cell)
  | [] => .nil
  | face :: faces =>
      match face.model with
      | .regular zero clearance => .regular ⟨face.cell, face.member, zero, clearance⟩ (ofAnalytic faces)
      | .ramified index equal state boxEq =>
          .hole ⟨index, face.cell, face.member, equal, state, boxEq⟩ (ofAnalytic faces)

section
open Purelib.Curves
open Purelib.Polynomial
/-- Read the regular faces from the classification spine in their original order. -/
@[expose] def regulars : {cells : List (Geometry.Grid.ClearGrid.Cell curve.polynomial
  (Hyperelliptic.Branches.Cuts.Ambient curve))} → FaceSplit bank cells → List (RegularFace bank)
  | _, .nil => []
  | _, .regular face tail => face :: tail.regulars
  | _, .hole _ tail => tail.regulars

/-- Read the branch holes from the classification spine in their original order. -/
@[expose] def holes : {cells : List (Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient
  curve))} → FaceSplit bank cells → List (BranchHole bank)
  | _, .nil => []
  | _, .regular _ tail => tail.holes
  | _, .hole face tail => face :: tail.holes

/-- The two classified list lengths sum to the original cell-list length. -/
theorem length_eq : ∀ {cells : List (Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient
  curve))} (split : FaceSplit bank cells),
    split.regulars.length + split.holes.length = cells.length
  | _, .nil => rfl
  | _, .regular _ tail => by
      simp only [regulars, holes, List.length_cons]
      have count := tail.length_eq
      omega
  | _, .hole _ tail => by
      simp only [regulars, holes, List.length_cons]
      have count := tail.length_eq
      omega

/-- Every classified regular face retains a cell from the original indexed list.

Structural recursion retains the original regular-face occurrence and its exact source cell. Each head or tail
membership constructor identifies that same cell in the classification spine. -/
theorem regular_member : ∀ {cells : List (Geometry.Grid.ClearGrid.Cell curve.polynomial
  (Hyperelliptic.Branches.Cuts.Ambient curve))} (split : FaceSplit bank cells)
    {face : RegularFace bank}, face ∈ split.regulars → face.cell ∈ cells
  | _, .nil, _, member => (List.not_mem_nil member).elim
  | _, .regular head tail, face, member => by
      rcases Membership.mem_cons.mp member with equal | member
      · exact Membership.mem_cons.mpr (Or.inl (congrArg RegularFace.cell equal))
      · exact List.mem_cons_of_mem _ (tail.regular_member member)
  | _, .hole _ tail, _, member => List.mem_cons_of_mem _ (tail.regular_member member)

/-- Every classified branch hole retains a cell from the original indexed list.

Structural recursion retains the original branch-hole occurrence and its exact source cell. Each head or tail membership
constructor identifies that same cell in the classification spine. -/
theorem hole_member : ∀ {cells : List (Geometry.Grid.ClearGrid.Cell curve.polynomial
  (Hyperelliptic.Branches.Cuts.Ambient curve))} (split : FaceSplit bank cells)
    {face : BranchHole bank}, face ∈ split.holes → face.cell ∈ cells
  | _, .nil, _, member => (List.not_mem_nil member).elim
  | _, .regular _ tail, _, member => List.mem_cons_of_mem _ (tail.hole_member member)
  | _, .hole head tail, face, member => by
      rcases Membership.mem_cons.mp member with equal | member
      · exact Membership.mem_cons.mpr (Or.inl (congrArg BranchHole.cell equal))
      · exact List.mem_cons_of_mem _ (tail.hole_member member)

/-- Every original cell is retained by a regular face or a branch hole in the split.

Each original cell occurrence is retained in exactly the regular or hole branch supplied by the classification spine.
Structural recursion returns the corresponding original face and its ordered-list membership witness. -/
theorem covers : ∀ {cells : List (Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient
  curve))} (split : FaceSplit bank cells)
    {cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)}, cell ∈ cells →
      (∃ face ∈ split.regulars, face.cell = cell) ∨ (∃ hole ∈ split.holes, hole.cell = cell)
  | _, .nil, _, member => (List.not_mem_nil member).elim
  | _, .regular face tail, cell, member => by
      rcases Membership.mem_cons.mp member with equal | member
      · exact Or.inl ⟨face, List.mem_cons_self, equal.symm⟩
      · rcases tail.covers member with ⟨other, belongs, equal⟩ | found
        · exact Or.inl ⟨other, List.mem_cons_of_mem _ belongs, equal⟩
        · exact Or.inr found
  | _, .hole face tail, cell, member => by
      rcases Membership.mem_cons.mp member with equal | member
      · exact Or.inr ⟨face, List.mem_cons_self, equal.symm⟩
      · rcases tail.covers member with found | ⟨other, belongs, equal⟩
        · exact Or.inl found
        · exact Or.inr ⟨other, List.mem_cons_of_mem _ belongs, equal⟩

/-- A proper grid cell's interior is not separated from itself. -/
private theorem not_self_separated (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial
  (Hyperelliptic.Branches.Cuts.Ambient curve)) : ¬cell.box.InteriorSeparated cell.box := by
  intro separated
  rcases separated with before | after | below | above
  · exact (not_lt_of_ge before) cell.box_proper.1
  · exact (not_lt_of_ge after) cell.box_proper.1
  · exact (not_lt_of_ge below) cell.box_proper.2
  · exact (not_lt_of_ge above) cell.box_proper.2

/-- Pairwise separated original cells give pairwise distinct retained branch-hole labels. -/
theorem holes_pairwise : ∀ {cells : List (Geometry.Grid.ClearGrid.Cell curve.polynomial
  (Hyperelliptic.Branches.Cuts.Ambient curve))} (split : FaceSplit bank cells),
    cells.Pairwise (fun first second => first.box.InteriorSeparated second.box) →
      split.holes.Pairwise (fun first second => first.index ≠ second.index)
  | _, .nil, _ => .nil
  | _, .regular _ tail, separated => tail.holes_pairwise (List.pairwise_cons.mp separated).2
  | _, .hole head tail, separated => by
      refine .cons ?_ (tail.holes_pairwise (List.pairwise_cons.mp separated).2)
      intro other member equal
      have apart := (List.pairwise_cons.mp separated).1 other.cell (tail.hole_member member)
      have cellsEq : head.cell = other.cell := head.cell_eq.trans ((congrArg bank.cell equal).trans other.cell_eq.symm)
      rw [cellsEq] at apart
      exact not_self_separated other.cell apart

end

end FaceSplit

open Purelib.Curves in
set_option genInjectivity false in
/-- The exact grid classification with materialized regular-face and branch-hole lists.

Readback equations bind both caches to the same classification spine over the retained grid's complete cell list. -/
structure PuncturedFaces (bank : Hyperelliptic.Branches.BranchCellBank curve branches higher) where
  /-- The classification spine indexed by the exact retained grid cell list. -/ split : FaceSplit bank bank.grid.cells
  /-- The materialized ordered regular-face cache. -/ regulars : List (RegularFace bank)
  /-- The regular-face cache equals the spine's regular readback. -/ regulars_eq : regulars = split.regulars
  /-- The materialized ordered branch-hole cache. -/ holes : List (BranchHole bank)
  /-- The branch-hole cache equals the spine's hole readback. -/ holes_eq : holes = split.holes

constructive_injectivity PuncturedFaces

namespace PuncturedFaces

variable {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher}

section
open Purelib.Curves
/-- Materialize punctured faces from analytic models covering the exact original grid cells. -/
@[expose] def ofAnalytic (bank : Hyperelliptic.Branches.BranchCellBank curve branches higher) (faces : List
  (AnalyticFace bank))
    (cellsEq : faces.map AnalyticFace.cell = bank.grid.cells) : PuncturedFaces bank :=
  let split := cellsEq ▸ FaceSplit.ofAnalytic faces
  ⟨split, split.regulars, rfl, split.holes, rfl⟩

/-- Build and cache the regular faces and holes of the retained branch-cell bank. -/
@[expose] def build (bank : Hyperelliptic.Branches.BranchCellBank curve branches higher) : PuncturedFaces bank :=
  ofAnalytic bank (analyticFaces bank) (analyticFaces_cells bank)

end

/-- The cached regular and hole counts sum to the retained grid cell count. -/
theorem length_eq (faces : PuncturedFaces bank) : faces.regulars.length + faces.holes.length = bank.grid.cells.length :=
  by
  rw [faces.regulars_eq, faces.holes_eq]
  exact faces.split.length_eq

open Purelib.Curves in
/-- Every original branch label occurs in the retained hole cache. -/
theorem hole_complete (faces : PuncturedFaces bank) (index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches)
  :
    ∃ hole ∈ faces.holes, hole.index = index := by
  rcases faces.split.covers (bank.cell_mem index) with ⟨regular, _, equal⟩ | ⟨hole, member, equal⟩
  · exact (regular.unassigned index equal).elim
  · refine ⟨hole, ?_, Hyperelliptic.Branches.BranchFaceClassification.FaceKind.branch_unique hole.cell_eq equal⟩
    rw [faces.holes_eq]
    exact member

open Purelib.Polynomial in
/-- Distinct entries in the retained hole cache have distinct branch labels. -/
theorem holes_pairwise (faces : PuncturedFaces bank) :
    faces.holes.Pairwise (fun first second => first.index ≠ second.index) := by
  rw [faces.holes_eq]
  exact faces.split.holes_pairwise (Polynomial.Geometry.Grid.ClearGridCoverage.cells_pairwise bank.grid)

end PuncturedFaces

end Purelib.Riemann.Meshes.PuncturedGridFaces
