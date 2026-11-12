module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.RootIsolation.SquareRoot.Grid.Branch.Location
public import Purelib.Polynomial.Geometry.Grid.Extension
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Geometry.Grid.Inclusion.CellParents
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

public section

/-!
# Cached branch locations in distinct common-grid faces

Materialize each branch's refined winding-one state and its containing face
once, sharing one grid and one numeric refinement budget.  Every selected
face lies in its original isolated branch box, so different branch indices
give positively separated faces.  `BranchCellWinding` identifies the other
faces as unramified; `FramedBranchCellBank` places the selected faces strictly
inside an enclosing exterior.  Two-sheet gluing is separate.
-/

namespace Purelib.Curves.Hyperelliptic.Branches

open Purelib
open Purelib.Curves
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Geometry
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.RootIsolation.SquareRoot.Grid.Branch
open Purelib.RootIsolation.SquareRoot.Grid.Branch.Location

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Polynomial.Geometry.Grid.FromStates (BranchState)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid
  (branchGrid refinedState_mem_branchStates)
open _root_.Purelib.Polynomial.Geometry.Grid.FromStates
  (ofStates_x_bounds ofStates_y_bounds)
open Purelib.RootIsolation.SquareRoot.Grid.Branch.Location (BranchBudget BranchLocation)
open Purelib.Polynomial.Geometry.Grid.Extension (CoordinateInclusion)

namespace BranchCellBank

set_option genInjectivity false in
/-- One cached original branch box and its certified grid location.

The location is indexed by the exact retained original winding-one state. It supplies the selected grid face and the
refinement certificates for that state without replacing its owner. -/
structure BranchCellRow {polynomial : ClearPath.GaussianPolynomial} {ambient : Rational.Box} (grid :
  ClearGrid polynomial ambient) where
  /-- The retained original winding-one branch state. -/ original : BranchState polynomial ambient
  /-- The certified location of this exact original branch state in the shared grid. -/ location :
    BranchLocation grid original

constructive_injectivity BranchCellRow

end BranchCellBank

set_option genInjectivity false in
/-- A materialized location for every branch index. Coordinate inclusion retains the initial tour geometry while
allowing additional certified lines, including an enclosing frame and smaller branch neighborhoods.

The original curve, branch data and degree bound index the stored common grid and row vector. One shared numeric budget
and the original-state equations certify the retained branch occurrences. -/
structure BranchCellBank {genus : Nat} (curve : HyperellipticCurve genus) (branches :
  Data curve)
    (higher : 1 < curve.polynomial.natDegree) where
  /-- The retained common clear-line grid for all original branch occurrences. -/ grid :
    ClearGrid curve.polynomial
    (Cuts.Ambient curve)
  /-- Every original initial branch-tour grid coordinate belongs to the retained grid. -/ baseIncluded :
    CoordinateInclusion (branchGrid curve branches higher 0) grid
  /-- The shared finite branch-location refinement budget for the retained grid. -/ budget : BranchBudget grid
  /-- The cached original state and certified face location for every original branch index. -/ rows :
    Data.Vector (BranchCellBank.BranchCellRow grid) branches.siteCount
  /-- Each cached row retains exactly the original branch track state at refinement zero. -/ original_eq : ∀ index,
    (rows index).original = Cuts.refinedState branches higher index 0

constructive_injectivity BranchCellBank

namespace BranchCellBank

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Data curve}
  {higher : 1 < curve.polynomial.natDegree}

/-- Retain the original branch state and acquire its certified face location.

The shared grid budget and exact coordinate membership certificates select a location for the original refinement-zero
state. The result retains both that state and its certified containing cell. -/
@[expose] def acquireRow (curve : HyperellipticCurve genus) (branches : Data curve)
    (higher : 1 < curve.polynomial.natDegree)
    (budget : BranchBudget (branchGrid curve branches higher 0)) (index : Data.Index branches) :
    BranchCellRow (branchGrid curve branches higher 0) :=
  let current := Cuts.refinedState branches higher index 0
  let member := refinedState_mem_branchStates curve branches higher 0 index
  let x := ofStates_x_bounds _ member
  let y := ofStates_y_bounds _ member
  ⟨current, BranchLocation.acquire budget (degreePositive curve) (branches.track higher index)
    current x.1 x.2 y.1 y.2⟩

/-- The finite branch data already contains the shrinking tracks. Only one refinement per branch is requested; no branch
isolation is repeated here. -/
@[expose] def ofData (curve : HyperellipticCurve genus) (branches : Data curve)
    (higher : 1 < curve.polynomial.natDegree) : BranchCellBank curve branches higher :=
  let grid := branchGrid curve branches higher 0
  let budget := BranchBudget.ofGrid grid
  { grid := grid
    baseIncluded := .refl grid
    budget := budget
    rows := Data.Vector.Basic.vectorOfFn (acquireRow curve branches higher
      budget)
    original_eq := fun index => by rw [Data.Vector.Basic.vectorOfFn_apply]; rfl }

/-- Geometry consumers use the retained cell directly. -/
@[expose] def cell (bank : BranchCellBank curve branches higher) (index : Data.Index
  branches) :
    Cell curve.polynomial (Cuts.Ambient curve) := (bank.rows index).location.cell

/-- The retained cell for an original branch index belongs to the shared grid. -/
theorem cell_mem (bank : BranchCellBank curve branches higher) (index : Data.Index
  branches) :
    bank.cell index ∈ bank.grid.cells := (bank.rows index).location.member

/-- The retained branch cell lies within its original isolated branch box. -/
theorem cell_refines_original (bank : BranchCellBank curve branches higher) (index :
  Data.Index branches) :
    (bank.cell index).box.Refines (branches.track higher index).initial.box := by
  have refines := (bank.rows index).location.cell_refines
  change (bank.cell index).box.Refines (bank.rows index).original.box at refines
  rw [bank.original_eq index] at refines
  exact refines

/-- Different branches occupy distinct, positively separated grid faces. -/
theorem cells_separated (bank : BranchCellBank curve branches higher) (first second :
  Data.Index branches)
    (different : first ≠ second) : (bank.cell first).box.Separated (bank.cell second).box :=
  (branches.separated higher first second different).of_refines
    (bank.cell_refines_original first) (bank.cell_refines_original second)

/-- Distinct original branch indices have distinct retained grid cells. -/
theorem cells_ne (bank : BranchCellBank curve branches higher) (first second : Data.Index
  branches)
    (different : first ≠ second) : bank.cell first ≠ bank.cell second := by
  intro equal
  have separated := bank.cells_separated first second different
  rw [equal] at separated
  exact separated.points_ne (bank.cell second).box.contains_anchor (bank.cell second).box.contains_anchor rfl

/-- An exact original branch row whose selected new cell refines its old labelled cell. -/
private def RowRefinement (bank : BranchCellBank curve branches higher)
    (grid : Grid curve.polynomial (Cuts.Ambient curve)) (index : Data.Index branches) :=
  { row : BranchCellRow grid // row.original = (bank.rows index).original ∧
      row.location.cell.box.Refines (bank.cell index).box }

/-- Refine the actual retained branch state into a coordinate-enlarged grid.

The old state, its track and its original parent remain inputs. The one
new refinement is located by the original locator, and grid incidence
keeps its selected cell inside the old labelled cell.
-/
private def refineRow (bank : BranchCellBank curve branches higher)
    (grid : Grid curve.polynomial (Cuts.Ambient curve))
    (included : CoordinateInclusion bank.grid grid) (budget : BranchBudget grid)
    (index : Data.Index branches) : RowRefinement bank grid index := by
  let previous := (bank.rows index).location
  let track := branches.track higher index
  let current := track.refine previous.state budget.radius budget.radius_positive
  have nested : current.box.Refines previous.state.box :=
    track.nested previous.state budget.radius budget.radius_positive
  have accurate : current.box.diagonalSq ≤ budget.radius ^ 2 :=
    track.accurate previous.state budget.radius budget.radius_positive
  let initialIncluded := bank.baseIncluded.trans included
  have originalX :
      (bank.rows index).original.box.xLower ∈ grid.vertical.map ClearGrid.VerticalLine.coordinate ∧
      (bank.rows index).original.box.xUpper ∈ grid.vertical.map ClearGrid.VerticalLine.coordinate := by
    rw [bank.original_eq index]
    have bounds := ofStates_x_bounds _ (refinedState_mem_branchStates curve branches higher 0 index)
    exact ⟨initialIncluded.vertical _ bounds.1, initialIncluded.vertical _ bounds.2⟩
  have originalY :
      (bank.rows index).original.box.yLower ∈ grid.horizontal.map ClearGrid.HorizontalLine.coordinate ∧
      (bank.rows index).original.box.yUpper ∈ grid.horizontal.map ClearGrid.HorizontalLine.coordinate := by
    rw [bank.original_eq index]
    have bounds := ofStates_y_bounds _ (refinedState_mem_branchStates curve branches higher 0 index)
    exact ⟨initialIncluded.horizontal _ bounds.1, initialIncluded.horizontal _ bounds.2⟩
  let located := BranchLocation.ofRefinement budget (degreePositive curve) current
    (nested.trans previous.refines) accurate originalX.1 originalX.2 originalY.1 originalY.2
  have inside : located.cell.box.StrictContains current.box.anchor :=
    ⟨located.strict.left, current.box.x_valid.trans_lt located.strict.right,
      located.strict.bottom, current.box.y_valid.trans_lt located.strict.top⟩
  have oldInside : (bank.cell index).box.Contains current.box.anchor :=
    (Rational.Box.Refinement.StrictInterior.refines previous.strict).contains
      (nested.contains current.box.contains_anchor)
  have incidence := Inclusion.CellParents.refines_of_interior included located.member
    (bank.cell_mem index) inside oldInside
  exact ⟨⟨(bank.rows index).original, located⟩, rfl, incidence⟩

/-- Locate the same retained branch family on a supplied coordinate-enlarged grid.

One shared numeric budget and one refinement of each already retained
state produce the new rows. No branch isolation, label permutation or
canonical period programme is constructed here.
-/
def onGrid (bank : BranchCellBank curve branches higher)
    (grid : Grid curve.polynomial (Cuts.Ambient curve))
    (included : CoordinateInclusion bank.grid grid) : BranchCellBank curve branches higher :=
  let budget := BranchBudget.ofGrid grid
  let rows := Data.Vector.Basic.vectorOfFn fun index => (refineRow bank grid included budget index).val
  { grid := grid
    baseIncluded := bank.baseIncluded.trans included
    budget := budget
    rows := rows
    original_eq := fun index => by
      rw [Data.Vector.Basic.vectorOfFn_apply]
      exact (refineRow bank grid included budget index).property.1.trans (bank.original_eq index) }

/-- The retained branch-bank transport has exactly the supplied enlarged grid. -/
theorem onGrid_grid (bank : BranchCellBank curve branches higher)
    (grid : Grid curve.polynomial (Cuts.Ambient curve))
    (included : CoordinateInclusion bank.grid grid) : (bank.onGrid grid included).grid = grid := (rfl)

/-- Each new branch cell belongs to the same original labelled cell.

This is the actual selected-cell refinement retained by the row producer;
it does not follow from equality of root values or from a relabelling.
-/
theorem onGrid_cell_refines (bank : BranchCellBank curve branches higher)
    (grid : Grid curve.polynomial (Cuts.Ambient curve))
    (included : CoordinateInclusion bank.grid grid) (index : Data.Index branches) :
    ((bank.onGrid grid included).cell index).box.Refines (bank.cell index).box := by
  change ((Data.Vector.Basic.vectorOfFn fun index =>
    (refineRow bank grid included (BranchBudget.ofGrid grid) index).val) index).location.cell.box.Refines _
  rw [Data.Vector.Basic.vectorOfFn_apply]
  exact (refineRow bank grid included (BranchBudget.ofGrid grid) index).property.2

end BranchCellBank

end Purelib.Curves.Hyperelliptic.Branches
