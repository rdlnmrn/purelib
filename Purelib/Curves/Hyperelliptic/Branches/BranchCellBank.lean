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
  Polynomial.Geometry.Grid.ClearGrid polynomial ambient) where
  /-- The retained original winding-one branch state. -/ original : FromStates.BranchState polynomial ambient
  /-- The certified location of this exact original branch state in the shared grid. -/ location :
    Location.BranchLocation grid original

constructive_injectivity BranchCellRow

end BranchCellBank

set_option genInjectivity false in
/-- A materialized location for every branch index. Coordinate inclusion retains the initial tour geometry while
allowing additional certified lines, including an enclosing frame and smaller branch neighborhoods.

The original curve, branch data and degree bound index the stored common grid and row vector. One shared numeric budget
and the original-state equations certify the retained branch occurrences. -/
structure BranchCellBank {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches :
  BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree) where
  /-- The retained common clear-line grid for all original branch occurrences. -/ grid :
    Polynomial.Geometry.Grid.ClearGrid curve.polynomial
    (Cuts.Ambient curve)
  /-- Every original initial branch-tour grid coordinate belongs to the retained grid. -/ baseIncluded :
    Extension.CoordinateInclusion (BranchGrid.branchGrid curve branches higher 0) grid
  /-- The shared finite branch-location refinement budget for the retained grid. -/ budget : Location.BranchBudget grid
  /-- The cached original state and certified face location for every original branch index. -/ rows :
    Data.Vector (Curves.Hyperelliptic.Branches.BranchCellBank.BranchCellRow grid) branches.siteCount
  /-- Each cached row retains exactly the original branch track state at refinement zero. -/ original_eq : ∀ index,
    (rows index).original = Cuts.refinedState branches higher index 0

constructive_injectivity BranchCellBank

namespace BranchCellBank

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

/-- Retain the original branch state and acquire its certified face location.

The shared grid budget and exact coordinate membership certificates select a location for the original refinement-zero
state. The result retains both that state and its certified containing cell. -/
@[expose] def acquireRow (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree)
    (budget : Location.BranchBudget (BranchGrid.branchGrid curve branches higher 0)) (index : Data.Index branches) :
    BranchCellRow (BranchGrid.branchGrid curve branches higher 0) :=
  let current := Cuts.refinedState branches higher index 0
  let member := BranchGrid.refinedState_mem_branchStates curve branches higher 0 index
  let x := Polynomial.Geometry.Grid.FromStates.ofStates_x_bounds _ member
  let y := Polynomial.Geometry.Grid.FromStates.ofStates_y_bounds _ member
  ⟨current, BranchLocation.acquire budget (BranchIsolation.degreePositive curve) (branches.track higher index)
    current x.1 x.2 y.1 y.2⟩

/-- The finite branch data already contains the shrinking tracks. Only one refinement per branch is requested; no branch
isolation is repeated here. -/
@[expose] def ofData (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree) : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher :=
  let grid := BranchGrid.branchGrid curve branches higher 0
  let budget := BranchBudget.ofGrid grid
  { grid := grid
    baseIncluded := .refl grid
    budget := budget
    rows := Data.Vector.Basic.vectorOfFn (acquireRow curve branches higher
      budget)
    original_eq := fun index => by rw [Data.Vector.Basic.vectorOfFn_apply]; rfl }

/-- Geometry consumers use the retained cell directly. -/
@[expose] def cell (bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher) (index : Data.Index
  branches) :
    ClearGrid.Cell curve.polynomial (Cuts.Ambient curve) := (bank.rows index).location.cell

/-- The retained cell for an original branch index belongs to the shared grid. -/
theorem cell_mem (bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher) (index : Data.Index
  branches) :
    bank.cell index ∈ bank.grid.cells := (bank.rows index).location.member

/-- The retained branch cell lies within its original isolated branch box. -/
theorem cell_refines_original (bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher) (index :
  Data.Index branches) :
    (bank.cell index).box.Refines (branches.track higher index).initial.box := by
  have refines := (bank.rows index).location.cell_refines
  change (bank.cell index).box.Refines (bank.rows index).original.box at refines
  rw [bank.original_eq index] at refines
  exact refines

/-- Different branches occupy distinct, positively separated grid faces. -/
theorem cells_separated (bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher) (first second :
  Data.Index branches)
    (different : first ≠ second) : (bank.cell first).box.Separated (bank.cell second).box :=
  (branches.separated higher first second different).of_refines
    (bank.cell_refines_original first) (bank.cell_refines_original second)

/-- Distinct original branch indices have distinct retained grid cells. -/
theorem cells_ne (bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher) (first second : Data.Index
  branches)
    (different : first ≠ second) : bank.cell first ≠ bank.cell second := by
  intro equal
  have separated := bank.cells_separated first second different
  rw [equal] at separated
  exact separated.points_ne (bank.cell second).box.contains_anchor (bank.cell second).box.contains_anchor rfl

end BranchCellBank

end Purelib.Curves.Hyperelliptic.Branches
