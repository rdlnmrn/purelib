module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.RootRadius
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.RootIsolation.SquareRoot.Grid.Branch.Location
public import Purelib.Curves.Hyperelliptic.Branches.BranchCellBankReplay
public import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation

open Purelib.Geometry.Rational.Box

open Purelib.Polynomial.Clearance.Box.Boundary

open Purelib.Polynomial.Geometry.Grid.FramedClearGrid

open Purelib.Polynomial.Geometry.Grid.FramedClearGrid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Riemann

open Purelib.Riemann.Meshes

open Purelib.RootIsolation.SquareRoot.Grid.Branch

open Purelib.RootIsolation.SquareRoot.Grid.Branch.Location

@[expose] public section

/-! Restore the second canonical branch refinement, its enclosing frame and
its classified punctured grid. The first bank and its retained states remain
shared; every restored field belongs to the original framed constructor. -/
namespace Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBankReplay

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply vector_ext)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank FramedBranchCellBank)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (BranchCellRow)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding (state state_strict_cell)
open _root_.Purelib.Polynomial.Geometry.Grid.FromStates (ofStates_x_bounds ofStates_y_bounds)
open Purelib.RootIsolation.SquareRoot.Grid.Branch.Location (BranchBudget BranchLocation)
open _root_.Purelib.Polynomial.Geometry.Grid.FramedClearGrid (FramedExtension)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} (bank : BranchCellBank curve branches
    higher)

/-- Extend the original branch grid by the retained large-square boundary clearance and original branch states. -/
def extension : Polynomial.Geometry.Grid.FramedClearGrid.FramedExtension bank.grid bank.retainedStates :=
  FramedExtension.build bank.grid
    (RootRadius.largeSquare_boundaryClearance (BranchIsolation.degreePositive curve)) bank.retainedStates

/-- The finite location budget of the retained framed grid extension. -/
def budget := BranchBudget.ofGrid (extension bank).grid

section
open Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
/-- Refine the original indexed branch state to the retained framed-grid budget radius. -/
def refined (index : Data.Index branches) : BranchCellBankReplay.State curve :=
  (branches.track higher index).refine (state bank index)
    (budget bank).radius
    (budget bank).radius_positive

/-- The saved branch state is exactly the original indexed state at the framed-grid refinement. -/
abbrev Saved (index : Data.Index branches) :=
  {state : BranchCellBankReplay.State curve // state = refined
    bank index}

/-- Restore the original branch location from its exact saved state, retained refinement bounds and framed-grid
coordinate inclusions. -/
def location (index : Data.Index branches) (saved : Saved bank
  index) :
    Location.BranchLocation (extension bank).grid (state bank
      index) := by
  let member := bank.state_mem_retainedStates index
  let x := Polynomial.Geometry.Grid.FromStates.ofStates_x_bounds _ member
  let y := Polynomial.Geometry.Grid.FromStates.ofStates_y_bounds _ member
  have nested : saved.val.box.Refines (state bank index).box := by
    rw [saved.property]
    exact (branches.track higher index).nested _ (budget
      bank).radius (budget bank).radius_positive
  have accurate : saved.val.box.diagonalSq ≤ (budget
    bank).radius ^ 2 := by
    rw [saved.property]
    exact (branches.track higher index).accurate _ (budget
      bank).radius (budget bank).radius_positive
  exact BranchLocation.ofRefinement (budget bank)
    (BranchIsolation.degreePositive curve)
    saved.val nested accurate
    ((extension bank).statesIncluded.vertical _ x.1)
      ((extension bank).statesIncluded.vertical _ x.2)
    ((extension bank).statesIncluded.horizontal _ y.1)
      ((extension bank).statesIncluded.horizontal _ y.2)

end

/-- Restore one framed row using its original branch state and the certified saved location. -/
def row (index : Data.Index branches) (saved : Saved bank
  index) :
    BranchCellBank.BranchCellRow (extension bank).grid :=
  let found := location bank index saved
  ⟨(bank.rows index).original,
    ⟨found.state, found.refines.trans (bank.rows index).location.refines, found.cell, found.member,
      found.strict, found.cell_refines.trans (bank.rows index).location.refines⟩⟩

/-- The restored row equals the original framed bank row at the same branch index. -/
theorem row_eq (index : Data.Index branches) (saved : Saved
  bank index) :
    row bank index saved = bank.framed.rows index := by
  rcases saved with ⟨state, same⟩
  cases same
  unfold BranchCellBank.framed BranchCellBank.framedOfExtension
  dsimp only
  rw [Data.Vector.Basic.vectorOfFn_apply]
  rfl

/-- Every saved branch state equals the original indexed branch state at its retained framed refinement. -/
def Matches (states : BranchCellBankReplay.States curve branches) : Prop :=
  ∀ index, states index = refined bank index

/-- Reconstruct the framed branch bank from matching saved states.

The original extension grid, shared budget, branch indices and strict frame containment certificates are preserved. -/
def restore (states : BranchCellBankReplay.States curve branches) (same :
  Matches bank states) :
    Branches.FramedBranchCellBank curve branches higher where
  grid := (extension bank).grid
  baseIncluded := bank.baseIncluded.trans (extension
    bank).originalIncluded
  budget := budget bank
  rows := Data.Vector.Basic.vectorOfFn fun index => row bank
    index ⟨states index, same index⟩
  original_eq := fun index => by
    rw [Data.Vector.Basic.vectorOfFn_apply]
    exact bank.original_eq index
  frame := (extension bank).frame
  holesInterior := fun index => by
    rw [BranchCellBank.cell, Data.Vector.Basic.vectorOfFn_apply]
    exact Geometry.Rational.Box.Refinement.StrictInterior.of_refines
      (Geometry.Rational.Box.Refinement.StrictInterior.Boxes.trans_refines
        (BranchCellWinding.state_strict_cell bank index) (bank.cell index).box_refines)
      (location bank index ⟨states index, same
        index⟩).cell_refines

/-- Restoring matching saved states recovers exactly the original framed branch bank. -/
theorem restore_eq (states : BranchCellBankReplay.States curve branches) (same :
  Matches bank states) :
    restore bank states same = bank.framed := by
  have rows : (restore bank states same).rows =
    bank.framed.rows := by
    apply Data.Vector.Basic.vector_ext
    intro index
    change (Data.Vector.Basic.vectorOfFn fun i => row bank i
      ⟨states i, same i⟩) index = _
    rw [Data.Vector.Basic.vectorOfFn_apply]
    exact row_eq bank index _
  unfold restore BranchCellBank.framed
    BranchCellBank.framedOfExtension at rows ⊢
  dsimp only at rows ⊢
  congr 2

/-- Construct the punctured grid from the restored framed branch bank and its retained holes. -/
def punctured (states : BranchCellBankReplay.States curve branches) (same :
  Matches bank states) :
    Meshes.FramedPuncturedGrid curve branches higher := FramedPuncturedGrid.ofBank
      (restore bank states same)

/-- The restored punctured grid equals the one constructed from the original framed bank. -/
theorem punctured_eq (states : BranchCellBankReplay.States curve branches) (same :
  Matches bank states) :
    punctured bank states same = FramedPuncturedGrid.ofBank
      bank.framed :=
  congrArg FramedPuncturedGrid.ofBank (restore_eq bank states
    same)

end Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBankReplay
