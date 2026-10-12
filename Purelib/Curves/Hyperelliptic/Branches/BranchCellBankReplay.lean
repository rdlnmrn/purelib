module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Exact.LargeSquare
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.RootIsolation.Exact.Canonical
public import Purelib.RootIsolation.Track.Newton.Canonical

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.RootIsolation.SquareRoot.Grid.Branch.Location
public import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
public import Purelib.Curves.Hyperelliptic.Branches.BranchIsolationReplay
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.RootIsolation.Track.Basic

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Polynomial.Elimination.Axis.Certificate

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.RootIsolation

open Purelib.RootIsolation.Exact

open Purelib.RootIsolation.SquareRoot.Grid.Branch.Location

open Purelib.RootIsolation.State

open Purelib.RootIsolation.Track

@[expose] public section

/-! Restore the original branch-cell bank from exact track-refinement states.
The grid, refinement budget, row ordering and selected containing cells remain
those of `BranchCellBank.ofData`. The isolator's refiner identity connects the
saved Newton extraction to each retained branch track. -/
namespace Purelib.Curves.Hyperelliptic.Branches.BranchCellBankReplay

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply vector_ext)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (BranchCellRow)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid (branchGrid refinedState_mem_branchStates)
open _root_.Purelib.Polynomial.Geometry.Grid.FromStates (ofStates_x_bounds ofStates_y_bounds)
open Purelib.RootIsolation.SquareRoot.Grid.Branch.Location (BranchBudget BranchLocation)

variable {genus : Nat} (curve : HyperellipticCurve genus)
  (branches : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve) (higher : 1 <
    curve.polynomial.natDegree)

/-- An original winding-one state for the curve polynomial in its retained ambient box. -/
abbrev State := WindingOne.Basic.WindingOneState curve.polynomial (Cuts.Ambient curve)

/-- The original common branch grid at refinement zero. -/
def grid := BranchGrid.branchGrid curve branches higher 0

/-- The original location budget computed for the retained common branch grid. -/
def budget := BranchBudget.ofGrid (grid curve branches higher)

/-- The original branch-track state at refinement zero for this exact branch occurrence. -/
def original (index : Data.Index branches) : State curve :=
  Cuts.refinedState branches higher index 0

/-- The exact original branch-track refinement to the retained grid budget radius. -/
def refined (index : Data.Index branches) : State curve :=
  (branches.track higher index).refine (original curve branches
    higher index)
    (budget curve branches higher).radius
      (budget curve branches higher).radius_positive

/-- A saved branch state with equality to the original budget-directed refinement. -/
abbrev Saved (index : Data.Index branches) :=
  {state : State curve // state =
    refined curve branches higher index}

/-- Restore the original branch-location row from its exact saved refinement.

The original grid, parent state, nesting proof and budget accuracy determine the same retained face location. -/
def row (index : Data.Index branches) (saved : Saved curve branches
  higher index) :
    BranchCellBank.BranchCellRow (grid curve branches higher) := by
  let current := original curve branches higher index
  let member := BranchGrid.refinedState_mem_branchStates curve branches higher 0 index
  let x := Polynomial.Geometry.Grid.FromStates.ofStates_x_bounds _ member
  let y := Polynomial.Geometry.Grid.FromStates.ofStates_y_bounds _ member
  have nested : saved.val.box.Refines current.box := by
    rw [saved.property]
    exact (branches.track higher index).nested current (budget curve
      branches higher).radius
      (budget curve branches higher).radius_positive
  have accurate : saved.val.box.diagonalSq ≤ (budget curve branches
    higher).radius ^ 2 := by
    rw [saved.property]
    exact (branches.track higher index).accurate current (budget
      curve branches higher).radius
      (budget curve branches higher).radius_positive
  exact ⟨current, BranchLocation.ofRefinement (budget curve branches
    higher)
    (BranchIsolation.degreePositive curve) saved.val nested accurate x.1 x.2 y.1 y.2⟩

/-- Restoring one exact saved refinement gives the original branch-bank row. -/
theorem row_eq (index : Data.Index branches) (saved : Saved curve
  branches higher index) :
    row curve branches higher index saved =
      (Purelib.Curves.Hyperelliptic.Branches.BranchCellBank.ofData curve branches higher).rows index := by
  rcases saved with ⟨state, same⟩
  cases same
  unfold BranchCellBank.ofData
  dsimp only
  rw [Data.Vector.Basic.vectorOfFn_apply]
  rfl

/-- One saved winding-one state for every original branch occurrence. -/
abbrev States := Data.Vector (State curve)
  branches.siteCount

/-- Every saved state equals the original branch-track refinement for the shared grid budget. -/
def Matches (states : States curve branches) : Prop :=
  ∀ index, states index = refined curve branches higher index

/-- Restore the branch-cell bank from exact saved refinements.

The original grid, budget, row ordering and parent-state identities are retained. -/
def restore (states : States curve branches) (same :
  Matches curve branches higher states) :
    Branches.BranchCellBank curve branches higher where
  grid := grid curve branches higher
  baseIncluded := .refl _
  budget := budget curve branches higher
  rows := Data.Vector.Basic.vectorOfFn fun index => row curve
    branches higher index ⟨states index, same index⟩
  original_eq := fun index => by rw [Data.Vector.Basic.vectorOfFn_apply]; rfl

/-- Restoring all exact saved refinements gives the original branch-cell bank. -/
theorem restore_eq (states : States curve branches) (same :
  Matches curve branches higher states) :
    restore curve branches higher states same =
      Purelib.Curves.Hyperelliptic.Branches.BranchCellBank.ofData curve branches higher := by
  have rows : (BranchCellBankReplay.restore curve branches higher states same).rows = (BranchCellBank.ofData curve
    branches higher).rows := by
    apply Data.Vector.Basic.vector_ext
    intro index
    change (Data.Vector.Basic.vectorOfFn fun i => row curve branches
      higher i ⟨states i, same i⟩) index = _
    rw [Data.Vector.Basic.vectorOfFn_apply]
    exact row_eq curve branches higher index _
  unfold BranchCellBankReplay.restore BranchCellBank.ofData at rows ⊢
  dsimp only at rows ⊢
  congr 1

/-- Canonical isolation fixes the complete refiner, not just its initial box. This lets the checkpoint driver invoke
`NewtonExtractionCheckpoint` directly. -/
theorem restored_track {degreeBound : Nat}
    (elimination : AxisSafeCuts.AxisEliminationCertificate curve.polynomial degreeBound)
    (output : Exact.Basic.Output curve.polynomial (Cuts.Ambient curve) curve.polynomial.natDegree)
    (same : output = LargeSquare.isolateLargeSquare higher curve.squarefree elimination)
    (index : Fin curve.polynomial.natDegree) :
    RootIsolation.Track.Newton.Canonical higher curve.squarefree elimination
      ((BranchIsolationReplay.data curve higher output).track higher index) := by
  have known : Newton.Canonical.All higher curve.squarefree elimination output.tracks := by
    rw [same]
    exact Exact.Canonical.largeSquare higher curve.squarefree elimination
  exact Exact.Canonical.trackAt higher curve.squarefree elimination output known index

end Purelib.Curves.Hyperelliptic.Branches.BranchCellBankReplay
