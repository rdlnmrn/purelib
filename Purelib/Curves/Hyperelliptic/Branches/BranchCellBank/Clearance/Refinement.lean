module

public import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank.Clearance
public import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.RootIsolation.SquareRoot.Grid.Branch.Location
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.RootIsolation.Track.Exclusion.Uniform

/-! # Related framed branch banks from the same retained clearance preparation

The original grid and holes remain retained inputs. Only their cached inner
winding states are advanced to the actual clearance replies. The existing
framedOfExtension constructor then locates smaller holes in the same cached
extended grid, preserving every original branch occurrence and state owner.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Branches.BranchCellBank.ClearancePreparation

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding (state)
open Purelib.Data.List.OfFn.Basic (ofFn_congr)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.FramedClearGrid (AmbientFrame FramedExtension)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.RootIsolation.SquareRoot.Grid.Branch.Location (BranchBudget)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
    {patches : List (ContinuedNeighborhood curve.polynomial count)}
    (prepared : ClearancePreparation bank patches)

/-- The SAME cached extended grid contains every side coordinate of its actual clearance states. -/
theorem states_included : Extension.CoordinateInclusion (FromStates.ofStates prepared.states) prepared.grid where
  vertical := by
    intro coordinate member
    have added := (ClearGrid.build_vertical_coordinates _ _ _).mp member
    have listed : coordinate ∈ prepared.vertical.map ClearGrid.VerticalLine.coordinate :=
      Eq.mpr (congrArg (fun lines => coordinate ∈ lines.map ClearGrid.VerticalLine.coordinate)
        prepared.vertical_eq) added
    exact Eq.mpr (congrArg (fun grid => coordinate ∈ grid.vertical.map ClearGrid.VerticalLine.coordinate)
      prepared.grid_eq) (Extension.extend_vertical bank.grid prepared.vertical prepared.horizontal listed)
  horizontal := by
    intro coordinate member
    have added := (ClearGrid.build_horizontal_coordinates _ _ _).mp member
    have listed : coordinate ∈ prepared.horizontal.map ClearGrid.HorizontalLine.coordinate :=
      Eq.mpr (congrArg (fun lines => coordinate ∈ lines.map ClearGrid.HorizontalLine.coordinate)
        prepared.horizontal_eq) added
    exact Eq.mpr (congrArg (fun grid => coordinate ∈ grid.horizontal.map ClearGrid.HorizontalLine.coordinate)
      prepared.grid_eq) (Extension.extend_horizontal bank.grid prepared.vertical prepared.horizontal listed)

/-- Advance only the original row's cached inner state, retaining its original state, cell and location certificates.

The actual clearance reply supplies the new state. Its original Uniform
refinement factory composes with the old location refinement, and its proved
strict hole containment preserves the original cell. No callback runs here.
-/
@[expose] def innerRow (index : Data.Index branches) : BranchCellRow bank.grid :=
  let original := bank.rows index
  let reply := prepared.replies.get index
  have nested : reply.state.box.Refines original.location.state.box :=
    Eq.mpr (congrArg (fun value => value.box.Refines original.location.state.box)
      (prepared.reply_state_eq index))
      (RootIsolation.Track.Exclusion.Uniform.refinePastUniformMargin_refines
        (branches.track higher index) original.location.state prepared.lower prepared.lower_positive)
  ⟨original.original, ⟨reply.state, nested.trans original.location.refines,
    original.location.cell, original.location.member, prepared.reply_inside_hole index,
    original.location.cell_refines⟩⟩

/-- The advanced row's inner state is the same retained clearance reply state. -/
theorem innerRow_state (index : Data.Index branches) :
    (prepared.innerRow index).location.state = (prepared.replies.get index).state := by
  unfold innerRow
  rfl

/-- Retain the original bank on its SAME grid and cells with only its actual inner-state cache advanced.

Original branch tracks, indices, outer row states, cell owners, base inclusion
and old grid budget remain unchanged. This related bank is retained beside
the original; it is not an independent isolation or period-bank acquisition.
-/
@[expose] def innerBank : BranchCellBank curve branches higher where
  grid := bank.grid
  baseIncluded := bank.baseIncluded
  budget := bank.budget
  rows := vectorOfFn prepared.innerRow
  original_eq := fun index =>
    (congrArg (fun row : BranchCellRow bank.grid => row.original)
      (vectorOfFn_apply prepared.innerRow index)).trans (bank.original_eq index)

/-- Each related bank row retains exactly its given original clearance state. -/
theorem innerBank_state (index : Data.Index branches) :
    state prepared.innerBank index = (prepared.replies.get index).state :=
  (congrArg (fun row : BranchCellRow bank.grid => row.location.state)
    (vectorOfFn_apply prepared.innerRow index)).trans (prepared.innerRow_state index)

/-- The related bank's original occurrence list is the SAME retained clearance state list. -/
theorem innerBank_states : prepared.innerBank.retainedStates = prepared.states :=
  (ofFn_congr (fun index => prepared.innerBank_state index)).trans prepared.states_eq.symm

/-- View the SAME clearance grid as a framed extension of a GIVEN whole related inner bank.

The original ambient frame transports along the retained coordinate inclusion.
The supplied equality is the actual innerBank factory, transporting the whole
bank jointly; no root or line certificate is reconstructed.
-/
@[expose] def extension (frame : AmbientFrame bank.grid)
    (inner : BranchCellBank curve branches higher) (factory : inner = prepared.innerBank) :
    FramedExtension inner.grid inner.retainedStates := by
  cases factory
  exact ⟨prepared.grid, prepared.included,
    Eq.mpr (congrArg (fun values => Extension.CoordinateInclusion (FromStates.ofStates values) prepared.grid)
      prepared.innerBank_states) prepared.states_included,
    ⟨prepared.included.vertical _ frame.xLower, prepared.included.vertical _ frame.xUpper,
      prepared.included.horizontal _ frame.yLower, prepared.included.horizontal _ frame.yUpper⟩⟩

/-- The related extension retains exactly the existing cached clearance grid. -/
theorem extension_grid (frame : AmbientFrame bank.grid)
    (inner : BranchCellBank curve branches higher) (factory : inner = prepared.innerBank) :
    (prepared.extension frame inner factory).grid = prepared.grid := by
  cases factory
  unfold extension
  rfl

/-- Original related-bank, extension, budget and framed result caches with all complete factories.

The final bank is constructed only by the existing framedOfExtension worker.
Its genuine BranchLocation calls remain explicit new work, one per original
finite branch occurrence, after the new budget has been computed once.
-/
@[expose] def FramedRefinement (frame : AmbientFrame bank.grid) : Type _ :=
  (inner : {value : BranchCellBank curve branches higher // value = prepared.innerBank}) ×
  (extension : {value : FramedExtension inner.val.grid inner.val.retainedStates //
    value = prepared.extension frame inner.val inner.property}) ×
  (budget : {value : BranchBudget extension.val.grid // value = BranchBudget.ofGrid extension.val.grid}) ×
  {fine : FramedBranchCellBank curve branches higher //
    fine = inner.val.framedOfExtension extension.val budget.val}

/-- Locate genuinely smaller branch holes once through the original framed-bank construction.

The 385 states and grid are supplied caches. The related inner bank and
extension perform record/list work, one new BranchBudget precedes the old
framedOfExtension worker, and each original BranchLocation operation executes
once. The original bank and its cut are never replaced or rebuilt.
-/
def refineFramed (frame : AmbientFrame bank.grid) : prepared.FramedRefinement frame :=
  let inner := prepared.innerBank
  let extension := prepared.extension frame inner rfl
  let budget := BranchBudget.ofGrid extension.grid
  let fine := inner.framedOfExtension extension budget
  ⟨⟨inner, rfl⟩, ⟨extension, rfl⟩, ⟨budget, rfl⟩, ⟨fine, rfl⟩⟩

namespace FramedRefinement

variable {prepared} {frame : AmbientFrame bank.grid} (refined : prepared.FramedRefinement frame)

/-- Read the same related inner bank with its exact original constructor factory. -/
@[expose] def inner : BranchCellBank curve branches higher := refined.1.val

/-- Read the actual once-built framed bank on the same cached extended grid. -/
@[expose] def fine : FramedBranchCellBank curve branches higher := refined.2.2.2.val

/-- The actual framed bank uses exactly the original clearance preparation's extended grid. -/
theorem grid_eq : refined.fine.grid = prepared.grid :=
  (congrArg (fun value : FramedBranchCellBank curve branches higher => value.grid) refined.2.2.2.property).trans
    ((BranchCellBank.framedOfExtension_grid refined.inner refined.2.1.val refined.2.2.1.val).trans
      ((congrArg (fun value => value.grid) refined.2.1.property).trans
        (prepared.extension_grid frame refined.inner refined.1.property)))

/-- Each new hole refines the SAME original clearance reply state. -/
theorem cell_refines (index : Data.Index branches) :
    (refined.fine.toBranchCellBank.cell index).box.Refines (prepared.replies.get index).state.box := by
  have cellEq := congrArg (fun value : FramedBranchCellBank curve branches higher =>
    (value.toBranchCellBank.cell index).box) refined.2.2.2.property
  have bounded := BranchCellBank.framedOfExtension_cell_refines_state
    refined.inner refined.2.1.val refined.2.2.1.val index
  have stateEq := (congrArg (fun value : BranchCellBank curve branches higher => state value index)
    refined.1.property).trans (prepared.innerBank_state index)
  have moved := Eq.mp (congrArg (fun value =>
      ((refined.inner.framedOfExtension refined.2.1.val refined.2.2.1.val).toBranchCellBank.cell index).box.Refines
        value.box) stateEq) bounded
  exact Eq.mpr (congrArg (fun value => value.Refines (prepared.replies.get index).state.box) cellEq) moved

/-- Every original branch occurrence retains its whole SAME original winding-one state. -/
theorem row_original (index : Data.Index branches) :
    (refined.fine.toBranchCellBank.rows index).original = (bank.rows index).original :=
  (refined.fine.toBranchCellBank.original_eq index).trans (bank.original_eq index).symm

/-- Every new hole stays strictly inside its SAME old original hole. -/
theorem cell_inside_original (index : Data.Index branches) :
    (refined.fine.toBranchCellBank.cell index).box.StrictInterior (bank.cell index).box :=
  Box.Refinement.StrictInterior.of_refines (prepared.reply_inside_hole index) (refined.cell_refines index)

/-- Every smaller hole remains positively separated from all original supplied neighborhood occurrences. -/
theorem separated (index : Data.Index branches)
    {patch : ContinuedNeighborhood curve.polynomial count} (member : patch ∈ patches) :
    (refined.fine.toBranchCellBank.cell index).box.Separated patch.box :=
  (prepared.separated index member).of_refines (refined.cell_refines index) (Box.refines_refl patch.box)

end FramedRefinement

end Purelib.Curves.Hyperelliptic.Branches.BranchCellBank.ClearancePreparation

end
