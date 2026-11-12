module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.RootRadius
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Winding.Box.Global
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGridCoverage
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.RootIsolation.SquareRoot.Grid.Branch.Location
public import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
public import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Init.Data.List.OfFn
import Purelib.Data.List.OfFn.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.RootIsolation.State.WindingOne.Basic

public section

/-!
# Constructed interior branch holes on an enclosing clear grid

The first branch bank already retains small states strictly inside its
selected faces.  Add those states' sides and the ambient boundary, then
locate each branch inside its retained small state.  The new selected faces
are strictly interior to the ambient frame.  No root isolation is repeated,
and no successful search or hole-interiority premise is required.
-/

namespace Purelib.Curves.Hyperelliptic.Branches

open Purelib
open Purelib.Curves
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
open Purelib.Geometry.Rational.Box
open Purelib.Polynomial.Clearance.Box.Boundary
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.ClearGridCoverage
open Purelib.Polynomial.Geometry.Grid.FramedClearGrid
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.Polynomial.Winding.Box
open Purelib.Riemann.Paths.PreparedPathWinding
open Purelib.RootIsolation.SquareRoot.Grid.Branch
open Purelib.RootIsolation.SquareRoot.Grid.Branch.Location

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Polynomial.Geometry.Grid.FromStates (BranchState)
open _root_.Purelib.Polynomial.Geometry.Grid.FromStates (ofStates_x_bounds ofStates_y_bounds)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding (state state_strict_cell)
open Purelib.RootIsolation.SquareRoot.Grid.Branch.Location (BranchBudget BranchLocation)
open Purelib.Polynomial.Geometry.Grid.Extension (CoordinateInclusion)
open _root_.Purelib.Polynomial.Geometry.Grid.FramedClearGrid (AmbientFrame FramedExtension)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGridCoverage (Located)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath (rawWinding)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Data curve}
  {higher : 1 < curve.polynomial.natDegree}

set_option genInjectivity false in
/-- A branch bank whose removed faces are genuine interior holes. The semantic fields also accept independently
generated checked grids and rows.

Its ambient frame encloses the exact retained grid. Each cached branch row keeps its original owner and proves that the
selected hole lies strictly inside the same curve ambient box. -/
structure FramedBranchCellBank (curve : HyperellipticCurve genus) (branches : Data
  curve)
    (higher : 1 < curve.polynomial.natDegree) extends BranchCellBank curve branches higher where
  /-- The retained ambient boundary frame on the original enlarged grid. -/ frame :
    AmbientFrame grid
  /-- Every retained branch-hole cell lies strictly inside the original ambient box. -/ holesInterior : ∀ index,
    (toBranchCellBank.cell index).box.StrictInterior (Cuts.Ambient curve)

constructive_injectivity FramedBranchCellBank

namespace BranchCellBank

/-- List the original cached small branch states in branch-index order. -/
@[expose] def retainedStates (bank : BranchCellBank curve branches higher) : List (BranchState
  curve.polynomial (Cuts.Ambient curve)) :=
  List.ofFn (state bank)

/-- Each original cached branch state belongs to the retained state list.

The finite table enumerates the original branch indices in order. The supplied index witnesses membership of its exact
cached state, retaining its owner and all bounds. -/
theorem state_mem_retainedStates (bank : BranchCellBank curve branches higher) (index : Data.Index branches) :
    state bank index ∈ bank.retainedStates := Data.List.OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩

/-- Acquire a branch location within its original cached small state.

The framed extension transports the original coordinate membership bounds into its grid. Its retained budget selects the
certified location for the same cached state and branch index. -/
@[expose] def framedLocation (bank : BranchCellBank curve branches higher)
    (extension : FramedExtension bank.grid bank.retainedStates) (budget :
      BranchBudget extension.grid)
    (index : Data.Index branches) : BranchLocation extension.grid (state bank index) :=
  let member := bank.state_mem_retainedStates index
  let x := ofStates_x_bounds _ member
  let y := ofStates_y_bounds _ member
  BranchLocation.acquire budget (degreePositive curve) (branches.track higher index)
    (state bank index)
    (extension.statesIncluded.vertical _ x.1) (extension.statesIncluded.vertical _ x.2)
    (extension.statesIncluded.horizontal _ y.1) (extension.statesIncluded.horizontal _ y.2)

/-- Retain the original parent branch state in a framed-grid row.

The located small state supplies its selected cell and strict containment certificate. Composed refinement witnesses
link both that state and cell back to the exact original cached branch row. -/
@[expose] def framedRow (bank : BranchCellBank curve branches higher)
    (extension : FramedExtension bank.grid bank.retainedStates) (budget :
      BranchBudget extension.grid)
    (index : Data.Index branches) : BranchCellRow extension.grid :=
  let found := bank.framedLocation extension budget index
  ⟨(bank.rows index).original,
    ⟨found.state, found.refines.trans (bank.rows index).location.refines, found.cell, found.member,
      found.strict, found.cell_refines.trans (bank.rows index).location.refines⟩⟩

/-- Reuse a checked enlarged grid and one retained numeric budget. Alternative generated line banks do not need to equal
the canonical frame constructor. -/
@[expose] def framedOfExtension (bank : BranchCellBank curve branches higher)
    (extension : FramedExtension bank.grid bank.retainedStates) (budget :
      BranchBudget extension.grid) :
    FramedBranchCellBank curve branches higher :=
  let rows := Data.Vector.Basic.vectorOfFn (bank.framedRow extension budget)
  { grid := extension.grid
    baseIncluded := bank.baseIncluded.trans extension.originalIncluded
    budget := budget
    rows := rows
    original_eq := fun index => by
      rw [Data.Vector.Basic.vectorOfFn_apply]
      exact bank.original_eq index
    frame := extension.frame
    holesInterior := fun index => by
      change ((rows index).location.cell).box.StrictInterior (Cuts.Ambient curve)
      rw [Data.Vector.Basic.vectorOfFn_apply]
      exact (Refinement.StrictInterior.of_refines
          (Refinement.StrictInterior.Boxes.trans_refines
        (state_strict_cell bank index) (bank.cell index).box_refines))
        (bank.framedLocation extension budget index).cell_refines }

/-- The original framed constructor retains its supplied extension's exact grid. -/
theorem framedOfExtension_grid (bank : BranchCellBank curve branches higher)
    (extension : FramedExtension bank.grid bank.retainedStates) (budget : BranchBudget extension.grid) :
    (bank.framedOfExtension extension budget).grid = extension.grid := by rfl

/-- Each original framed hole refines that SAME original bank row's retained inner state.

The existing row constructor consumes its original location once. Its exact
cell-refinement field supplies this readback without another location query.
-/
theorem framedOfExtension_cell_refines_state (bank : BranchCellBank curve branches higher)
    (extension : FramedExtension bank.grid bank.retainedStates) (budget : BranchBudget extension.grid)
    (index : Data.Index branches) :
    ((bank.framedOfExtension extension budget).toBranchCellBank.cell index).box.Refines (state bank index).box := by
  change ((Data.Vector.Basic.vectorOfFn (bank.framedRow extension budget)) index).location.cell.box.Refines _
  have same := Data.Vector.Basic.vectorOfFn_apply (bank.framedRow extension budget) index
  exact Eq.mpr (congrArg (fun row : BranchCellRow extension.grid =>
    row.location.cell.box.Refines (state bank index).box) same)
    (bank.framedLocation extension budget index).cell_refines

/-- The canonical constructor copies the known ambient boundary clearance and cached branch states before computing the
new grid-wide refinement budget. -/
@[expose] def framed (bank : BranchCellBank curve branches higher) :
  FramedBranchCellBank curve branches higher :=
  let clearance := RootRadius.largeSquare_boundaryClearance (degreePositive curve)
  let extension := FramedExtension.build bank.grid clearance bank.retainedStates
  bank.framedOfExtension extension (BranchBudget.ofGrid extension.grid)

/-- Every original branch-grid coordinate belongs to its constructed framed extension. -/
theorem framed_inclusion (bank : BranchCellBank curve branches higher) : CoordinateInclusion
  bank.grid bank.framed.grid :=
  withFrame_inclusion bank.grid _ _

end BranchCellBank

namespace FramedBranchCellBank

/-- Construct the original branch-cell bank and extend it to an enclosing grid with strict interior branch holes. -/
@[expose] def ofData (curve : HyperellipticCurve genus) (branches : Data curve)
    (higher : 1 < curve.polynomial.natDegree) : FramedBranchCellBank curve branches higher
      :=
  (BranchCellBank.ofData curve branches higher).framed

/-- Read the retained ambient-frame boundary walk of the framed branch bank. -/
@[expose] def exterior (bank : FramedBranchCellBank curve branches higher) :
    Walk bank.grid (Cuts.Ambient curve).anchor (Cuts.Ambient curve).anchor := bank.frame.boundary

/-- The retained exterior boundary raw winding is four times the original curve polynomial degree. -/
theorem exterior_winding (bank : FramedBranchCellBank curve branches higher) :
    rawWinding bank.exterior.path = (4 : Int) * curve.polynomial.natDegree :=
  bank.frame.boundary_winding.trans (Global.largeSquare_winding_eq_degree (degreePositive curve)).1

/-- Coverage now includes the whole enclosing ambient box, not just the coordinate span of the initial branch boxes. -/
@[expose] def locate (bank : FramedBranchCellBank curve branches higher) (point :
  Data.Gaussian.Basic.Canonical) (inside : (Cuts.Ambient curve).Contains point) :
    Located bank.grid point :=
  AmbientFrame.locate bank.frame
    (RootRadius.Box.largeSquareBox_proper _) point inside

/-- Retain an original framed branch family on a coordinate-enlarged grid.

The four original frame coordinates are transported by inclusion. Each
new hole stays inside its actual old labelled hole, so the original
strict ambient containment is preserved without another frame choice.
-/
def onGrid (bank : FramedBranchCellBank curve branches higher)
    (grid : ClearGrid curve.polynomial (Cuts.Ambient curve))
    (included : CoordinateInclusion bank.grid grid) : FramedBranchCellBank curve branches higher :=
  let retained := bank.toBranchCellBank.onGrid grid included
  { toBranchCellBank := retained
    frame := Eq.mpr (congrArg AmbientFrame (bank.toBranchCellBank.onGrid_grid grid included))
      ⟨included.vertical _ bank.frame.xLower, included.vertical _ bank.frame.xUpper,
        included.horizontal _ bank.frame.yLower, included.horizontal _ bank.frame.yUpper⟩
    holesInterior := fun index =>
      Refinement.StrictInterior.of_refines (bank.holesInterior index)
        (bank.toBranchCellBank.onGrid_cell_refines grid included index) }

/-- The framed-grid transport retains exactly its branch-bank execution.

Only the original frame and strict-containment proofs are added to the
same computed branch bank; the row producer is not run a second time.
-/
theorem onGrid_toBranchCellBank (bank : FramedBranchCellBank curve branches higher)
    (grid : ClearGrid curve.polynomial (Cuts.Ambient curve))
    (included : CoordinateInclusion bank.grid grid) :
    (bank.onGrid grid included).toBranchCellBank = bank.toBranchCellBank.onGrid grid included := (rfl)

end FramedBranchCellBank

end Purelib.Curves.Hyperelliptic.Branches
