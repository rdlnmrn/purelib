module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Polynomial.Geometry.Grid.FromStates
public import Purelib.RootIsolation.Winding.Clearance

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification

public section

/-!
# Quantitative analytic data on every classified grid face

Retain a winding-one state on a branch face, or full closed-box polynomial
clearance on an unramified face.  The latter is computed from the proved
zero winding, not supplied by the caller.  No sheet-consistent primitive or
global surface/period comparison is asserted by this local analytic data.
-/

namespace Purelib.Riemann.Meshes.AnalyticGridFaces

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Polynomial.Geometry.Grid.FromStates (BranchState)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification
  (ClassifiedFace FaceKind)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding (ramifiedState unassigned_winding_zero)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

open Purelib.Curves in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- Analytic data for a classified ramified or regular branch-grid face.

A ramified face retains its branch index and a winding-one state on the exact cell box. A regular face retains zero
winding and executable full-box clearance. -/
inductive AnalyticKind (bank : Hyperelliptic.Branches.BranchCellBank curve branches higher) (cell :
  Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve))
  /-- Retain a branch index, the exact branch-cell identity and a state on that cell box. -/ | ramified (index :
    Hyperelliptic.Branches.BranchIsolation.Data.Index branches) (cell_eq : cell = bank.cell index)
      (state : Geometry.Grid.FromStates.BranchState curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve))
        (box_eq : state.box = cell.box)
  /-- Retain zero winding and a full closed-box clearance for the cell. -/ | regular (zero :
    Winding.Box.Basic.quadrupledBoxWinding curve.polynomial cell.box = 0)
      (clearance : Clearance.Box.Region.RegionClearance curve.polynomial cell.box)

constructive_injectivity AnalyticKind

namespace AnalyticKind

variable {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher} {cell :
  Purelib.Polynomial.Geometry.Grid.ClearGrid.Cell curve.polynomial (Purelib.Curves.Hyperelliptic.Branches.Cuts.Ambient
  curve)}

open Purelib.Curves in
/-- Read the retained branch index of a ramified face, or none for a regular face. -/
@[expose] def branchIndex? : AnalyticKind bank cell → Option (Hyperelliptic.Branches.BranchIsolation.Data.Index
  branches)
  | .ramified index _ _ _ => some index
  | .regular _ _ => none

end AnalyticKind

open Purelib.Curves in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- A retained grid cell with membership evidence and its exact analytic payload.

The branch-state or clear-box payload belongs to the exact original cell and its retained bank. Materialization keeps
its source occurrence and mathematical owner. -/
structure AnalyticFace (bank : Hyperelliptic.Branches.BranchCellBank curve branches higher) where
  /-- The retained cell of the branch grid. -/ cell : Geometry.Grid.ClearGrid.Cell curve.polynomial
    (Hyperelliptic.Branches.Cuts.Ambient curve)
  /-- The retained cell belongs to the original bank's grid. -/ member : cell ∈ bank.grid.cells
  /-- The ramified-state or regular-clearance data indexed by that cell. -/ model : AnalyticKind bank cell

constructive_injectivity AnalyticFace

section
open Purelib.Curves
open Purelib.Polynomial
/-- View a clear grid cell as a protected ambient box with the same bounds and clearance.

The original cell box, ambient refinement, properness and boundary clearance are retained unchanged. This view performs
no new root extraction or clearance search. -/
@[expose] def protectedCell (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient
  curve)) :
    Clearance.Box.Region.ProtectedAmbient curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve) :=
  ⟨cell.box, cell.box_refines, cell.box_proper, cell.boundaryClearance⟩

/-- Construct analytic data from a classified branch-grid face.

A branch case reuses its winding-one state; a clear case computes a full-box clearance from the retained zero-winding
proof on that exact cell. -/
@[expose] def ClassifiedFace.analytic {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher} (face :
  Hyperelliptic.Branches.BranchFaceClassification.ClassifiedFace bank) : AnalyticFace bank where
  cell := face.cell
  member := face.member
  model := match face.kind with
    | .branch index equal =>
        .ramified index equal (Hyperelliptic.Branches.BranchCellWinding.ramifiedState bank index) (congrArg
          Geometry.Grid.ClearGrid.Cell.box equal.symm)
    | .clear unassigned =>
        let zero := Hyperelliptic.Branches.BranchCellWinding.unassigned_winding_zero bank face.cell face.member
          unassigned
        .regular zero (Clearance.Box.Region.RegionClearance.ofZeroWinding higher curve.nonzero curve.squarefree
          (protectedCell face.cell) zero)

end

open Purelib.Curves in
/-- Analytic materialization preserves the classified face's optional branch index.

The retained classified face determines its original branch or clear case. Direct reduction of that same case identifies
the optional branch index of the analytic payload. -/
theorem ClassifiedFace.analytic_branchIndex {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher} (face :
  Hyperelliptic.Branches.BranchFaceClassification.ClassifiedFace bank) :
    (ClassifiedFace.analytic face).model.branchIndex? = face.kind.branchIndex? := by
  cases kindEq : face.kind <;> rw [ClassifiedFace.analytic, kindEq] <;> rfl

open Purelib.Curves
/-- Mapping classified faces to analytic payloads preserves the exact list of cells.

Structural mapping retains the exact head cell and the unchanged tail readback. Each analytic payload belongs to its
original classified occurrence, so the ordered cell list is preserved. -/
theorem analytic_cells {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher} (faces : List
  (Hyperelliptic.Branches.BranchFaceClassification.ClassifiedFace bank)) :
    (faces.map ClassifiedFace.analytic).map AnalyticFace.cell = faces.map ClassifiedFace.cell := by
  induction faces with
  | nil => rfl
  | cons face rest ih => exact congrArg (fun cells => face.cell :: cells) ih

/-- Materialize the classified faces and their analytic payloads once for a branch-cell bank. -/
@[expose] def analyticFaces (bank : Hyperelliptic.Branches.BranchCellBank curve branches higher) : List (AnalyticFace
  bank) :=
  (Hyperelliptic.Branches.BranchFaceClassification.classifiedFaces bank).map ClassifiedFace.analytic

/-- The analytic face list has exactly the original bank's grid cells in their retained order. -/
theorem analyticFaces_cells (bank : Hyperelliptic.Branches.BranchCellBank curve branches higher) :
    (analyticFaces bank).map AnalyticFace.cell = bank.grid.cells :=
  (analytic_cells (Hyperelliptic.Branches.BranchFaceClassification.classifiedFaces bank)).trans
    (Hyperelliptic.Branches.BranchFaceClassification.classifiedFaces_cells bank)

end Purelib.Riemann.Meshes.AnalyticGridFaces
