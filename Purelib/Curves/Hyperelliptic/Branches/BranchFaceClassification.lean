module
import Purelib.Data.List.Membership
public import Purelib.Data.List.OfFn.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Polynomial.Winding.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Polynomial.Geometry.Grid.CellSeparation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Init.Data.Int.Basic
import Init.Data.List.Lemmas
import Init.Data.List.OfFn
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation

open Purelib.Polynomial

open Purelib.Polynomial.Geometry.Grid

public section

/-!
# Executable classification of every retained grid face

Compare a face with the anchors of the cached small branch boxes.  Strict
interiority identifies a matching branch's actual cell, without decidable
equality of clearance functions.  An exhausted finite scan proves winding
zero.  The classification does not evaluate a Cauchy index or run an isolator;
the exact winding equations are supplied by the generic degree-bound proof.
-/

namespace Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
  (state selected_winding_four unassigned_winding_zero anchor_strict_cell)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

set_option genInjectivity false in
/-- One actual branch index, or proof that none of the finite branch sites belongs to this face.

The selected index retains its exact branch-cell identity, while the clear alternative certifies exclusion of every
original selected branch cell. These are evidence for the same displayed grid face. -/
inductive FaceKind (bank : Branches.BranchCellBank curve branches higher) (cell : ClearGrid.Cell curve.polynomial
  (Cuts.Ambient curve))
  /-- Retain the original branch occurrence and equality of its selected cell with this face. -/ | branch (index :
    Data.Index branches) (cell_eq : cell = bank.cell index)
  /-- Retain proof that this face is none of the original selected branch cells. -/ | clear (unassigned : ∀ index, cell
    ≠ bank.cell index)

constructive_injectivity FaceKind

namespace FaceKind

variable {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher} {cell :
  Purelib.Polynomial.Geometry.Grid.ClearGrid.Cell curve.polynomial (Purelib.Curves.Hyperelliptic.Branches.Cuts.Ambient
  curve)}

/-- Read the retained original branch index when this face is ramified. -/
@[expose] def branchIndex? : Curves.Hyperelliptic.Branches.BranchFaceClassification.FaceKind bank cell → Option
  (Data.Index branches)
  | .branch index _ => some index
  | .clear _ => none

/-- The raw normalization is four for one branch and zero otherwise. -/
@[expose] def rawWinding : Curves.Hyperelliptic.Branches.BranchFaceClassification.FaceKind bank cell → Int
  | .branch _ _ => 4
  | .clear _ => 0

/-- The retained branch-or-clear classification gives exactly the original face's raw polynomial winding. -/
theorem rawWinding_eq (member : cell ∈ bank.grid.cells) (kind :
  Curves.Hyperelliptic.Branches.BranchFaceClassification.FaceKind bank cell) :
    kind.rawWinding = Winding.Box.Basic.quadrupledBoxWinding curve.polynomial cell.box := by
  cases kind with
  | branch index equal =>
      change 4 = Winding.Box.Basic.quadrupledBoxWinding curve.polynomial cell.box
      rw [equal]
      exact (BranchCellWinding.selected_winding_four bank index).symm
  | clear unassigned => exact (BranchCellWinding.unassigned_winding_zero bank cell member unassigned).symm

/-- Distinct branch labels cannot classify the same geometric cell. -/
theorem branch_unique {first second : Data.Index branches}
    (firstEq : cell = bank.cell first) (secondEq : cell = bank.cell second) : first = second := by
  by_cases equal : first = second
  · exact equal
  · exact (bank.cells_ne first second equal (firstEq.symm.trans secondEq)).elim

/-- A face equal to an original selected branch cell returns that exact branch index. -/
theorem branchIndex_eq_of_cell_eq (kind : Curves.Hyperelliptic.Branches.BranchFaceClassification.FaceKind bank cell)
  (index : Data.Index branches)
    (equal : cell = bank.cell index) : kind.branchIndex? = some index := by
  cases kind with
  | branch other otherEq =>
      exact congrArg some (Curves.Hyperelliptic.Branches.BranchFaceClassification.FaceKind.branch_unique otherEq equal)
  | clear unassigned => exact (unassigned index equal).elim

end FaceKind

set_option genInjectivity false in
/-- A finite scan retaining either a branch anchor in the original cell or its exclusion for every scanned occurrence.

The original listed index and containment evidence are retained on success. Exhaustion records exclusion at every actual
occurrence of the same finite input list. -/
inductive Scan (bank : Branches.BranchCellBank curve branches higher) (cell : ClearGrid.Cell curve.polynomial
  (Cuts.Ambient curve))
    (indices : List (Data.Index branches))
  /-- Retain the original listed branch occurrence whose cached anchor lies in the cell. -/ | found (index : Data.Index
    branches) (member : index ∈ indices)
      (inside : cell.box.Contains (BranchCellWinding.state bank index).box.anchor)
  /-- Every original listed branch anchor lies outside the cell. -/ | absent (outside : ∀ index ∈ indices,
    ¬cell.box.Contains (BranchCellWinding.state bank index).box.anchor)

constructive_injectivity Scan

open Purelib.Data.List in
/-- Scan the original finite branch-index list by exact containment of cached branch anchors.

Containment is checked in the original list order using each retained branch state anchor. The first accepted occurrence
is kept; exhaustion retains explicit exclusion for the exact scanned list. -/
@[expose] def scan (bank : Branches.BranchCellBank curve branches higher) (cell : ClearGrid.Cell curve.polynomial
  (Cuts.Ambient curve)) :
    (indices : List (Data.Index branches)) → Curves.Hyperelliptic.Branches.BranchFaceClassification.Scan bank cell
      indices
  | [] => .absent (fun _ member => (List.not_mem_nil member).elim)
  | index :: rest =>
      if inside : cell.box.Contains (BranchCellWinding.state bank index).box.anchor then .found index List.mem_cons_self
        inside
      else
        match Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification.scan bank cell rest with
        | .found next member inside => .found next (List.mem_cons_of_mem _ member) inside
        | .absent outside => .absent (fun other member => by
            rcases Membership.mem_cons.mp member with equal | member
            · rw [equal]
              exact inside
            · exact outside other member)

/-- Classify an original grid cell from a complete retained branch-index list and its cached anchor scan. -/
@[expose] def classifyWith (bank : Branches.BranchCellBank curve branches higher)
    (indices : List (Data.Index branches)) (complete : ∀ index, index ∈ indices)
    (cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)) (member : cell ∈ bank.grid.cells) :
      Curves.Hyperelliptic.Branches.BranchFaceClassification.FaceKind bank cell :=
  match Curves.Hyperelliptic.Branches.BranchFaceClassification.scan bank cell indices with
  | .found index _ inside =>
      .branch index (CellSeparation.cells_eq_of_common_point bank.grid (bank.cell_mem index) member
        (BranchCellWinding.anchor_strict_cell bank index) inside).symm
  | .absent outside => .clear (fun index equal => outside index (complete index) (by
      rw [equal]
      exact (BranchCellWinding.anchor_strict_cell bank index).contains))

open Purelib.Data.List in
/-- Total face classification using only cached branch boxes and rational coordinate comparisons. No successful-search
or winding-check input.

The original List.ofFn enumeration supplies every bounded branch index in its retained order. Classification consumes
those same cached branch anchors and preserves the resulting branch witness or clear-face evidence. -/
@[expose] def classify (bank : Branches.BranchCellBank curve branches higher) (cell : ClearGrid.Cell curve.polynomial
  (Cuts.Ambient curve))
    (member : cell ∈ bank.grid.cells) : Curves.Hyperelliptic.Branches.BranchFaceClassification.FaceKind bank cell :=
  Curves.Hyperelliptic.Branches.BranchFaceClassification.classifyWith bank (List.ofFn fun index : Data.Index branches =>
    index)
    (fun index => OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩) cell member

/-- Classifying an original selected branch cell returns its exact branch occurrence. -/
theorem classify_selected (bank : Branches.BranchCellBank curve branches higher) (index : Data.Index branches) :
    (Curves.Hyperelliptic.Branches.BranchFaceClassification.classify bank (bank.cell index) (bank.cell_mem
      index)).branchIndex? = some index :=
  Curves.Hyperelliptic.Branches.BranchFaceClassification.FaceKind.branchIndex_eq_of_cell_eq _ index rfl

set_option genInjectivity false in
/-- One materialized face together with its branch classification.

The original grid-cell membership and branch-or-clear payload refer to that exact retained cell. No replacement face or
branch owner is selected by this record. -/
structure ClassifiedFace (bank : Branches.BranchCellBank curve branches higher) where
  /-- The retained original grid cell being classified. -/ cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)
  /-- The retained cell belongs to the original branch grid. -/ member : cell ∈ bank.grid.cells
  /-- The branch-or-clear certificate for this exact original cell. -/ kind :
    Curves.Hyperelliptic.Branches.BranchFaceClassification.FaceKind bank cell

constructive_injectivity ClassifiedFace

/-- Materialize branch-or-clear certificates in the original cell-list order using one complete branch-index list. -/
@[expose] def classifyCells (bank : Branches.BranchCellBank curve branches higher)
    (indices : List (Data.Index branches)) (complete : ∀ index, index ∈ indices) :
    (cells : List (ClearGrid.Cell curve.polynomial (Cuts.Ambient curve))) → (∀ cell ∈ cells, cell ∈ bank.grid.cells) →
      List (Curves.Hyperelliptic.Branches.BranchFaceClassification.ClassifiedFace bank)
  | [], _ => []
  | cell :: rest, included =>
      ⟨cell, included cell List.mem_cons_self, Curves.Hyperelliptic.Branches.BranchFaceClassification.classifyWith bank
        indices complete cell (included cell List.mem_cons_self)⟩ ::
        Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification.classifyCells bank indices complete rest (fun
          cell member => included cell (List.mem_cons_of_mem _ member))

/-- Reading back cells from the retained classified list gives the exact original cell list. -/
private theorem classifyCells_cells (bank : Branches.BranchCellBank curve branches higher)
    (indices : List (Data.Index branches)) (complete : ∀ index, index ∈ indices)
    (cells : List (ClearGrid.Cell curve.polynomial (Cuts.Ambient curve))) (included : ∀ cell ∈ cells, cell ∈
      bank.grid.cells) :
    (Curves.Hyperelliptic.Branches.BranchFaceClassification.classifyCells bank indices complete cells included).map
      Curves.Hyperelliptic.Branches.BranchFaceClassification.ClassifiedFace.cell = cells := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      change cell :: (Curves.Hyperelliptic.Branches.BranchFaceClassification.classifyCells bank indices complete rest
        _).map Curves.Hyperelliptic.Branches.BranchFaceClassification.ClassifiedFace.cell = cell :: rest
      rw [ih]

open Purelib.Data.List in
/-- Materialize every face once, sharing one finite index list across the scans. Downstream surface construction
consumes this retained data.

One original finite branch-index list is shared by the ordered grid-cell scans. The materialized records retain each
exact cell, its original membership and its selected branch-or-clear evidence. -/
@[expose] def classifiedFaces (bank : Branches.BranchCellBank curve branches higher) : List
  (Curves.Hyperelliptic.Branches.BranchFaceClassification.ClassifiedFace bank) :=
  Curves.Hyperelliptic.Branches.BranchFaceClassification.classifyCells bank (List.ofFn fun index : Data.Index branches
    => index)
    (fun index => OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩) bank.grid.cells (fun _ member => member)

/-- The retained complete classification preserves the exact original grid-cell list. -/
theorem classifiedFaces_cells (bank : Branches.BranchCellBank curve branches higher) :
    (Curves.Hyperelliptic.Branches.BranchFaceClassification.classifiedFaces bank).map
      Curves.Hyperelliptic.Branches.BranchFaceClassification.ClassifiedFace.cell = bank.grid.cells :=
      Curves.Hyperelliptic.Branches.BranchFaceClassification.classifyCells_cells _ _ _ _ _

end Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification
