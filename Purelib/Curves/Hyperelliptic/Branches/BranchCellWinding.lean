module
import Purelib.Data.Fin
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Grid.Central.Build
import Purelib.Polynomial.Winding.Box.Nonnegative.Squarefree
import Purelib.Polynomial.Winding.Box.Region.Complement
import Purelib.Polynomial.Winding.Box.Region.Selection
import Purelib.Polynomial.Winding.Box.Region.Sum
import Purelib.RootIsolation.Exact.Extraction
import Purelib.RootIsolation.Exact.Ownership.Cardinality
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Count
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Newton.Build

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Polynomial.Geometry.Grid.CellSeparation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.SquareRoot.Grid.Branch.Location
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation

open Purelib.Geometry

open Purelib.Geometry.Rational.Box

open Purelib.Polynomial

open Purelib.Polynomial.Clearance.Box

open Purelib.Polynomial.Elimination.Axis

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Winding.Box

open Purelib.Polynomial.Winding.Box.Grid.Central

open Purelib.Polynomial.Winding.Box.Region

open Purelib.RootIsolation

open Purelib.RootIsolation.Exact

open Purelib.RootIsolation.Exact.Ownership

open Purelib.RootIsolation.State

open Purelib.RootIsolation.State.WindingOne

open Purelib.RootIsolation.Track.Newton

public section

/-!
# Exact winding classification of the common branch grid

The degree-complete branch bank leaves no room for another separated
winding-one state.  An unassigned nonzero-winding face would supply one by
finite extraction.  A selected face with winding exceeding four would supply
one in the eight-cell complement of its retained branch state.  All such
extractions are proof-only; executable classification can use the cached
branch locations instead of recomputing polynomial winding on every face.
-/

namespace Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)
open Purelib.Polynomial.Winding.Box.Basic (quadrupledBoxWinding)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

/-- Reuse the retained small branch state, not a fresh extraction. -/
@[expose] def state (bank : Branches.BranchCellBank curve branches higher) (index : Data.Index branches) :
    WindingOne.Basic.WindingOneState curve.polynomial (Cuts.Ambient curve) := (bank.rows index).location.state

/-- The retained original branch state lies strictly inside its selected grid cell. -/
theorem state_strict_cell (bank : Branches.BranchCellBank curve branches higher) (index : Data.Index branches) :
    (Curves.Hyperelliptic.Branches.BranchCellWinding.state bank index).box.StrictInterior (bank.cell index).box :=
      (bank.rows index).location.strict

/-- The retained original branch anchor lies strictly inside its selected grid cell. -/
theorem anchor_strict_cell (bank : Branches.BranchCellBank curve branches higher) (index : Data.Index branches) :
    (bank.cell index).box.StrictContains (Curves.Hyperelliptic.Branches.BranchCellWinding.state bank index).box.anchor
      :=
  ⟨(Curves.Hyperelliptic.Branches.BranchCellWinding.state_strict_cell bank index).left,
    (Curves.Hyperelliptic.Branches.BranchCellWinding.state bank index).box.x_valid.trans_lt
    (Curves.Hyperelliptic.Branches.BranchCellWinding.state_strict_cell bank index).right,
    (Curves.Hyperelliptic.Branches.BranchCellWinding.state_strict_cell bank index).bottom,
      (Curves.Hyperelliptic.Branches.BranchCellWinding.state bank index).box.y_valid.trans_lt
      (Curves.Hyperelliptic.Branches.BranchCellWinding.state_strict_cell bank index).top⟩

/-- Distinct original branch indices retain positively separated branch-state boxes. -/
theorem states_separated (bank : Branches.BranchCellBank curve branches higher) (first second : Data.Index branches)
    (different : first ≠ second) : (Curves.Hyperelliptic.Branches.BranchCellWinding.state bank first).box.Separated
      (Curves.Hyperelliptic.Branches.BranchCellWinding.state bank second).box :=
  (bank.cells_separated first second different).of_refines
    (Geometry.Rational.Box.Refinement.StrictInterior.refines
        (Curves.Hyperelliptic.Branches.BranchCellWinding.state_strict_cell bank
      first)) (Geometry.Rational.Box.Refinement.StrictInterior.refines
          (Curves.Hyperelliptic.Branches.BranchCellWinding.state_strict_cell
      bank second))

/-- Degree-sharp finite maximality rules out any additional state separated from the entire retained branch bank. The
auxiliary tracks are proof-only.

The original degree-complete bank is extended by the displayed separated state using an explicit successor-index split.
Finite cardinality of those same retained states contradicts the original degree count; no new branch state is selected.
-/
theorem no_additional_state (bank : Branches.BranchCellBank curve branches higher)
    (extra : WindingOne.Basic.WindingOneState curve.polynomial (Cuts.Ambient curve))
    (separated : ∀ index, extra.box.Separated (Curves.Hyperelliptic.Branches.BranchCellWinding.state bank index).box) :
      False := by
  let elimination := Separated.separatedAxisEliminationCertificate curve.polynomial curve.nonzero
    (BranchIsolation.degreePositive curve)
  let states : Fin (branches.siteCount + 1) → WindingOne.Basic.WindingOneState curve.polynomial (Cuts.Ambient curve) :=
    Purelib.Data.Fin.cases extra (Curves.Hyperelliptic.Branches.BranchCellWinding.state bank)
  let family : Fin (branches.siteCount + 1) → Track.Basic.WindingOneTrack curve.polynomial (Cuts.Ambient curve) :=
    fun index => Build.ofInitial higher curve.squarefree elimination (states index)
  have pairwise : ∀ first second, first ≠ second → (family first).initial.box.Separated (family second).initial.box :=
    by
    intro first
    refine Purelib.Data.Fin.cases_induction ?_ (fun first => ?_) first
    · intro second
      refine Purelib.Data.Fin.cases_induction ?_ (fun second => ?_) second
      · intro different
        exact (different rfl).elim
      · intro _
        exact separated second
    · intro second
      refine Purelib.Data.Fin.cases_induction ?_ (fun second => ?_) second
      · intro _
        exact Rational.Box.separated_symm (separated first)
      · intro different
        exact Curves.Hyperelliptic.Branches.BranchCellWinding.states_separated bank first second (fun equal => different
          (congrArg Fin.succ equal))
  have bound := Cardinality.family_card_le_natDegree higher curve.squarefree elimination family pairwise
  have count := branches.count_eq
  omega

/-- Present the original grid cell and its boundary clearance as a clear region in the same ambient box.

The original box, ambient refinement, properness and boundary-clearance fields are retained exactly. This view performs
no extraction, clearance search or branch classification. -/
@[expose] def region (cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)) : Region.ClearRegion curve.polynomial
  (Cuts.Ambient curve) :=
  ⟨cell.box, cell.box_refines, cell.box_proper, cell.boundaryClearance⟩

include higher in
/-- Every original clear grid cell has nonnegative raw winding for the squarefree curve polynomial. -/
theorem winding_nonnegative (cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)) : 0 ≤
  Winding.Box.Basic.quadrupledBoxWinding curve.polynomial cell.box :=
  Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative higher curve.squarefree
    (Separated.separatedAxisEliminationCertificate curve.polynomial curve.nonzero (BranchIsolation.degreePositive
      curve))
    cell.box_refines cell.box_proper cell.boundaryClearance

section
open Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
/-- A cell retaining its original strict interior winding-one state has raw winding at least four. -/
theorem selected_winding_ge_four (bank : Branches.BranchCellBank curve branches higher) (index : Data.Index branches) :
    4 ≤ Winding.Box.Basic.quadrupledBoxWinding curve.polynomial (bank.cell index).box :=
  Count.region_rawWinding_ge_four_of_strictInterior higher curve.squarefree
    (Separated.separatedAxisEliminationCertificate curve.polynomial curve.nonzero (BranchIsolation.degreePositive
      curve))
    (Curves.Hyperelliptic.Branches.BranchCellWinding.state bank index) (region (bank.cell index))
      (Curves.Hyperelliptic.Branches.BranchCellWinding.state_strict_cell bank index)

/-- A face containing no selected branch has exactly zero winding. -/
theorem unassigned_winding_zero (bank : Branches.BranchCellBank curve branches higher) (cell : ClearGrid.Cell
  curve.polynomial (Cuts.Ambient curve))
    (member : cell ∈ bank.grid.cells) (unassigned : ∀ index, cell ≠ bank.cell index) :
    Winding.Box.Basic.quadrupledBoxWinding curve.polynomial cell.box = 0 := by
  by_cases zero : Winding.Box.Basic.quadrupledBoxWinding curve.polynomial cell.box = 0
  · exact zero
  · let raw := (region cell).raw zero
    let extra := BranchIsolation.trackOfRaw curve higher raw
    have strict : extra.initial.box.StrictInterior cell.box := BranchIsolation.trackOfRaw_initial_strict curve higher
      raw
    exact (Curves.Hyperelliptic.Branches.BranchCellWinding.no_additional_state bank extra.initial (fun index =>
      (CellSeparation.cells_interiorSeparated bank.grid member (bank.cell_mem index) (unassigned
        index)).strict_refinements
        strict (Curves.Hyperelliptic.Branches.BranchCellWinding.state_strict_cell bank index))).elim

/-- Each selected face has exactly one branch in the raw normalization. Any positive remainder would extract a forbidden
additional separated state. -/
theorem selected_winding_four (bank : Branches.BranchCellBank curve branches higher) (index : Data.Index branches) :
    Winding.Box.Basic.quadrupledBoxWinding curve.polynomial (bank.cell index).box = 4 := by
  by_cases four : Winding.Box.Basic.quadrupledBoxWinding curve.polynomial (bank.cell index).box = 4
  · exact four
  · let original := Curves.Hyperelliptic.Branches.BranchCellWinding.state bank index
    let cell := bank.cell index
    let complement := Build.build cell.boundaryClearance original.proper
      (Curves.Hyperelliptic.Branches.BranchCellWinding.state_strict_cell bank index)
      (original.ambientLeftClearance.restrict cell.box_refines) (original.ambientRightClearance.restrict
        cell.box_refines)
      (original.ambientBottomClearance.restrict cell.box_refines) (original.ambientTopClearance.restrict
        cell.box_refines)
    let regions := Complement.complementRegions complement cell.box_refines
    have totalPositive : 0 < Region.Sum.totalRaw regions := by
      have additive := Complement.totalRaw_complementRegions complement cell.box_refines
      have lower := Curves.Hyperelliptic.Branches.BranchCellWinding.selected_winding_ge_four bank index
      rw [original.rawWindingFour] at additive
      change Region.Sum.totalRaw regions = Winding.Box.Basic.quadrupledBoxWinding curve.polynomial (bank.cell index).box
        - 4 at additive
      omega
    let elimination := Separated.separatedAxisEliminationCertificate curve.polynomial curve.nonzero
      (BranchIsolation.degreePositive curve)
    have nonnegative : ∀ candidateRegion ∈ regions, 0 ≤ Winding.Box.Basic.quadrupledBoxWinding curve.polynomial
      candidateRegion.box := by
      intro candidateRegion _
      exact Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative higher curve.squarefree elimination
        candidateRegion.refinesAmbient candidateRegion.proper candidateRegion.clearance
    let selected := Selection.selectPositive regions nonnegative totalPositive
    have selectedMember : selected.selected ∈ regions := by
      apply Eq.mpr (congrArg (fun values => selected.selected ∈ values) selected.decomposition)
      exact List.mem_append_right _ List.mem_cons_self
    let extra := Extraction.extractRegion higher curve.squarefree elimination selected.selected selected.positive
    have strict : extra.track.initial.box.StrictInterior cell.box :=
        Geometry.Rational.Box.Refinement.StrictInterior.Boxes.trans_refines
      extra.centerStrict
      (Complement.complementRegions_refine_outer complement cell.box_refines selectedMember)
    apply (Curves.Hyperelliptic.Branches.BranchCellWinding.no_additional_state bank extra.track.initial ?_).elim
    intro other
    by_cases same : index = other
    · subst other
      exact Rational.Box.separated_symm
        (Complement.center_separated_from_complement_strictInterior complement cell.box_refines selectedMember
          extra.centerStrict)
    · exact (CellSeparation.cells_interiorSeparated bank.grid (bank.cell_mem index) (bank.cell_mem other)
        (bank.cells_ne index other same)).strict_refinements strict
          (Curves.Hyperelliptic.Branches.BranchCellWinding.state_strict_cell bank other)

end

/-- Promote the actual grid face to a winding-one state using its retained four line certificates. This performs no root
extraction or new clearance search, and retains the strictly enclosed original branch witness. -/
@[expose] def ramifiedState (bank : Branches.BranchCellBank curve branches higher) (index : Data.Index branches) :
    WindingOne.Basic.WindingOneState curve.polynomial (Cuts.Ambient curve) :=
  let cell := bank.cell index
  { box := cell.box
    refinesAmbient := cell.box_refines
    proper := cell.box_proper
    clearance := cell.boundaryClearance
    rawWindingFour := Curves.Hyperelliptic.Branches.BranchCellWinding.selected_winding_four bank index
    ambientLeftClearance := cell.horizontal.lower.clearance
    ambientRightClearance := cell.horizontal.upper.clearance
    ambientBottomClearance := cell.vertical.lower.clearance
    ambientTopClearance := cell.vertical.upper.clearance }

/-- The original retained branch state remains strictly inside the promoted ramified grid state. -/
theorem ramifiedState_owns (bank : Branches.BranchCellBank curve branches higher) (index : Data.Index branches) :
    (Curves.Hyperelliptic.Branches.BranchCellWinding.state bank index).box.StrictInterior
      (Curves.Hyperelliptic.Branches.BranchCellWinding.ramifiedState bank index).box :=
      Curves.Hyperelliptic.Branches.BranchCellWinding.state_strict_cell bank index

/-- The promoted ramified grid state lies within its original isolated branch box. -/
theorem ramifiedState_refines_original (bank : Branches.BranchCellBank curve branches higher) (index : Data.Index
  branches) :
    (Curves.Hyperelliptic.Branches.BranchCellWinding.ramifiedState bank index).box.Refines (branches.track higher
      index).initial.box := bank.cell_refines_original index

end Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
