module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSideSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Tactic.Ring

public section

/-! Finite bounds for selected interfaces and hole components. The exterior
component remains explicit in the final boundary comparison. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryBounds

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders.TwoSheetRequest

open Purelib.Data.Gaussian.Norm.Sum

open Purelib.Data.Rat

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides (value)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition.SelectedSides
  (outgoingSum interfaceEvaluation boundaryEvaluation_partition)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders.TwoSheetRequest.SelectedSides
  (boundaryEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents (componentEvaluation
  physicalEvaluation_components)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_neg)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {faces : PuncturedFaces bank}

/-- Four squared-norm bounds give a signed four-term bound of sixteen times their common allowance. -/
private theorem four_bound {a b c d : Data.Gaussian.Basic.Canonical} {bound : Fraction.Rational}
    (ha : Data.Gaussian.Norm.Basic.normSq a ≤ bound) (hb : Data.Gaussian.Norm.Basic.normSq b ≤ bound)
    (hc : Data.Gaussian.Norm.Basic.normSq c ≤ bound) (hd : Data.Gaussian.Norm.Basic.normSq d ≤ bound)
      :
    Data.Gaussian.Norm.Basic.normSq (a - b - (c - d)) ≤ 16 * bound := by
  have ab := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two a b).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct ha hb) (by
      decide : (0 : Fraction.Rational) ≤ 2))
  have cd := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two c d).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct hc hd) (by
      decide : (0 : Fraction.Rational) ≤ 2))
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct ab cd) (by
      decide : (0 : Fraction.Rational) ≤ 2)).trans_eq (by ring1))

/-- The selected-to-omitted side sum is bounded by the fourth power of the regular-face count times its pointwise
allowance. -/
private theorem outgoing_bound (keep : Fin faces.regulars.length → Bool)
    (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length → Data.Gaussian.Basic.Canonical) (side :
      GridLiftedDualSteps.GridSide)
    {allowance : Fraction.Rational} (nonnegative : 0 ≤ allowance)
    (bounded : ∀ first last, side.Matches (faces.regulars[first.val]'first.isLt).cell.box
      (faces.regulars[last.val]'last.isLt).cell.box → keep first = true → keep last = false →
      Data.Gaussian.Norm.Basic.normSq (values side first) ≤ allowance) :
    Data.Gaussian.Norm.Basic.normSq (SelectedSides.outgoingSum keep values side) ≤ (faces.regulars.length :
      Fraction.Rational)^4 * allowance := by
  have pointwise (first last : Fin faces.regulars.length) :
      Data.Gaussian.Norm.Basic.normSq (if side.Matches (faces.regulars[first.val]'first.isLt).cell.box
        (faces.regulars[last.val]'last.isLt).cell.box ∧ keep first = true ∧ keep last = false
        then values side first else 0) ≤ allowance := by
    split
    · rename_i present
      exact bounded first last present.1 present.2.1 present.2.2
    · exact nonnegative
  have rows (first : Fin faces.regulars.length) :=
    Indexed.normSq_sumFin_le _ allowance (pointwise first)
  exact (Indexed.normSq_sumFin_le _ _ rows).trans_eq (by ring1)

/-- Uniform bounds on selected-to-omitted sides control the complete regular selection interface. -/
theorem interfaceEvaluation_bound (keep : Fin faces.regulars.length → Bool)
    (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length → Data.Gaussian.Basic.Canonical)
    {allowance : Fraction.Rational} (nonnegative : 0 ≤ allowance)
    (bounded : ∀ side first last, side.Matches (faces.regulars[first.val]'first.isLt).cell.box
      (faces.regulars[last.val]'last.isLt).cell.box → keep first = true → keep last = false →
      Data.Gaussian.Norm.Basic.normSq (values side first) ≤ allowance) :
    Data.Gaussian.Norm.Basic.normSq
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition.SelectedSides.interfaceEvaluation
      keep values) ≤ 16 * (faces.regulars.length : Fraction.Rational)^4 * allowance := by
  have bottom := outgoing_bound keep values .bottom
    nonnegative (bounded .bottom)
  have right := outgoing_bound keep values .right
    nonnegative (bounded .right)
  have top := outgoing_bound keep values .top
    nonnegative (bounded .top)
  have left := outgoing_bound keep values .left
    nonnegative (bounded .left)
  have estimate := four_bound bottom
    ((Data.Gaussian.Norm.Basic.normSq_neg _).trans_le right) top ((Data.Gaussian.Norm.Basic.normSq_neg _).trans_le left)
  have equal : SelectedSides.outgoingSum keep values .bottom - -SelectedSides.outgoingSum keep values .right -
      (SelectedSides.outgoingSum keep values .top - -SelectedSides.outgoingSum keep values .left) =
        SelectedSides.interfaceEvaluation keep values := by
    unfold SelectedSides.interfaceEvaluation
    ring1
  rw [equal] at estimate
  exact estimate.trans_eq (by ring1)

/-- One retained selected hole-neighbor term satisfies its actual matching-side allowance.

The original geometric adjacency selects the supplied hole contribution. An
unselected occurrence or a different component contributes zero, while a
selected adjacent occurrence retains its given squared-norm bound. -/
private theorem hole_term_bound (keep : Fin faces.regulars.length → Bool)
    (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length → Data.Gaussian.Basic.Canonical) (side :
      GridLiftedDualSteps.GridSide)
    (position : Fin faces.regulars.length) (hole : Fin faces.holes.length)
    (neighbor : PuncturedFaces.SideNeighbor faces (faces.regulars[position.val]'position.isLt) side)
    {allowance : Fraction.Rational} (nonnegative : 0 ≤ allowance)
    (bounded : side.Matches (faces.regulars[position.val]'position.isLt).cell.box
      (faces.holes[hole.val]'hole.isLt).cell.box → keep position = true → Data.Gaussian.Norm.Basic.normSq
        (values side position) ≤ allowance) :
    Data.Gaussian.Norm.Basic.normSq (SideNeighbor.componentValue neighbor (.hole hole) (SelectedSides.value
      (keep position) (values side position))) ≤ allowance := by
  rw [HoleSideSelection.SideNeighbor.hole_value_eq]
  by_cases matching : side.Matches (faces.regulars[position.val]'position.isLt).cell.box
      (faces.holes[hole.val]'hole.isLt).cell.box
  · rw [if_pos matching]
    cases selected : keep position with
    | false =>
        rw [SelectedSides.value, if_neg Bool.false_ne_true]
        exact nonnegative
    | true => exact bounded matching selected
  · rw [if_neg matching]
    exact nonnegative

/-- The selected contribution of one original hole is bounded by sixteen times the square of the regular-face count. -/
theorem hole_component_bound (neighbors : PuncturedFaces.NeighborBank faces)
    (keep : Fin faces.regulars.length → Bool) (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length →
      Data.Gaussian.Basic.Canonical)
    (hole : Fin faces.holes.length) {allowance : Fraction.Rational} (nonnegative : 0 ≤ allowance)
    (bounded : ∀ side position, side.Matches (faces.regulars[position.val]'position.isLt).cell.box
      (faces.holes[hole.val]'hole.isLt).cell.box → keep position = true → Data.Gaussian.Norm.Basic.normSq
        (values side position) ≤ allowance) :
    Data.Gaussian.Norm.Basic.normSq (SelectedPhysicalComponents.componentEvaluation neighbors keep values
      (.hole hole)) ≤
      16 * (faces.regulars.length : Fraction.Rational)^2 * allowance := by
  have sides (side : GridLiftedDualSteps.GridSide) := Indexed.normSq_sumFin_le _ allowance
    (fun position => hole_term_bound keep values side
      position hole (FaceNeighbors.at (neighbors.entries.get position) side)
      nonnegative (bounded side position))
  exact (four_bound (sides .right) (sides .left) (sides
    .top) (sides .bottom)).trans_eq (by ring1)

/-- Only the exterior remains after paying all selected hole sides and regular selection interfaces. No physical
component is silently discarded. -/
theorem boundary_sub_exterior_bound (neighbors : PuncturedFaces.NeighborBank faces)
    (keep : Fin faces.regulars.length → Bool) (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length →
      Data.Gaussian.Basic.Canonical)
    {allowance : Fraction.Rational} (nonnegative : 0 ≤ allowance)
    (interfaces : ∀ side first last, side.Matches (faces.regulars[first.val]'first.isLt).cell.box
      (faces.regulars[last.val]'last.isLt).cell.box → keep first = true → keep last = false →
      Data.Gaussian.Norm.Basic.normSq (values side first) ≤ allowance)
    (holes : ∀ (hole : Fin faces.holes.length) side position, side.Matches
      (faces.regulars[position.val]'position.isLt).cell.box
      (faces.holes[hole.val]'hole.isLt).cell.box → keep position = true → Data.Gaussian.Norm.Basic.normSq
        (values side position) ≤ allowance) :
    Data.Gaussian.Norm.Basic.normSq (SelectedSides.boundaryEvaluation neighbors keep values -
      SelectedPhysicalComponents.componentEvaluation neighbors keep values .exterior) ≤
      32 * ((faces.regulars.length : Fraction.Rational)^4 +
        (faces.holes.length : Fraction.Rational)^2 * (faces.regulars.length : Fraction.Rational)^2) * allowance := by
  have interfaceBound := interfaceEvaluation_bound keep
    values nonnegative interfaces
  have holeBound := Indexed.normSq_sumFin_le _ _
    (fun hole => hole_component_bound neighbors keep
      values hole nonnegative (holes hole))
  have equal : SelectedSides.boundaryEvaluation neighbors keep values - SelectedPhysicalComponents.componentEvaluation
    neighbors keep values .exterior =
      SelectedSides.interfaceEvaluation keep values + FiniteSum.Fin.sumFin (fun hole =>
        SelectedPhysicalComponents.componentEvaluation neighbors keep values (.hole hole)) := by
    rw [SelectedSides.boundaryEvaluation_partition, SelectedPhysicalComponents.physicalEvaluation_components]
    ring1
  rw [equal]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      interfaceBound holeBound)
      (by decide : (0 : Fraction.Rational) ≤ 2)).trans_eq (by ring1))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryBounds

end
