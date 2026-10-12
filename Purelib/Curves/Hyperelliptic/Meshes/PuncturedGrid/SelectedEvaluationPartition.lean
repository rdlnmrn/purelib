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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders.TwoSheetRequest
open Purelib.Data.Gaussian.Norm.Sum
open Purelib.Data.Rat
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.GridLiftedDualSteps
open Purelib.Riemann.Meshes.PuncturedGridFaces

/-! Exact partition of arbitrary selected side values. Internal pairs use
only retained neighbors; the existing boundary evaluator retains all other sides. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides (value transition split)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders.TwoSheetRequest.SelectedSides
  (boundaryEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition.SelectedSides (physicalEvaluation)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank}

/-- The signed sum of the selected regular-face perimeter values. -/
@[expose] def perimeterEvaluation (keep : Fin faces.regulars.length → Bool)
    (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length → Data.Gaussian.Basic.Canonical) : Gaussian :=
  FiniteSum.Fin.sumFin (fun p => SelectedSides.value (keep p) (values .bottom p + values .right p - values .top p -
    values .left p))

/-- The sum of actual side discrepancies over matching pairs whose two faces are selected. -/
@[expose] def pairSum (keep : Fin faces.regulars.length → Bool)
    (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length → Data.Gaussian.Basic.Canonical) (side :
      GridLiftedDualSteps.GridSide) : Gaussian :=
  FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun last =>
    if side.Matches (faces.regulars[first.val]'first.isLt).cell.box (faces.regulars[last.val]'last.isLt).cell.box then
      SelectedSides.value (keep first && keep last) (values side first - values side.opposite last) else 0))

/-- The signed transition contribution across matching sides with different selection states. -/
private def transitionSum (keep : Fin faces.regulars.length → Bool)
    (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length → Data.Gaussian.Basic.Canonical) (side :
      GridLiftedDualSteps.GridSide) : Gaussian :=
  FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun last =>
    if side.Matches (faces.regulars[first.val]'first.isLt).cell.box (faces.regulars[last.val]'last.isLt).cell.box then
      SelectedSides.transition (keep first) (keep last) (values side first) (values side.opposite last) else 0))

/-- The vertical selected-pair contribution minus the horizontal selected-pair contribution. -/
@[expose] def pairedEvaluation (keep : Fin faces.regulars.length → Bool)
    (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length → Data.Gaussian.Basic.Canonical) : Gaussian :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.pairSum keep values .right -
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.pairSum keep values .top

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides in
/-- Each matching-pair contribution splits into a jointly selected discrepancy and the selection-transition term. -/
private theorem pair_split (keep : Fin faces.regulars.length → Bool)
    (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length → Data.Gaussian.Basic.Canonical) (side :
      GridLiftedDualSteps.GridSide) :
    FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun last =>
      if side.Matches (faces.regulars[first.val]'first.isLt).cell.box (faces.regulars[last.val]'last.isLt).cell.box then
        SelectedSides.value (keep first) (values side first) - SelectedSides.value (keep last) (values side.opposite
          last) else 0)) =
      Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.pairSum keep values side +
        Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.transitionSum keep values side := by
  have pointwise (first last : Fin faces.regulars.length) :
      (if side.Matches (faces.regulars[first.val]'first.isLt).cell.box (faces.regulars[last.val]'last.isLt).cell.box
        then
        SelectedSides.value (keep first) (values side first) - SelectedSides.value (keep last) (values side.opposite
          last) else 0) =
      (if side.Matches (faces.regulars[first.val]'first.isLt).cell.box (faces.regulars[last.val]'last.isLt).cell.box
        then
        SelectedSides.value (keep first && keep last) (values side first - values side.opposite last) else 0) +
      (if side.Matches (faces.regulars[first.val]'first.isLt).cell.box (faces.regulars[last.val]'last.isLt).cell.box
        then
        SelectedSides.transition (keep first) (keep last) (values side first) (values side.opposite last) else 0) := by
    split
    · exact SelectedSides.split ..
    · exact (zero_add _).symm
  rw [FiniteSum.Fin.sumFin_congr (fun first => FiniteSum.Fin.sumFin_congr (pointwise first))]
  simp only [FiniteSum.Fin.sumFin_add, Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.pairSum,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.transitionSum, -eq_self, -iff_self]
  rfl

/-- The selected perimeter evaluation equals the signed difference of its four selected side sums. -/
private theorem side_sum (keep : Fin faces.regulars.length → Bool)
    (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length → Data.Gaussian.Basic.Canonical) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.perimeterEvaluation keep values =
      FiniteSum.Fin.sumFin (fun p => SelectedSides.value (keep p) (values .right p)) - FiniteSum.Fin.sumFin (fun p =>
        SelectedSides.value (keep p) (values .left p)) -
        (FiniteSum.Fin.sumFin (fun p => SelectedSides.value (keep p) (values .top p)) - FiniteSum.Fin.sumFin (fun p =>
          SelectedSides.value (keep p) (values .bottom p))) := by
  have pointwise (p : Fin faces.regulars.length) :
      SelectedSides.value (keep p) (values .bottom p + values .right p - values .top p - values .left p) =
        SelectedSides.value (keep p) (values .right p) - SelectedSides.value (keep p) (values .left p) -
          (SelectedSides.value (keep p) (values .top p) - SelectedSides.value (keep p) (values .bottom p)) := by
    cases keep p <;> simp only [SelectedSides.value, if_neg (by decide : ¬ false = true), if_pos (Eq.refl true),
      -eq_self, -iff_self] <;> ring1
  unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.perimeterEvaluation
  rw [FiniteSum.Fin.sumFin_congr pointwise]
  simp only [FiniteSum.Fin.sumFin_sub, -eq_self, -iff_self]
  rfl

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides in
/-- The selected perimeter evaluation is exactly its internal paired evaluation plus the retained selection boundary.

The original neighbor bank determines internal matches and all physical or discarded-neighbor boundary contributions. -/
theorem perimeter_partition (neighbors : PuncturedFaces.NeighborBank faces)
    (keep : Fin faces.regulars.length → Bool) (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length →
      Data.Gaussian.Basic.Canonical) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.perimeterEvaluation keep values =
      Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.pairedEvaluation keep values +
        SelectedSides.boundaryEvaluation neighbors keep values := by
  have split (side : GridLiftedDualSteps.GridSide) : FiniteSum.Fin.sumFin (fun p => SelectedSides.value (keep p) (values
    side p)) =
      FiniteSum.Fin.sumFin (fun p => SideNeighbor.regularValue (FaceNeighbors.at (neighbors.entries.get p) side)
        (SelectedSides.value (keep p) (values side p))) +
      FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue (FaceNeighbors.at (neighbors.entries.get p) side)
        (SelectedSides.value (keep p) (values side p))) := by
    rw [FiniteSum.Fin.sumFin_congr (fun p => SideNeighbor.value_split (FaceNeighbors.at (neighbors.entries.get p) side)
      (SelectedSides.value (keep p) (values side p))), FiniteSum.Fin.sumFin_add]
  have pairs (side : GridLiftedDualSteps.GridSide) :=
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.pair_split keep values side).symm.trans
    (NeighborBank.pair_sum neighbors side (fun p => SelectedSides.value (keep p) (values side p))
      (fun p => SelectedSides.value (keep p) (values side.opposite p)))
  have vertical := pairs .right
  have horizontal := pairs .top
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.side_sum keep values, split .right, split
    .left, split .top, split .bottom]
  dsimp only [FaceNeighbors.at, GridSide.opposite] at vertical horizontal ⊢
  dsimp only [Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.pairedEvaluation,
    SelectedSides.boundaryEvaluation]
  change _ = Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.pairSum keep values .right -
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.pairSum keep values .top +
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition.SelectedSides.physicalEvaluation neighbors
      keep values + Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.transitionSum keep values
      .right - Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.transitionSum keep values .top)
  have combine {a b c d r l t bot v x vt xt : Data.Gaussian.Basic.Canonical}
      (vEq : v + vt = a - b) (xEq : x + xt = c - d) :
      (a + r) - (b + l) - ((c + t) - (d + bot)) =
        v - x + ((r - l - (t - bot)) + vt - xt) := by
    calc
      _ = (a - b) - (c - d) + (r - l - (t - bot)) := by ring1
      _ = _ := by rw [← vEq, ← xEq]; ring1
  exact combine vertical horizontal

/-- A uniform bound on matching side discrepancies bounds the selected pair sum with the fourth power of the
regular-face count. -/
private theorem pairSum_bound (keep : Fin faces.regulars.length → Bool)
    (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length → Data.Gaussian.Basic.Canonical) (side :
      GridLiftedDualSteps.GridSide) {allowance : Fraction.Rational}
    (nonnegative : 0 ≤ allowance)
    (bounded : ∀ first last, side.Matches (faces.regulars[first.val]'first.isLt).cell.box
      (faces.regulars[last.val]'last.isLt).cell.box →
      Data.Gaussian.Norm.Basic.normSq (values side first - values side.opposite last) ≤ allowance) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.pairSum keep values side) ≤
      (faces.regulars.length : Fraction.Rational)^4 * allowance := by
  have pointwise (first last : Fin faces.regulars.length) :
      Data.Gaussian.Norm.Basic.normSq
        (if side.Matches (faces.regulars[first.val]'first.isLt).cell.box
          (faces.regulars[last.val]'last.isLt).cell.box then SelectedSides.value (keep first && keep last) (values side
            first - values side.opposite last) else 0) ≤ allowance := by
    by_cases matching : side.Matches (faces.regulars[first.val]'first.isLt).cell.box
      (faces.regulars[last.val]'last.isLt).cell.box
    · rw [if_pos matching]
      cases keep first && keep last with
      | true => exact bounded first last matching
      | false =>
          simpa only [SelectedSides.value, if_neg (by decide : ¬ false = true), if_pos (Eq.refl true),
            Data.Gaussian.Norm.Basic.normSq_zero, -eq_self, -iff_self] using nonnegative
    · rw [if_neg matching]
      exact nonnegative
  have rows (first : Fin faces.regulars.length) :=
    Indexed.normSq_sumFin_le _ allowance (pointwise first)
  have total := Indexed.normSq_sumFin_le _
    ((faces.regulars.length : Fraction.Rational)^2 * allowance) rows
  exact total.trans_eq (by ring1)

/-- Uniform horizontal and vertical discrepancy bounds control the complete selected internal evaluation.

The squared-norm estimate pays four times the fourth power of the original regular-face count. -/
theorem pairedEvaluation_bound (keep : Fin faces.regulars.length → Bool)
    (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length → Data.Gaussian.Basic.Canonical) {allowance :
      Fraction.Rational} (nonnegative : 0 ≤ allowance)
    (horizontal : ∀ first last, GridSide.Matches .top (faces.regulars[first.val]'first.isLt).cell.box
      (faces.regulars[last.val]'last.isLt).cell.box →
      Data.Gaussian.Norm.Basic.normSq
        (values .top first - values .bottom last) ≤ allowance)
    (vertical : ∀ first last, GridSide.Matches .right (faces.regulars[first.val]'first.isLt).cell.box
      (faces.regulars[last.val]'last.isLt).cell.box →
      Data.Gaussian.Norm.Basic.normSq
        (values .right first - values .left last) ≤ allowance) :
    Data.Gaussian.Norm.Basic.normSq
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.pairedEvaluation keep values) ≤
      4 * (faces.regulars.length : Fraction.Rational)^4 * allowance := by
  unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.pairedEvaluation
  have right := Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.pairSum_bound keep values .right
    nonnegative vertical
  have top := Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition.pairSum_bound keep values .top
    nonnegative horizontal
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct right top) (by decide : (0 : Fraction.Rational) ≤ 2)).trans_eq (by
        ring1))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition
