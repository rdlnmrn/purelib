module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Riemann.Branches
open Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
open Purelib.Riemann.Normalization

/-!
# Full reciprocal area comparison on a retained boundary side

Concatenate the actual parent traces, including their polygon of totals.
The common request pays both the number of retained parents and every
cross-term; reciprocal cell counts and fine depths may differ by parent.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (Summary pathArea)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive count_mul_perTerm_lt)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover ParentCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests (CoupledLocalAreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests (CoupledParents CoupledRequest)
open Purelib.Riemann.Integration

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

namespace ParentCovers

/-- Take the finite maximum of the original source slope bounds in the retained parent cover bank. -/
@[expose] def sourceSlopeMaximum : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
  UniformReciprocalCover.ParentCovers parents → InverseRootPolynomial.Coordinate
  | _, .nil => 0
  | _, .cons _ data _ tail => max data.sourceSlope
    (sourceSlopeMaximum tail)

/-- The maximum original source slope in a retained parent cover bank is nonnegative. -/
theorem sourceSlopeMaximum_nonnegative {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  (covers : UniformReciprocalCover.ParentCovers parents) :
    0 ≤ (sourceSlopeMaximum covers) := by
  cases covers with
  | nil => exact le_rfl
  | cons _ data _ _ => exact data.sourceSlope_nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)

end ParentCovers

set_option genInjectivity false in
/-- Two local tolerances pay internal areas and the polygon of parent totals separately. The endpoint tolerance is
capped by one to fix a norm bound before constructing any requested polynomial bank. -/
structure SideAreaBudget (slope : InverseRootPolynomial.Coordinate) (count : Nat) (target :
  InverseRootPolynomial.Coordinate) where
  /-- The retained per-parent internal-area error target. -/ areaTarget : InverseRootPolynomial.Coordinate
  /-- The retained per-parent total-increment error target. -/ totalTarget : InverseRootPolynomial.Coordinate
  /-- The retained internal-area target is strictly positive. -/ area_positive : 0 < areaTarget
  /-- The retained total-increment target is strictly positive. -/ total_positive : 0 < totalTarget
  /-- The retained total-increment target is capped by one. -/ total_le_one : totalTarget ≤ 1
  /-- The two retained tolerances pay all original parent-count and area cross-term factors. -/ paid : 2 * ((count :
    InverseRootPolynomial.Coordinate) ^ 2 * areaTarget +
    16 * (count : InverseRootPolynomial.Coordinate) ^ 4 * totalTarget * (2 * (slope + 1))) < target

constructive_injectivity SideAreaBudget

namespace SideAreaBudget

/-- Select positive local area and total tolerances paying the exact original parent count, source ceiling and side
target. -/
@[expose] def build (slope : InverseRootPolynomial.Coordinate) (nonnegative : 0 ≤ slope) (count : Nat) (target :
  InverseRootPolynomial.Coordinate)
    (positive : 0 < target) : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.SideAreaBudget slope count
      target := by
  let inner := target / (128 * (slope + 1))
  have shifted : 0 < slope + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct nonnegative (by decide)
  have innerPositive : 0 < inner := Fraction.Order.Field.div_pos_direct positive
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel) shifted)
  let areaTarget := Aggregate.perTerm (target / 4) count
  let totalTarget := min 1 (Aggregate.perTerm (Aggregate.perTerm inner count) count)
  have totalPositive : 0 < totalTarget := Fraction.Order.Basic.lt_min (by decide) (Aggregate.perTerm_positive
    (Aggregate.perTerm_positive innerPositive _) _)
  refine ⟨areaTarget, totalTarget, Aggregate.perTerm_positive (Fraction.Order.Field.div_pos_direct positive (by decide))
    _,
    totalPositive, Fraction.Order.Basic.min_le_left _ _, ?_⟩
  have squareNonnegative : (0 : InverseRootPolynomial.Coordinate) ≤ (count : InverseRootPolynomial.Coordinate) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  have innerPaid : (count : InverseRootPolynomial.Coordinate) ^ 4 * totalTarget < inner := by
    have firstPaid : (count : InverseRootPolynomial.Coordinate) ^ 2 * Aggregate.perTerm (Aggregate.perTerm inner count)
      count < Aggregate.perTerm inner count := by
      simpa only [pow_two, Fraction.Field.mul_assoc, -eq_self, -iff_self] using Aggregate.count_mul_perTerm_lt
        (Aggregate.perTerm_positive innerPositive count) count
    have first : (count : InverseRootPolynomial.Coordinate) ^ 2 * totalTarget ≤ Aggregate.perTerm inner count :=
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_right _ _)
        squareNonnegative).trans
        firstPaid.le
    calc
      _ = (count : InverseRootPolynomial.Coordinate) ^ 2 * ((count : InverseRootPolynomial.Coordinate) ^ 2 *
        totalTarget) := by
        ring1
      _ ≤ (count : InverseRootPolynomial.Coordinate) ^ 2 * Aggregate.perTerm inner count :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct first squareNonnegative
      _ < inner := by
        simpa only [pow_two, Fraction.Field.mul_assoc, -eq_self, -iff_self] using Aggregate.count_mul_perTerm_lt
          innerPositive count
  have internal : 2 * ((count : InverseRootPolynomial.Coordinate) ^ 2 * areaTarget) < target / 2 := by
    have paid : (count : InverseRootPolynomial.Coordinate) ^ 2 * areaTarget < target / 4 := by
      simpa only [pow_two, Fraction.Field.mul_assoc, -eq_self, -iff_self] using Aggregate.count_mul_perTerm_lt
        (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : InverseRootPolynomial.Coordinate) < 4)) count
    apply (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : InverseRootPolynomial.Coordinate) < 2) paid).trans_eq
    apply Fraction.Field.mul_right_cancel_of_ne (by decide : (4 : InverseRootPolynomial.Coordinate) ≠ 0)
    calc
      _ = 2 * ((target / 4) * 4) := by ring1
      _ = 2 * target := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
      _ = (target / 2) * 4 := by
        rw [show (target / 2) * 4 = ((target / 2) * 2) * 2 by ring1, Fraction.Field.div_mul_cancel_of_ne _ _ (by
          decide)]
        ring1
  have polygon : 64 * (slope + 1) * ((count : InverseRootPolynomial.Coordinate) ^ 4 * totalTarget) < target / 2 := by
    apply (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (Fraction.Order.Arithmetic.mul_pos_direct
      (by decide +kernel) shifted) innerPaid).trans_eq
    apply Fraction.Field.mul_right_cancel_of_ne (by decide : (2 : InverseRootPolynomial.Coordinate) ≠ 0)
    calc
      _ = inner * (128 * (slope + 1)) := by ring1
      _ = target := Fraction.Field.div_mul_cancel_of_ne _ _ (Fraction.Order.Arithmetic.mul_pos_direct
        (by decide +kernel) shifted).ne'
      _ = (target / 2) * 2 := (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)).symm
  calc
    _ = 2 * ((count : InverseRootPolynomial.Coordinate) ^ 2 * areaTarget) +
      64 * (slope + 1) * ((count : InverseRootPolynomial.Coordinate) ^ 4 * totalTarget) := by ring1
    _ < target / 2 + target / 2 := Fraction.Order.Arithmetic.add_lt_add_direct internal polygon
    _ = target := (by ring1 : target / 2 + target / 2 = (target / 2) * 2).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

end SideAreaBudget

set_option genInjectivity false in
/-- Coupled source, reciprocal and area requests on the original retained parent covers.

Each occurrence keeps its own reciprocal mesh and actual source request while sharing the caller's budgets and stage
floors. -/
inductive CoupledAreaParents (sourceTarget reciprocalTarget coefficientTarget areaTarget totalTarget :
  InverseRootPolynomial.Coordinate)
    (minimum depth : Nat) : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
      UniformReciprocalCover.ParentCovers parents → Type 2
  /-- The empty original parent cover bank retains no area requests. -/ | nil :
    CoupledAreaParents sourceTarget reciprocalTarget
    coefficientTarget areaTarget totalTarget minimum depth .nil
  /-- Retain the original head cover's coupled area request and the exact remaining parent-cover tail. -/ | cons {parent
    : PreparedSubdivisionModelCore.CenteredEdge curve differential} {remaining : List
    (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
      {patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data : UniformReciprocalModels.Data patch
        genus} {cover : UniformReciprocalCover.Cover data} {tail : UniformReciprocalCover.ParentCovers remaining}
      (head : PreparedReciprocalAreaRequests.CoupledLocalAreaRequest cover sourceTarget reciprocalTarget
        coefficientTarget areaTarget totalTarget minimum depth)
      (rest : CoupledAreaParents sourceTarget
        reciprocalTarget coefficientTarget areaTarget totalTarget minimum depth tail) :
        CoupledAreaParents sourceTarget
          reciprocalTarget coefficientTarget areaTarget totalTarget minimum depth (.cons patch data cover tail)

constructive_injectivity CoupledAreaParents

namespace CoupledAreaParents

variable {sourceTarget reciprocalTarget coefficientTarget areaTarget totalTarget :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum depth : Nat}

/-- Request each original proper parent cover with the common positive budgets and retained stage floors. -/
@[expose] def build (sourceTarget reciprocalTarget coefficientTarget areaTarget totalTarget :
  InverseRootPolynomial.Coordinate)
    (sourcePositive : 0 < sourceTarget) (reciprocalPositive : 0 < reciprocalTarget) (coefficientPositive : 0 <
      coefficientTarget)
    (areaPositive : 0 < areaTarget) (totalPositive : 0 < totalTarget) (minimum depth : Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → (covers :
      UniformReciprocalCover.ParentCovers parents) →
    PreparedDyadicRefinements.AllParentsProper parents →
      Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.CoupledAreaParents sourceTarget reciprocalTarget
        coefficientTarget areaTarget totalTarget minimum depth covers
  | _, .nil, _ => .nil
  | _, .cons _ _ cover tail, proper =>
      .cons (CoupledLocalAreaRequest.build cover _ _ _ _ _ sourcePositive reciprocalPositive coefficientPositive
        areaPositive totalPositive proper.1 minimum depth)
        (build _ _ _ _ _
          sourcePositive reciprocalPositive coefficientPositive areaPositive totalPositive minimum depth tail proper.2)

/-- Project the original controlled primitive requests from the retained area request bank. -/
@[expose] def compared : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.CoupledAreaParents sourceTarget reciprocalTarget
      coefficientTarget areaTarget totalTarget minimum depth covers →
      PreparedReciprocalControlledRequests.CoupledParents sourceTarget reciprocalTarget coefficientTarget minimum covers
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons head.compared tail.compared

/-- Read the original paired source and reciprocal increment paths in retained parent order. -/
@[expose] def pairs : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.CoupledAreaParents sourceTarget reciprocalTarget
      coefficientTarget areaTarget totalTarget minimum depth covers →
      List (List InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  | _, _, .nil => []
  | _, _, .cons head tail =>
      ((head.area.cells.pairs.map Prod.fst).flatten, (head.area.cells.pairs.map Prod.snd).flatten) :: tail.pairs

/-- There is exactly one retained path pair for every original parent. -/
theorem pairs_length {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.CoupledAreaParents sourceTarget
      reciprocalTarget coefficientTarget areaTarget totalTarget minimum depth covers) :
    requests.pairs.length = parents.length := by
  induction requests with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- Combine the cached source summaries in original parent order, retaining their actual concatenated path. -/
@[expose] def leftSummary : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.CoupledAreaParents sourceTarget
      reciprocalTarget coefficientTarget areaTarget totalTarget minimum depth covers) →
      IncrementArea.Summary (requests.pairs.map Prod.fst).flatten
  | _, _, .nil => IncrementArea.Summary.build []
  | _, _, .cons head tail => head.area.left.append tail.leftSummary

/-- Combine the cached reciprocal summaries in original parent order, retaining their actual concatenated path. -/
@[expose] def rightSummary : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.CoupledAreaParents sourceTarget
      reciprocalTarget coefficientTarget areaTarget totalTarget minimum depth covers) →
      IncrementArea.Summary (requests.pairs.map Prod.snd).flatten
  | _, _, .nil => IncrementArea.Summary.build []
  | _, _, .cons head tail => head.area.right.append tail.rightSummary

/-- The combined source summary reads back the original retained source increment sum. -/
theorem left_total {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.CoupledAreaParents sourceTarget
      reciprocalTarget coefficientTarget areaTarget totalTarget minimum depth covers) :
    requests.leftSummary.total = Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.compared.source.increments := by
  induction requests with
  | nil => rfl
  | cons head tail ih =>
      change head.area.left.total + tail.leftSummary.total = (LocalRequest.increment head.compared.source.localRequest)
        + _
      rw [head.left_total_eq, ih, head.compared.source_eq]

/-- The combined reciprocal summary reads back the original retained reciprocal increment sum. -/
theorem right_total {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.CoupledAreaParents sourceTarget
      reciprocalTarget coefficientTarget areaTarget totalTarget minimum depth covers) :
    requests.rightSummary.total = Data.Gaussian.Norm.Sum.Basic.gaussianSum
      requests.compared.reciprocal.reciprocalValues := by
  induction requests with
  | nil => rfl
  | cons head tail ih =>
      change head.area.right.total + tail.rightSummary.total = head.compared.reciprocal.reciprocalIncrement + _
      rw [head.right_total_eq, ih]

/-- Each retained path pair satisfies its internal area and total discrepancy budgets and the common original slope
ceiling. -/
private theorem bounds {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.CoupledAreaParents sourceTarget
      reciprocalTarget coefficientTarget areaTarget totalTarget minimum depth covers)
    (totalSmall : totalTarget ≤ 1) {slope : InverseRootPolynomial.Coordinate} (slopeNonnegative : 0 ≤ slope)
    (slopeLe : (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.ParentCovers.sourceSlopeMaximum covers) ≤
      slope) :
    ∀ pair ∈ requests.pairs,
      Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea pair.1 - IncrementArea.pathArea pair.2) ≤
        areaTarget ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ totalTarget ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1) ≤ 2 * (slope + 1)
        ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ 2 * (slope + 1)
        := by
  induction requests with
  | nil => intro _ member; exact False.elim (List.not_mem_nil member)
  | @cons parent remaining patch data cover tail head rest ih =>
      intro pair member
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst pair
        change Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea (head.area.cells.pairs.map
          Prod.fst).flatten - IncrementArea.pathArea (head.area.cells.pairs.map Prod.snd).flatten) ≤ _ ∧ _
        rw [← head.area.left.area_eq, ← head.area.right.area_eq, ← head.area.left.total_eq, ← head.area.right.total_eq]
        have totalBound : Data.Gaussian.Norm.Basic.normSq (head.area.left.total - head.area.right.total) ≤
          totalTarget := by
          rw [head.left_total_eq, head.right_total_eq]
          exact head.compared.reciprocal.close.trans head.total_accurate.le
        have leftBound : Data.Gaussian.Norm.Basic.normSq head.area.left.total ≤ slope := by
          have sourceBound := head.area.source.increment_bound (first := 0) (last := 1)
            ⟨le_rfl, by decide⟩ ⟨by decide, le_rfl⟩
          rw [← head.area.source_total] at sourceBound
          have localBound : Data.Gaussian.Norm.Basic.normSq head.area.left.total ≤ data.sourceSlope :=
            sourceBound.trans_eq (by ring1)
          exact localBound.trans ((Fraction.Order.Basic.le_max_left _ _).trans slopeLe)
        have expanded : slope ≤ 2 * (slope + 1) :=
          (le_add_of_nonneg_right (show (0 : InverseRootPolynomial.Coordinate) ≤ 1 by decide)).trans
            ((le_add_of_nonneg_right (add_nonneg slopeNonnegative (show (0 : InverseRootPolynomial.Coordinate) ≤ 1 by
              decide))).trans_eq (by ring1))
        refine ⟨head.area.close.trans head.area.error_lt.le, totalBound, leftBound.trans expanded, ?_⟩
        have identity : head.area.right.total = head.area.left.total + -(head.area.left.total - head.area.right.total)
          := by ring1
        have estimate := Data.Gaussian.Norm.Bounds.normSq_add_le_two head.area.left.total (-(head.area.left.total -
          head.area.right.total))
        rw [← identity, Data.Gaussian.Norm.Basic.normSq_neg] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add leftBound (totalBound.trans totalSmall)) (by decide))
      · exact ih ((Fraction.Order.Basic.le_max_right _ _).trans slopeLe) pair member

/-- The complete side includes the area of all parent-total cross-terms. Every parent may have its own reciprocal mesh;
no common cell count is used. -/
theorem whole_area_error {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    {target : InverseRootPolynomial.Coordinate} (budget :
      Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.SideAreaBudget
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.ParentCovers.sourceSlopeMaximum covers) parents.length
      target)
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.CoupledAreaParents sourceTarget
      reciprocalTarget coefficientTarget budget.areaTarget budget.totalTarget minimum depth covers) :
    Data.Gaussian.Norm.Basic.normSq (requests.leftSummary.area - requests.rightSummary.area) < target := by
  have bounded := requests.bounds budget.total_le_one
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.ParentCovers.sourceSlopeMaximum_nonnegative covers)
    le_rfl
  rw [requests.leftSummary.area_eq, requests.rightSummary.area_eq]
  have estimate := IncrementAreaComparison.blocks_area_difference_bound requests.pairs budget.total_positive.le
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.ParentCovers.sourceSlopeMaximum_nonnegative
        covers) (by decide)))
    (fun pair member => (bounded pair member).1) (fun pair member => (bounded pair member).2.1)
    (fun pair member => (bounded pair member).2.2.1) (fun pair member => (bounded pair member).2.2.2)
  rw [requests.pairs_length] at estimate
  exact estimate.trans_lt budget.paid

end CoupledAreaParents

set_option genInjectivity false in
/-- A full side area trace and an actual controlled prepared request built from precisely the same local banks. Cached
summaries retain their literal paths and exact integral readbacks. -/
structure CoupledAreaRequest {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} (covers :
  UniformReciprocalCover.ParentCovers parents)
    (sourceTarget reciprocalTarget areaTarget : InverseRootPolynomial.Coordinate) (minimum depth : Nat) where
  /-- The original source integration target is strictly positive. -/ source_positive : 0 < sourceTarget
  /-- The original reciprocal comparison target is strictly positive. -/ reciprocal_positive : 0 < reciprocalTarget
  /-- The retained side-area budget accounts for the exact original parent count and maximum slope. -/ budget :
    SideAreaBudget
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.ParentCovers.sourceSlopeMaximum covers) parents.length
    areaTarget
  /-- The coupled requests on the original parent cover bank with their exact paid local tolerances. -/ requests :
    CoupledAreaParents (Aggregate.perTerm sourceTarget
    parents.length) (Aggregate.perTerm reciprocalTarget parents.length)
    ((sourceTarget / 2) / (PreparedRefinementMovement.movementMass parents + 1)) budget.areaTarget budget.totalTarget
      minimum depth covers
  /-- The cached controlled primitive comparison sharing these exact original parent requests. -/ compared :
    PreparedReciprocalControlledRequests.CoupledRequest covers sourceTarget reciprocalTarget minimum
  /-- The cached controlled comparison is built from these same retained parent requests. -/ compared_eq : compared =
    CoupledRequest.ofRequests covers sourceTarget reciprocalTarget source_positive reciprocal_positive minimum
    requests.compared
  /-- The cached area and total summary of the concatenated original source paths. -/ left : IncrementArea.Summary
    (requests.pairs.map Prod.fst).flatten
  /-- The cached area and total summary of the concatenated original reciprocal paths. -/ right : IncrementArea.Summary
    (requests.pairs.map Prod.snd).flatten
  /-- The cached source total is the original controlled request's retained primitive sum. -/ left_total_eq : left.total
    = compared.source.primitiveSum
  /-- The cached reciprocal total is the original controlled request's retained reciprocal integral. -/ right_total_eq :
    right.total = compared.reciprocal.reciprocalIntegral
  /-- The cached full side areas differ by less than the original requested area target. -/ close :
    Data.Gaussian.Norm.Basic.normSq (left.area - right.area) < areaTarget

constructive_injectivity CoupledAreaRequest

namespace CoupledAreaRequest

/-- Prepare the full original side once, retaining its coupled comparisons, literal paths and paid area summaries. -/
@[expose] def build {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} (covers :
  UniformReciprocalCover.ParentCovers parents)
    (proper : PreparedDyadicRefinements.AllParentsProper parents) (sourceTarget reciprocalTarget areaTarget :
      InverseRootPolynomial.Coordinate)
    (sourcePositive : 0 < sourceTarget) (reciprocalPositive : 0 < reciprocalTarget) (areaPositive : 0 < areaTarget)
    (minimum depth : Nat) : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.CoupledAreaRequest covers
      sourceTarget reciprocalTarget areaTarget minimum depth := by
  let budget := Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.SideAreaBudget.build
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.ParentCovers.sourceSlopeMaximum covers)
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.ParentCovers.sourceSlopeMaximum_nonnegative covers)
    parents.length areaTarget areaPositive
  let requests := Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.CoupledAreaParents.build (Aggregate.perTerm
    sourceTarget parents.length) (Aggregate.perTerm reciprocalTarget parents.length)
    ((sourceTarget / 2) / (PreparedRefinementMovement.movementMass parents + 1)) budget.areaTarget budget.totalTarget
    (Aggregate.perTerm_positive sourcePositive _) (Aggregate.perTerm_positive reciprocalPositive _)
    (Fraction.Order.Field.div_pos_direct (Fraction.Order.Field.div_pos_direct sourcePositive (by decide))
      (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (PreparedRefinementMovement.movementMass_nonnegative
        parents) (by decide)))
    budget.area_positive budget.total_positive minimum depth covers proper
  let compared := CoupledRequest.ofRequests covers sourceTarget reciprocalTarget sourcePositive reciprocalPositive
    minimum requests.compared
  refine ⟨sourcePositive, reciprocalPositive, budget, requests, compared, rfl,
    requests.leftSummary, requests.rightSummary, ?_, requests.right_total, requests.whole_area_error budget⟩
  exact requests.left_total

variable {parents : List (CenteredEdge curve differential)}
  {covers : ParentCovers parents}
  {sourceTarget reciprocalTarget areaTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum
    depth : Nat}

/-- Moving both traces to the same primitive origin retains its endpoint correction. The final increments need not agree
or vanish. -/
theorem trace_error (request : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.CoupledAreaRequest covers
  sourceTarget reciprocalTarget areaTarget minimum depth)
    (start : InverseRootPolynomial.Gaussian) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.traceArea start (request.requests.pairs.map
      Prod.fst).flatten -
      IncrementArea.traceArea start (request.requests.pairs.map Prod.snd).flatten) <
        2 * (areaTarget + 4 * Data.Gaussian.Norm.Basic.normSq start * reciprocalTarget) := by
  rw [IncrementArea.traceArea_eq, IncrementArea.traceArea_eq,
    ← request.left.area_eq, ← request.right.area_eq, ← request.left.total_eq, ← request.right.total_eq]
  have identity : request.left.area + BoundaryRibbon.area start request.left.total -
      (request.right.area + BoundaryRibbon.area start request.right.total) =
      (request.left.area - request.right.area) + BoundaryRibbon.area start (request.left.total - request.right.total) :=
        by
    apply Data.Gaussian.Basic.ext <;> simp only [BoundaryRibbon.area, Data.Gaussian.Basic.conj,
      Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, -eq_self, -iff_self] <;> ring1
  rw [identity]
  have totalBound : Data.Gaussian.Norm.Basic.normSq (request.left.total - request.right.total) ≤
    reciprocalTarget := by
    rw [request.left_total_eq, request.right_total_eq, request.compared.source_eq]
    exact request.compared.reciprocal.close.trans request.compared.reciprocal.error_lt.le
  have endpointBound : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area start (request.left.total -
    request.right.total)) ≤
      4 * Data.Gaussian.Norm.Basic.normSq start * reciprocalTarget :=
    (BoundaryRibbon.area_bound _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totalBound
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg start)))
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add le_rfl endpointBound) (by decide)).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
        (Fraction.Order.Arithmetic.add_lt_add_right_direct request.close _)))

end CoupledAreaRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
