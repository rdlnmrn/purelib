module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Riemann.Normalization

/-!
# Full area and total comparison across the synchronized exterior side

Each retained parent's internal path and every cross term between parent
totals are included. The fixed parent count is paid before any additional
fine subdivision, and the original controlled source bank is preserved.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSideEstimates

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (pathArea)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank (Requests Evaluations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides (Plans Results)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
    Coordinate} {minimum index depth readingIndex : Nat}
  {box : Purelib.Geometry.Rational.Box} {sample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {parents : List (CenteredEdge curve differential)} {covers :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
  {prepared : SideBank regular covers} {requests :
    Requests sourceTarget reciprocalTarget
    coefficientTarget totalTarget areaTarget minimum prepared}

  {plans : Plans requests} {evaluated :
    Evaluations sample depth readingIndex
    requests}

/-- The retained regular-side source summary reads exactly the original evaluated source total. -/
theorem source_total_eq (results : RegularSides.Results plans evaluated) : results.leftSummary.total =
  evaluated.leftSummary.total := by
  rw [results.leftSummary.total_eq, Results.source_paths results, evaluated.leftSummary.total_eq]

/-- The retained regular-side source summary reads exactly the original evaluated source area. -/
theorem source_area_eq (results : RegularSides.Results plans evaluated) : results.leftSummary.area =
  evaluated.leftSummary.area := by
  rw [results.leftSummary.area_eq, Results.source_paths results, evaluated.leftSummary.area_eq]

/-- Every actual parent-path pair satisfies the retained area and total errors and the common source-slope magnitude
ceiling. -/
theorem bounds (results : RegularSides.Results plans evaluated) (totalSmall : totalTarget ≤ 1)
    {slope : InverseRootPolynomial.Coordinate} (slopeNonnegative : 0 ≤ slope) (slopeLe :
      (ParentCovers.sourceSlopeMaximum covers) ≤ slope) :
    ∀ pair ∈ results.pairs,
      Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea pair.1 - IncrementArea.pathArea pair.2) ≤
        areaTarget ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ totalTarget ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1) ≤ 2 * (slope + 1)
        ∧ Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ 2 * (slope +
        1) := by
  induction evaluated with
  | nil => intro _ member; exact False.elim (List.not_mem_nil member)
  | @cons parent remaining patch data cover covers prepared tail request requests head rest ih =>
      intro pair member
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst pair
        rw [← results.1.left.area_eq, ← results.1.cap.area_eq,
          ← results.1.left.total_eq, ← results.1.cap.total_eq]
        have areaBound := results.1.area_close.le
        have totalBound := results.1.total_close.le
        have leftBound : Data.Gaussian.Norm.Basic.normSq results.1.left.total ≤ slope := by
          have bounded := head.original.area.source.increment_bound (first := 0) (last := 1)
            ⟨le_rfl, by decide⟩ ⟨by decide, le_rfl⟩
          rw [← results.1.source_total] at bounded
          have localBound : Data.Gaussian.Norm.Basic.normSq results.1.left.total ≤ data.sourceSlope :=
            bounded.trans_eq (by ring1)
          exact localBound.trans ((Fraction.Order.Basic.le_max_left _ _).trans slopeLe)
        have expanded : slope ≤ 2 * (slope + 1) :=
          (le_add_of_nonneg_right (show (0 : InverseRootPolynomial.Coordinate) ≤ 1 by decide)).trans
            ((le_add_of_nonneg_right (add_nonneg slopeNonnegative (show (0 : InverseRootPolynomial.Coordinate) ≤ 1 by
              decide))).trans_eq (by ring1))
        refine ⟨areaBound, totalBound, leftBound.trans expanded, ?_⟩
        have identity : results.1.cap.total =
            results.1.left.total + -(results.1.left.total - results.1.cap.total) := by ring1
        have estimate := Data.Gaussian.Norm.Bounds.normSq_add_le_two results.1.left.total (-(results.1.left.total -
          results.1.cap.total))
        rw [← identity, Data.Gaussian.Norm.Basic.normSq_neg] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add leftBound (totalBound.trans totalSmall)) (by decide))
      · exact ih results.2 ((Fraction.Order.Basic.le_max_right _ _).trans slopeLe) pair member

/-- The sum of actual paired path-total differences equals the difference of their complete flattened totals. -/
private theorem sum_errors (pairs : List (List InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum
      pair.1 - Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map Prod.fst).flatten -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map Prod.snd).flatten := by
  induction pairs with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | cons pair pairs ih =>
      simp only [List.map_cons, List.flatten_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
        IncrementArea.sum_append, ih, -eq_self, -iff_self]
      ring1

/-- The complete actual side-total error is bounded by the original parent count squared times the retained local total
target. -/
theorem total_error (results : RegularSides.Results plans evaluated) (totalSmall : totalTarget ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (results.leftSummary.total - results.capSummary.total) ≤
      (parents.length : InverseRootPolynomial.Coordinate) * ((parents.length : InverseRootPolynomial.Coordinate) *
        totalTarget) := by
  have bounded := bounds results totalSmall
    (ParentCovers.sourceSlopeMaximum_nonnegative covers) le_rfl
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (results.pairs.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2)) totalTarget (by
      intro value member
      obtain ⟨pair, member, same⟩ := Map.mem_map.mp member
      rw [← same]
      exact (bounded pair member).2.1)
  rw [Data.List.Map.length_map, results.pairs_length,
    sum_errors, ← results.leftSummary.total_eq, ←
    results.capSummary.total_eq] at estimate
  exact estimate

/-- The complete actual side-area error includes both local parent areas and all cross terms, bounded using the fixed
original parent count and source-slope maximum. -/
theorem area_error (results : RegularSides.Results plans evaluated) (totalSmall : totalTarget ≤ 1)
    (totalNonnegative : 0 ≤ totalTarget) :
    Data.Gaussian.Norm.Basic.normSq (results.leftSummary.area - results.capSummary.area) ≤
      2 * ((parents.length : InverseRootPolynomial.Coordinate) ^ 2 * areaTarget + 16 * (parents.length :
        InverseRootPolynomial.Coordinate) ^ 4 * totalTarget *
        (2 * ((ParentCovers.sourceSlopeMaximum covers) + 1))) := by
  have bounded := bounds results totalSmall
    (ParentCovers.sourceSlopeMaximum_nonnegative covers) le_rfl
  have estimate := IncrementAreaComparison.blocks_area_difference_bound results.pairs totalNonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (ParentCovers.sourceSlopeMaximum_nonnegative covers) (by decide)))
    (fun pair member => (bounded pair member).1) (fun pair member => (bounded pair member).2.1)
    (fun pair member => (bounded pair member).2.2.1) (fun pair member => (bounded pair member).2.2.2)
  rw [results.pairs_length, ← results.leftSummary.area_eq, ← results.capSummary.area_eq] at estimate
  exact estimate

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSideEstimates
