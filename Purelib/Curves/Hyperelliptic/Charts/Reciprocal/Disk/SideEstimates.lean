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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
open Purelib.Riemann.Normalization

/-!
# Full area and total comparison across the synchronized exterior side

Each retained parent's internal path and every cross term between parent
totals are included. The fixed parent count is paid before any additional
fine subdivision, and the original controlled source bank is preserved.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEstimates

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (pathArea)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank (Requests Evaluations)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap}
  {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
    Coordinate} {minimum index depth readingIndex : Nat}
  {box : Geometry.Rational.Box} {sample :
    Cap.Primitives.Sample cap differential index box}
  {parents : List (CenteredEdge curve differential)} {covers :
    UniformReciprocalCover.ParentCovers parents}
  {prepared : SideBank regular covers} {requests :
    Requests sourceTarget reciprocalTarget
    coefficientTarget totalTarget areaTarget minimum prepared}

/-- The retained left summary reads back the exact increment sum of the original controlled source bank. -/
theorem source_total (evaluated : Evaluations sample depth readingIndex requests) :
    evaluated.leftSummary.total = gaussianSum
      evaluated.originals.compared.source.increments := by
  induction evaluated with
  | nil => rfl
  | cons head tail ih =>
      change head.original.area.left.total + tail.leftSummary.total = LocalRequest.increment
        head.original.compared.source.localRequest + _
      rw [head.original.left_total_eq, ih, head.original.compared.source_eq]

/-- The complete retained left paths are exactly the original prepared source paths. -/
theorem source_paths (evaluated : Evaluations sample depth readingIndex requests) :
    (evaluated.pairs.map Prod.fst).flatten = (evaluated.originals.pairs.map Prod.fst).flatten := by
  induction evaluated with
  | nil => rfl
  | cons head tail ih =>
      change _ ++ (tail.pairs.map Prod.fst).flatten = _ ++ (tail.originals.pairs.map Prod.fst).flatten
      rw [ih]

/-- Each actual retained parent pair satisfies the requested area and total errors and the common source-slope magnitude
ceiling. -/
theorem bounds (evaluated : Evaluations sample depth readingIndex requests) (totalSmall : totalTarget ≤ 1)
    {slope : Coordinate} (slopeNonnegative : 0 ≤ slope) (slopeLe : ParentCovers.sourceSlopeMaximum
      covers ≤ slope) :
    ∀ pair ∈ evaluated.pairs,
      Basic.normSq (pathArea pair.1 - pathArea pair.2) ≤
        areaTarget ∧
      Basic.normSq (gaussianSum pair.1 -
        gaussianSum pair.2) ≤ totalTarget ∧
      Basic.normSq (gaussianSum pair.1) ≤ 2 * (slope + 1)
        ∧ Basic.normSq (gaussianSum pair.2) ≤ 2 * (slope +
        1) := by
  induction evaluated with
  | nil => intro _ member; exact False.elim (List.not_mem_nil member)
  | @cons parent remaining patch data cover covers prepared tail request requests head rest ih =>
      intro pair member
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst pair
        rw [← head.original.area.left.area_eq, ← head.cap.joined.summary.area_eq,
          ← head.original.area.left.total_eq, ← head.cap.joined.summary.total_eq]
        have areaBound := head.cap.area_close.le
        have totalBound := head.cap.total_close.le
        rw [head.cap.polynomial.left_eq] at areaBound totalBound
        have leftBound : Basic.normSq head.original.area.left.total ≤ slope := by
          have bounded := head.original.area.source.increment_bound (first := 0) (last := 1)
            ⟨le_rfl, by decide⟩ ⟨by decide, le_rfl⟩
          rw [← head.original.area.source_total] at bounded
          have localBound : Basic.normSq head.original.area.left.total ≤ data.sourceSlope :=
            bounded.trans_eq (by ring1)
          exact localBound.trans ((Fraction.Order.Basic.le_max_left _ _).trans slopeLe)
        have expanded : slope ≤ 2 * (slope + 1) :=
          (le_add_of_nonneg_right (show (0 : Coordinate) ≤ 1 by decide)).trans
            ((le_add_of_nonneg_right (add_nonneg slopeNonnegative (show (0 : Coordinate) ≤ 1 by
              decide))).trans_eq (by ring1))
        refine ⟨areaBound, totalBound, leftBound.trans expanded, ?_⟩
        have identity : head.cap.joined.summary.total =
            head.original.area.left.total + -(head.original.area.left.total - head.cap.joined.summary.total) := by ring1
        have estimate := Bounds.normSq_add_le_two head.original.area.left.total
          (-(head.original.area.left.total - head.cap.joined.summary.total))
        rw [← identity, Basic.normSq_neg] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add leftBound (totalBound.trans totalSmall)) (by decide))
      · exact ih ((Fraction.Order.Basic.le_max_right _ _).trans slopeLe) pair member

/-- The sum of paired complete-path total differences equals the difference of their two flattened increment sums. -/
private theorem sum_errors (pairs : List (List Gaussian × List Gaussian)) :
    gaussianSum (pairs.map (fun pair => gaussianSum
      pair.1 - gaussianSum pair.2)) =
      gaussianSum (pairs.map Prod.fst).flatten -
        gaussianSum (pairs.map Prod.snd).flatten := by
  induction pairs with
  | nil => change (0 : Gaussian) = 0 - 0; ring1
  | cons pair pairs ih =>
      simp only [List.map_cons, List.flatten_cons, gaussianSum,
        IncrementArea.sum_append, ih, -eq_self, -iff_self]
      ring1

/-- The complete retained side-total discrepancy is bounded by the squared original parent count times the local total
target. -/
theorem total_error (evaluated : Evaluations sample depth readingIndex requests) (totalSmall : totalTarget ≤ 1)
  :
    Basic.normSq (evaluated.leftSummary.total - evaluated.capSummary.total) ≤
      (parents.length : Coordinate) * ((parents.length : Coordinate) *
        totalTarget) := by
  have bounded := bounds evaluated totalSmall
    (ParentCovers.sourceSlopeMaximum_nonnegative covers) le_rfl
  have estimate := Sum.Bounds.normSq_sum_le
    (evaluated.pairs.map (fun pair => gaussianSum pair.1 -
      gaussianSum pair.2)) totalTarget (by
      intro value member
      obtain ⟨pair, member, same⟩ := Map.mem_map.mp member
      rw [← same]
      exact (bounded pair member).2.1)
  rw [Map.length_map, evaluated.pairs_length,
    sum_errors, ← evaluated.leftSummary.total_eq, ←
    evaluated.capSummary.total_eq] at estimate
  exact estimate

/-- The complete retained side-area discrepancy satisfies the original parent-count budget, including all cross terms
between parent totals. -/
theorem area_error (evaluated : Evaluations sample depth readingIndex requests) (totalSmall : totalTarget ≤ 1)
    (totalNonnegative : 0 ≤ totalTarget) :
    Basic.normSq (evaluated.leftSummary.area - evaluated.capSummary.area) ≤
      2 * ((parents.length : Coordinate) ^ 2 * areaTarget + 16 * (parents.length :
        Coordinate) ^ 4 * totalTarget *
        (2 * ((ParentCovers.sourceSlopeMaximum covers) + 1))) := by
  have bounded := bounds evaluated totalSmall
    (ParentCovers.sourceSlopeMaximum_nonnegative covers) le_rfl
  have estimate := IncrementAreaComparison.blocks_area_difference_bound evaluated.pairs totalNonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (ParentCovers.sourceSlopeMaximum_nonnegative covers) (by decide)))
    (fun pair member => (bounded pair member).1) (fun pair member => (bounded pair member).2.1)
    (fun pair member => (bounded pair member).2.2.1) (fun pair member => (bounded pair member).2.2.2)
  rw [evaluated.pairs_length, ← evaluated.leftSummary.area_eq, ← evaluated.capSummary.area_eq] at estimate
  exact estimate

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEstimates
