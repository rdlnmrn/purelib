module
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Tactic.Ring
import Purelib.Data.List.Membership

open Purelib.Data.Rat.Fraction.Order

public section

/-!
# Closing the polygon of segment totals across retained endpoint gaps

The actual segment endpoints need not agree. Closing each total by its next
endpoint gap gives a closed polygon. The comparison retains the area of each
gap triangle and depends on segment lengths and gaps, not absolute positions.
-/

namespace Purelib.Riemann.Paths.SegmentGapArea

open Purelib.Data.List

open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea
open Purelib.Integration.Path.IncrementAreaComparison (pathArea_difference_bound)
open Purelib.Integration.Path.BoundaryRibbon (area area_bound)

section
open Purelib.Integration
/-- Read the first segment's start, using the supplied endpoint when the list is empty. -/
@[expose] def first : List (Gaussian × Gaussian) → Gaussian →
  Gaussian
  | [], fallback => fallback
  | segment :: _, _ => segment.1

/-- Pair each actual segment increment with its increment to the next retained start.

The final segment uses the supplied finish, so the second components form the polygon closed across the endpoint gaps.
-/
@[expose] def pairs : List (Gaussian × Gaussian) → Gaussian →
  List (Gaussian × Gaussian)
  | [], _ => []
  | segment :: remaining, finish =>
      (segment.2 - segment.1, first remaining finish - segment.1) :: pairs remaining finish

/-- Sum the areas of edges from each retained segment start to the next start or supplied finish. -/
@[expose] def edgeAreas : List (Gaussian × Gaussian) → Gaussian
  → Gaussian
  | [], _ => 0
  | segment :: remaining, finish => area segment.1 (first remaining finish) + edgeAreas remaining
    finish

/-- List the signed triangle areas contributed by each actual segment and its following endpoint gap. -/
@[expose] def gapAreas : List (Gaussian × Gaussian) → Gaussian
  → List Gaussian
  | [], _ => []
  | segment :: remaining, finish =>
      area (segment.2 - segment.1) (first remaining finish - segment.2) :: gapAreas remaining finish

/-- Sum the actual segment areas and the connecting endpoint-gap areas. -/
@[expose] def sewnAreas : List (Gaussian × Gaussian) → Gaussian
  → Gaussian
  | [], _ => 0
  | segment :: remaining, finish =>
      area segment.1 segment.2 + area segment.2 (first remaining finish) +
        sewnAreas remaining finish

open Purelib.Data in
/-- Every successive endpoint gap, including the final supplied endpoint, has quadrance at most the displayed error. -/
@[expose] def GapsSmall : List (Gaussian × Gaussian) → Gaussian
  → Coordinate → Prop
  | [], _, _ => True
  | segment :: remaining, finish, error =>
      Gaussian.Norm.Basic.normSq (first remaining finish - segment.2) ≤ error ∧ GapsSmall remaining finish
        error

/-- The increment-pair list has one entry per retained segment. -/
theorem pairs_length (segments : List (Gaussian × Gaussian)) (finish :
  Gaussian) :
    (pairs segments finish).length = segments.length := by
  induction segments with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- The first components are exactly the actual segment increments in order. -/
theorem pairs_left (segments : List (Gaussian × Gaussian)) (finish :
  Gaussian) :
    (pairs segments finish).map Prod.fst = segments.map (fun segment => segment.2 - segment.1) := by
  induction segments with
  | nil => rfl
  | cons _ _ ih => exact congrArg (List.cons _) ih

open Purelib.Data in
/-- The gap-closed polygon increments sum to final endpoint minus initial start. -/
theorem pairs_right_sum (segments : List (Gaussian × Gaussian)) (finish :
  Gaussian) :
    gaussianSum ((pairs segments finish).map Prod.snd) = finish - first segments finish :=
      by
  induction segments with
  | nil => change (0 : Gaussian) = finish - finish; ring1
  | cons _ _ ih => simp only [pairs, List.map_cons, gaussianSum, first, ih]; ring1

/-- The trace area of the gap-closed polygon equals the retained edge-area sum. -/
theorem pairs_right_trace (segments : List (Gaussian × Gaussian)) (finish :
  Gaussian) :
    traceArea (first segments finish) ((pairs segments finish).map Prod.snd) = edgeAreas segments
      finish := by
  induction segments with
  | nil => rfl
  | cons segment remaining ih =>
      change traceArea segment.1 ((pairs (segment :: remaining) finish).map Prod.snd) = _
      simp only [pairs, List.map_cons, traceArea, edgeAreas]
      rw [show segment.1 + (first remaining finish - segment.1) = first remaining finish by ring1, ih]

/-- The gap-closed polygon area is its edge-area sum minus the closing endpoint area. -/
theorem pairs_right_area (segments : List (Gaussian × Gaussian)) (finish :
  Gaussian) :
    pathArea ((pairs segments finish).map Prod.snd) =
      edgeAreas segments finish - area (first segments finish) finish := by
  have trace := pairs_right_trace segments finish
  rw [traceArea_eq, pairs_right_sum, Path.BoundaryRibbon.area_sub_self_right] at trace
  rw [← trace]
  ring1

section
open Purelib.Data
/-- Closing the polygon at its first start makes its path area equal the edge-area sum. -/
theorem pairs_closed_area (segments : List (Gaussian × Gaussian)) :
    pathArea ((pairs segments (first segments 0)).map Prod.snd) = edgeAreas segments (first segments
      0) := by
  rw [pairs_right_area]
  have same : first segments (first segments 0) = first segments 0 := by cases segments <;> rfl
  rw [same, area_self, Gaussian.Basic.sub_zero]

/-- Splitting an edge at an intermediate point adds the exact signed gap-triangle area. -/
theorem gap_triangle (a b c : Gaussian) :
    area a b + area b c = area a c +
      area (b - a) (c - b) := by
  apply Gaussian.Basic.ext <;> simp only [area, Gaussian.Basic.conj,
    Gaussian.Basic.conj, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re,
    Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- The sewn area is the edge-area sum plus all retained gap-triangle contributions. -/
theorem sewnAreas_eq (segments : List (Gaussian × Gaussian)) (finish :
  Gaussian) :
    sewnAreas segments finish = edgeAreas segments finish + gaussianSum (gapAreas segments
      finish) := by
  induction segments with
  | nil => change (0 : Gaussian) = 0 + 0; ring1
  | cons segment remaining ih =>
      simp only [sewnAreas, edgeAreas, gapAreas, gaussianSum, gap_triangle, ih]
      ring1

/-- The actual-increment area correction retains the polygon difference and every gap triangle.

The gap-closed polygon finishes at its first start, so no separate endpoint closing term remains. -/
theorem correction_eq (segments : List (Gaussian × Gaussian)) :
    pathArea (segments.map (fun segment => segment.2 - segment.1)) - sewnAreas segments (first
      segments 0) =
      (pathArea ((pairs segments (first segments 0)).map Prod.fst) -
        pathArea ((pairs segments (first segments 0)).map Prod.snd)) -
          gaussianSum (gapAreas segments (first segments 0)) := by
  rw [pairs_left, pairs_closed_area, sewnAreas_eq]
  ring1

/-- A uniform endpoint-gap bound also bounds the difference of each paired pair of increments.

Each retained pair keeps its original consecutive endpoints; the supplied gap bounds certify both readings in their
original order. -/
theorem pairs_errors {segments : List (Gaussian × Gaussian)} {finish :
  Gaussian} {error : Coordinate}
    (gaps : GapsSmall segments finish error) :
    ∀ pair ∈ pairs segments finish, Gaussian.Norm.Basic.normSq (pair.1 - pair.2) ≤ error := by
  induction segments with
  | nil => intro _ member; cases member
  | cons segment remaining ih =>
      intro pair member
      rcases Membership.mem_cons.mp member with rfl | member
      · change Gaussian.Norm.Basic.normSq ((segment.2 - segment.1) - (first remaining finish - segment.1)) ≤
          error
        rw [show (segment.2 - segment.1) - (first remaining finish - segment.1) =
          -(first remaining finish - segment.2) by ring1, Gaussian.Norm.Basic.normSq_neg]
        exact gaps.1
      · exact ih gaps.2 pair member

/-- Closing the actual scalar segment list bounds its total increment by the original count-squared gap payment.

The existing paired increments retain the original segments and their
successive gaps. Their second-column sum is zero at the same first start;
the common local gap bound therefore pays the first-column sum directly.
-/
theorem increments_normSq_le {segments : List (Gaussian × Gaussian)} {error : Coordinate}
    (gaps : GapsSmall segments (first segments 0) error) :
    Gaussian.Norm.Basic.normSq (gaussianSum (segments.map (fun segment => segment.2 - segment.1))) ≤
      (segments.length : Coordinate) * ((segments.length : Coordinate) * error) := by
  let finish := first segments 0
  have bound := Gaussian.Norm.Sum.Bounds.normSq_gaussianSum_map_sub_le
    (pairs segments finish) Prod.fst Prod.snd (pairs_errors gaps)
  have left := congrArg gaussianSum (pairs_left segments finish)
  have closed : first segments finish = finish := by cases segments <;> rfl
  have right : gaussianSum ((pairs segments finish).map Prod.snd) = 0 :=
    (pairs_right_sum segments finish).trans
      ((congrArg (fun value : Gaussian => finish - value) closed).trans (by ring1))
  have sums := congrArg₂ (fun left right : Gaussian => left - right) left right
  have actual : gaussianSum ((pairs segments finish).map Prod.fst) -
      gaussianSum ((pairs segments finish).map Prod.snd) =
        gaussianSum (segments.map (fun segment => segment.2 - segment.1)) :=
    sums.trans (by ring1)
  exact (congrArg Gaussian.Norm.Basic.normSq actual).symm.trans_le
    (bound.trans_eq (congrArg (fun length : Nat =>
      (length : Coordinate) * ((length : Coordinate) * error)) (pairs_length segments finish)))

/-- Actual and gap-closed increments both have quadrance at most twice the segment bound plus gap bound.

The two bounds are nonnegative, every actual segment satisfies its bound, and every retained endpoint gap satisfies the
error bound. -/
theorem pairs_bounds {segments : List (Gaussian × Gaussian)} {finish :
  Gaussian} {error bound : Coordinate}
    (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (gaps : GapsSmall segments finish error)
    (totals : ∀ segment ∈ segments, Gaussian.Norm.Basic.normSq (segment.2 - segment.1) ≤ bound) :
    ∀ pair ∈ pairs segments finish,
      Gaussian.Norm.Basic.normSq pair.1 ≤ 2 * (bound + error) ∧ Gaussian.Norm.Basic.normSq pair.2 ≤ 2
        * (bound + error) := by
  induction segments with
  | nil => intro _ member; cases member
  | cons segment remaining ih =>
      intro pair member
      rcases Membership.mem_cons.mp member with rfl | member
      · have total := totals segment (List.mem_cons_self ..)
        constructor
        · apply total.trans
          apply Arithmetic.le_of_sub_nonneg_direct
          exact (add_nonneg boundNonnegative
            (Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤ 2)
              errorNonnegative)).trans_eq (by ring1)
        · exact (Gaussian.Norm.Bounds.normSq_sub_le_via (first remaining finish) segment.2 segment.1).trans
            ((Arithmetic.mul_le_mul_of_nonneg_left_direct
              (Arithmetic.add_le_add_direct gaps.1 total) (by decide)).trans_eq (by ring1))
      · exact ih gaps.2 (fun item belongs => totals item (List.mem_cons_of_mem segment belongs)) pair member

end

/-- There is exactly one retained gap-triangle area per original segment. -/
theorem gapAreas_length (segments : List (Gaussian × Gaussian)) (finish :
  Gaussian) :
    (gapAreas segments finish).length = segments.length := by
  induction segments with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

open Purelib.Data
/-- Every gap-triangle quadrance is at most four times the segment bound times the gap error.

The segment bound is nonnegative, and the displayed segment and endpoint-gap estimates hold throughout the retained
list. -/
theorem gapAreas_bounded {segments : List (Gaussian × Gaussian)} {finish :
  Gaussian} {error bound : Coordinate}
    (boundNonnegative : 0 ≤ bound) (gaps : GapsSmall segments finish error)
    (totals : ∀ segment ∈ segments, Gaussian.Norm.Basic.normSq (segment.2 - segment.1) ≤ bound) :
    ∀ value ∈ gapAreas segments finish, Gaussian.Norm.Basic.normSq value ≤ 4 * bound * error := by
  induction segments with
  | nil => intro _ member; cases member
  | cons segment remaining ih =>
      intro value member
      rcases Membership.mem_cons.mp member with rfl | member
      · have product := Arithmetic.mul_le_mul_direct
          (totals segment (List.mem_cons_self ..)) gaps.1 (Gaussian.Norm.Basic.normSq_nonneg _) boundNonnegative
        exact (area_bound _ _).trans ((show
          4 * Gaussian.Norm.Basic.normSq (segment.2 - segment.1) * Gaussian.Norm.Basic.normSq (first
            remaining finish - segment.2) =
            4 * (Gaussian.Norm.Basic.normSq (segment.2 - segment.1) * Gaussian.Norm.Basic.normSq
              (first remaining finish - segment.2)) by ring1).trans_le
              ((Arithmetic.mul_le_mul_of_nonneg_left_direct product (by decide)).trans_eq (by
                ring1)))
      · exact ih gaps.2 (fun item belongs => totals item (List.mem_cons_of_mem segment belongs)) value member

/-- Bound the full coarse area correction using actual segment lengths, endpoint gaps and original segment count.

The estimate pays both the paired polygon difference and all gap triangles, with nonnegative uniform segment and gap
bounds. -/
theorem correction_bound (segments : List (Gaussian × Gaussian)) {error bound :
  Coordinate}
    (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (gaps : GapsSmall segments (first segments 0) error)
    (totals : ∀ segment ∈ segments, Gaussian.Norm.Basic.normSq (segment.2 - segment.1) ≤ bound) :
    Gaussian.Norm.Basic.normSq (pathArea (segments.map (fun segment => segment.2 -
      segment.1)) -
      sewnAreas segments (first segments 0)) ≤
        2 * (16 * (segments.length : Coordinate) ^ 4 * error * (2 * (bound + error)) +
          (segments.length : Coordinate) ^ 2 * (4 * bound * error)) := by
  have bounds := pairs_bounds errorNonnegative boundNonnegative gaps totals
  have polygon := pathArea_difference_bound (pairs segments (first segments 0))
    errorNonnegative
    (Arithmetic.mul_nonneg_direct (by decide) (add_nonneg boundNonnegative errorNonnegative))
    (pairs_errors gaps) (fun pair member => (bounds pair member).1) (fun pair member => (bounds pair member).2)
  rw [pairs_length] at polygon
  have triangles := sum_bound_of_length
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤ 4)
        boundNonnegative) errorNonnegative)
    (gapAreas_bounded boundNonnegative gaps totals) (le_of_eq (gapAreas_length segments (first segments 0)))
  rw [correction_eq]
  exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct polygon triangles) (by decide))

end

end Purelib.Riemann.Paths.SegmentGapArea
