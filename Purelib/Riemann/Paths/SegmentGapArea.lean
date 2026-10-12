module
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Tactic.Ring
import Purelib.Data.List.Membership

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
@[expose] def first : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian) → Path.IncrementArea.Gaussian →
  Path.IncrementArea.Gaussian
  | [], fallback => fallback
  | segment :: _, _ => segment.1

/-- Pair each actual segment increment with its increment to the next retained start.

The final segment uses the supplied finish, so the second components form the polygon closed across the endpoint gaps.
-/
@[expose] def pairs : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian) → Path.IncrementArea.Gaussian →
  List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian)
  | [], _ => []
  | segment :: remaining, finish =>
      (segment.2 - segment.1, first remaining finish - segment.1) :: pairs remaining finish

/-- Sum the areas of edges from each retained segment start to the next start or supplied finish. -/
@[expose] def edgeAreas : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian) → Path.IncrementArea.Gaussian
  → Path.IncrementArea.Gaussian
  | [], _ => 0
  | segment :: remaining, finish => Path.BoundaryRibbon.area segment.1 (first remaining finish) + edgeAreas remaining
    finish

/-- List the signed triangle areas contributed by each actual segment and its following endpoint gap. -/
@[expose] def gapAreas : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian) → Path.IncrementArea.Gaussian
  → List Path.IncrementArea.Gaussian
  | [], _ => []
  | segment :: remaining, finish =>
      Path.BoundaryRibbon.area (segment.2 - segment.1) (first remaining finish - segment.2) :: gapAreas remaining finish

/-- Sum the actual segment areas and the connecting endpoint-gap areas. -/
@[expose] def sewnAreas : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian) → Path.IncrementArea.Gaussian
  → Path.IncrementArea.Gaussian
  | [], _ => 0
  | segment :: remaining, finish =>
      Path.BoundaryRibbon.area segment.1 segment.2 + Path.BoundaryRibbon.area segment.2 (first remaining finish) +
        sewnAreas remaining finish

open Purelib.Data in
/-- Every successive endpoint gap, including the final supplied endpoint, has quadrance at most the displayed error. -/
@[expose] def GapsSmall : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian) → Path.IncrementArea.Gaussian
  → Path.IncrementArea.Coordinate → Prop
  | [], _, _ => True
  | segment :: remaining, finish, error =>
      Data.Gaussian.Norm.Basic.normSq (first remaining finish - segment.2) ≤ error ∧ GapsSmall remaining finish
        error

/-- The increment-pair list has one entry per retained segment. -/
theorem pairs_length (segments : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian)) (finish :
  Path.IncrementArea.Gaussian) :
    (pairs segments finish).length = segments.length := by
  induction segments with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- The first components are exactly the actual segment increments in order. -/
theorem pairs_left (segments : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian)) (finish :
  Path.IncrementArea.Gaussian) :
    (pairs segments finish).map Prod.fst = segments.map (fun segment => segment.2 - segment.1) := by
  induction segments with
  | nil => rfl
  | cons _ _ ih => exact congrArg (List.cons _) ih

open Purelib.Data in
/-- The gap-closed polygon increments sum to final endpoint minus initial start. -/
theorem pairs_right_sum (segments : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian)) (finish :
  Path.IncrementArea.Gaussian) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((pairs segments finish).map Prod.snd) = finish - first segments finish :=
      by
  induction segments with
  | nil => change (0 : Path.IncrementArea.Gaussian) = finish - finish; ring1
  | cons _ _ ih => simp only [pairs, List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, first, ih]; ring1

/-- The trace area of the gap-closed polygon equals the retained edge-area sum. -/
theorem pairs_right_trace (segments : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian)) (finish :
  Path.IncrementArea.Gaussian) :
    Path.IncrementArea.traceArea (first segments finish) ((pairs segments finish).map Prod.snd) = edgeAreas segments
      finish := by
  induction segments with
  | nil => rfl
  | cons segment remaining ih =>
      change Path.IncrementArea.traceArea segment.1 ((pairs (segment :: remaining) finish).map Prod.snd) = _
      simp only [pairs, List.map_cons, Path.IncrementArea.traceArea, edgeAreas]
      rw [show segment.1 + (first remaining finish - segment.1) = first remaining finish by ring1, ih]

/-- The gap-closed polygon area is its edge-area sum minus the closing endpoint area. -/
theorem pairs_right_area (segments : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian)) (finish :
  Path.IncrementArea.Gaussian) :
    Path.IncrementArea.pathArea ((pairs segments finish).map Prod.snd) =
      edgeAreas segments finish - Path.BoundaryRibbon.area (first segments finish) finish := by
  have trace := pairs_right_trace segments finish
  rw [Path.IncrementArea.traceArea_eq, pairs_right_sum, Path.BoundaryRibbon.area_sub_self_right] at trace
  rw [← trace]
  ring1

section
open Purelib.Data
/-- Closing the polygon at its first start makes its path area equal the edge-area sum. -/
theorem pairs_closed_area (segments : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian)) :
    Path.IncrementArea.pathArea ((pairs segments (first segments 0)).map Prod.snd) = edgeAreas segments (first segments
      0) := by
  rw [pairs_right_area]
  have same : first segments (first segments 0) = first segments 0 := by cases segments <;> rfl
  rw [same, Path.IncrementArea.area_self, Gaussian.Basic.sub_zero]

/-- Splitting an edge at an intermediate point adds the exact signed gap-triangle area. -/
theorem gap_triangle (a b c : Path.IncrementArea.Gaussian) :
    Path.BoundaryRibbon.area a b + Path.BoundaryRibbon.area b c = Path.BoundaryRibbon.area a c +
      Path.BoundaryRibbon.area (b - a) (c - b) := by
  apply Gaussian.Basic.ext <;> simp only [Path.BoundaryRibbon.area, Data.Gaussian.Basic.conj,
    Data.Gaussian.Basic.conj, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re,
    Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- The sewn area is the edge-area sum plus all retained gap-triangle contributions. -/
theorem sewnAreas_eq (segments : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian)) (finish :
  Path.IncrementArea.Gaussian) :
    sewnAreas segments finish = edgeAreas segments finish + Data.Gaussian.Norm.Sum.Basic.gaussianSum (gapAreas segments
      finish) := by
  induction segments with
  | nil => change (0 : Path.IncrementArea.Gaussian) = 0 + 0; ring1
  | cons segment remaining ih =>
      simp only [sewnAreas, edgeAreas, gapAreas, Data.Gaussian.Norm.Sum.Basic.gaussianSum, gap_triangle, ih]
      ring1

/-- The actual-increment area correction retains the polygon difference and every gap triangle.

The gap-closed polygon finishes at its first start, so no separate endpoint closing term remains. -/
theorem correction_eq (segments : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian)) :
    Path.IncrementArea.pathArea (segments.map (fun segment => segment.2 - segment.1)) - sewnAreas segments (first
      segments 0) =
      (Path.IncrementArea.pathArea ((pairs segments (first segments 0)).map Prod.fst) -
        Path.IncrementArea.pathArea ((pairs segments (first segments 0)).map Prod.snd)) -
          Data.Gaussian.Norm.Sum.Basic.gaussianSum (gapAreas segments (first segments 0)) := by
  rw [pairs_left, pairs_closed_area, sewnAreas_eq]
  ring1

/-- A uniform endpoint-gap bound also bounds the difference of each paired pair of increments.

Each retained pair keeps its original consecutive endpoints; the supplied gap bounds certify both readings in their
original order. -/
theorem pairs_errors {segments : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian)} {finish :
  Path.IncrementArea.Gaussian} {error : Path.IncrementArea.Coordinate}
    (gaps : GapsSmall segments finish error) :
    ∀ pair ∈ pairs segments finish, Data.Gaussian.Norm.Basic.normSq (pair.1 - pair.2) ≤ error := by
  induction segments with
  | nil => intro _ member; cases member
  | cons segment remaining ih =>
      intro pair member
      rcases Membership.mem_cons.mp member with rfl | member
      · change Data.Gaussian.Norm.Basic.normSq ((segment.2 - segment.1) - (first remaining finish - segment.1)) ≤
          error
        rw [show (segment.2 - segment.1) - (first remaining finish - segment.1) =
          -(first remaining finish - segment.2) by ring1, Gaussian.Norm.Basic.normSq_neg]
        exact gaps.1
      · exact ih gaps.2 pair member

/-- Actual and gap-closed increments both have quadrance at most twice the segment bound plus gap bound.

The two bounds are nonnegative, every actual segment satisfies its bound, and every retained endpoint gap satisfies the
error bound. -/
theorem pairs_bounds {segments : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian)} {finish :
  Path.IncrementArea.Gaussian} {error bound : Path.IncrementArea.Coordinate}
    (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (gaps : GapsSmall segments finish error)
    (totals : ∀ segment ∈ segments, Data.Gaussian.Norm.Basic.normSq (segment.2 - segment.1) ≤ bound) :
    ∀ pair ∈ pairs segments finish,
      Data.Gaussian.Norm.Basic.normSq pair.1 ≤ 2 * (bound + error) ∧ Data.Gaussian.Norm.Basic.normSq pair.2 ≤ 2
        * (bound + error) := by
  induction segments with
  | nil => intro _ member; cases member
  | cons segment remaining ih =>
      intro pair member
      rcases Membership.mem_cons.mp member with rfl | member
      · have total := totals segment (List.mem_cons_self ..)
        constructor
        · apply total.trans
          apply Rat.Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
          exact (add_nonneg boundNonnegative
            (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Path.IncrementArea.Coordinate) ≤ 2)
              errorNonnegative)).trans_eq (by ring1)
        · exact (Gaussian.Norm.Bounds.normSq_sub_le_via (first remaining finish) segment.2 segment.1).trans
            ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (Rat.Fraction.Order.Arithmetic.add_le_add_direct gaps.1 total) (by decide)).trans_eq (by ring1))
      · exact ih gaps.2 (fun item belongs => totals item (List.mem_cons_of_mem segment belongs)) pair member

end

/-- There is exactly one retained gap-triangle area per original segment. -/
theorem gapAreas_length (segments : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian)) (finish :
  Path.IncrementArea.Gaussian) :
    (gapAreas segments finish).length = segments.length := by
  induction segments with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

open Purelib.Data
/-- Every gap-triangle quadrance is at most four times the segment bound times the gap error.

The segment bound is nonnegative, and the displayed segment and endpoint-gap estimates hold throughout the retained
list. -/
theorem gapAreas_bounded {segments : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian)} {finish :
  Path.IncrementArea.Gaussian} {error bound : Path.IncrementArea.Coordinate}
    (boundNonnegative : 0 ≤ bound) (gaps : GapsSmall segments finish error)
    (totals : ∀ segment ∈ segments, Data.Gaussian.Norm.Basic.normSq (segment.2 - segment.1) ≤ bound) :
    ∀ value ∈ gapAreas segments finish, Data.Gaussian.Norm.Basic.normSq value ≤ 4 * bound * error := by
  induction segments with
  | nil => intro _ member; cases member
  | cons segment remaining ih =>
      intro value member
      rcases Membership.mem_cons.mp member with rfl | member
      · have product := Rat.Fraction.Order.Arithmetic.mul_le_mul_direct
          (totals segment (List.mem_cons_self ..)) gaps.1 (Gaussian.Norm.Basic.normSq_nonneg _) boundNonnegative
        exact (Path.BoundaryRibbon.area_bound _ _).trans ((show
          4 * Data.Gaussian.Norm.Basic.normSq (segment.2 - segment.1) * Data.Gaussian.Norm.Basic.normSq (first
            remaining finish - segment.2) =
            4 * (Data.Gaussian.Norm.Basic.normSq (segment.2 - segment.1) * Data.Gaussian.Norm.Basic.normSq
              (first remaining finish - segment.2)) by ring1).trans_le
              ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by decide)).trans_eq (by
                ring1)))
      · exact ih gaps.2 (fun item belongs => totals item (List.mem_cons_of_mem segment belongs)) value member

/-- Bound the full coarse area correction using actual segment lengths, endpoint gaps and original segment count.

The estimate pays both the paired polygon difference and all gap triangles, with nonnegative uniform segment and gap
bounds. -/
theorem correction_bound (segments : List (Path.IncrementArea.Gaussian × Path.IncrementArea.Gaussian)) {error bound :
  Path.IncrementArea.Coordinate}
    (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (gaps : GapsSmall segments (first segments 0) error)
    (totals : ∀ segment ∈ segments, Data.Gaussian.Norm.Basic.normSq (segment.2 - segment.1) ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea (segments.map (fun segment => segment.2 -
      segment.1)) -
      sewnAreas segments (first segments 0)) ≤
        2 * (16 * (segments.length : Path.IncrementArea.Coordinate) ^ 4 * error * (2 * (bound + error)) +
          (segments.length : Path.IncrementArea.Coordinate) ^ 2 * (4 * bound * error)) := by
  have bounds := pairs_bounds errorNonnegative boundNonnegative gaps totals
  have polygon := Path.IncrementAreaComparison.pathArea_difference_bound (pairs segments (first segments 0))
    errorNonnegative
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg boundNonnegative errorNonnegative))
    (pairs_errors gaps) (fun pair member => (bounds pair member).1) (fun pair member => (bounds pair member).2)
  rw [pairs_length] at polygon
  have triangles := Path.IncrementArea.sum_bound_of_length
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Path.IncrementArea.Coordinate) ≤ 4)
        boundNonnegative) errorNonnegative)
    (gapAreas_bounded boundNonnegative gaps totals) (le_of_eq (gapAreas_length segments (first segments 0)))
  rw [correction_eq]
  exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Rat.Fraction.Order.Arithmetic.add_le_add_direct polygon triangles) (by decide))

end

end Purelib.Riemann.Paths.SegmentGapArea
