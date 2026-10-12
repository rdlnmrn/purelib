module

import Purelib.Data.List.Membership
import Purelib.Data.List.Map

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring
public import Purelib.Data.Gaussian.Norm.Bounds
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Area of an actual finite increment path

The area retains every intermediate excursion, even when the total increment
is zero. Concatenation separates the internal block areas from the polygon of
block totals. The uniform estimate pays all four powers of the cell count.
Executable summaries cache both total and area in one pass; generated caches
need only satisfy the semantic equations, not equal the fallback computation.
-/

namespace Purelib.Integration.Path.IncrementArea

open Purelib.Data.List

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Integration.Path.BoundaryRibbon (area area_bound)

open Purelib.Data.Gaussian in
/-- The canonical rational Gaussian carrier for increments and area readings. -/
abbrev Gaussian := Basic.Canonical
open Purelib.Data.Rat in
/-- The rational carrier for increment error bounds. -/
abbrev Coordinate := Fraction.Rational

section
open Purelib.Data.Gaussian
open Purelib.Integration.Path
/-- Skew area is additive in its first argument. -/
theorem area_add_left (first second last : Gaussian) :
    BoundaryRibbon.area (first + second) last = BoundaryRibbon.area first last + BoundaryRibbon.area second last := by
  apply Basic.ext <;> simp only [BoundaryRibbon.area, Data.Gaussian.Basic.conj, Basic.add_re, Basic.add_im,
    Basic.sub_re,
    Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1

/-- Skew area is additive in its second argument. -/
theorem area_add_right (first second last : Gaussian) :
    BoundaryRibbon.area first (second + last) = BoundaryRibbon.area first second + BoundaryRibbon.area first last := by
  apply Basic.ext <;> simp only [BoundaryRibbon.area, Data.Gaussian.Basic.conj, Basic.add_re, Basic.add_im,
    Basic.sub_re,
    Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1

/-- Skew area with zero as its first argument vanishes. -/
@[simp] theorem area_zero_left (value : Gaussian) : BoundaryRibbon.area 0 value = 0 := by
  apply Basic.ext <;> simp only [BoundaryRibbon.area, Data.Gaussian.Basic.conj, Basic.zero_re, Basic.zero_im,
    Basic.sub_re,
    Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1

/-- Skew area with zero as its second argument vanishes. -/
@[simp] theorem area_zero_right (value : Gaussian) : BoundaryRibbon.area value 0 = 0 := by
  apply Basic.ext <;> simp only [BoundaryRibbon.area, Data.Gaussian.Basic.conj, Basic.zero_re, Basic.zero_im,
    Basic.sub_re,
    Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1

end

open Purelib.Integration.Path in
/-- The skew area of a value with itself vanishes. -/
@[simp] theorem area_self (value : Gaussian) : BoundaryRibbon.area value value = 0 := _root_.sub_self _

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
/-- Concatenating Gaussian increment lists adds their exact sums.

Both original increment lists retain their order. Structural recursion adds
the head to the exact unchanged tail sum. -/
theorem sum_append (first last : List Gaussian) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (first ++ last) = Data.Gaussian.Norm.Sum.Basic.gaussianSum first +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum last := by
  induction first with
  | nil =>
      change _ = 0 + _
      exact (Basic.zero_add _).symm
  | cons value first ih =>
      change value + Data.Gaussian.Norm.Sum.Basic.gaussianSum (first ++ last) =
        (value + Data.Gaussian.Norm.Sum.Basic.gaussianSum first) + Data.Gaussian.Norm.Sum.Basic.gaussianSum last
      rewrite [ih]
      exact (Basic.add_assoc _ _ _).symm

section
open Purelib.Integration.Path
/-- Sum consecutive skew areas while accumulating the original ordered increments from a retained start. -/
@[expose] def traceArea (start : Gaussian) : List Gaussian → Gaussian
  | [] => 0
  | value :: remaining => BoundaryRibbon.area start (start + value) + traceArea
    (start + value) remaining

/-- The area traced by the original ordered increments starting at zero. -/
@[expose] def pathArea (increments : List Gaussian) : Gaussian := traceArea 0 increments

end

section
open Purelib.Data.Gaussian
open Purelib.Integration.Path
/-- Translating the starting point changes the area by its skew product with the total increment.

The shift contributes its skew area with the exact total displacement.
Every original excursion remains in the recursively accumulated path area. -/
theorem traceArea_translate (start shift : Gaussian) (increments : List Gaussian) :
    traceArea (start + shift) increments = traceArea start increments + BoundaryRibbon.area
      shift (Data.Gaussian.Norm.Sum.Basic.gaussianSum increments) := by
  induction increments generalizing start with
  | nil =>
      change 0 = 0 + BoundaryRibbon.area shift 0
      rewrite [area_zero_right]
      exact (Basic.add_zero _).symm
  | cons value remaining ih =>
      simp only [traceArea, Data.Gaussian.Norm.Sum.Basic.gaussianSum]
      rw [show start + shift + value = (start + value) + shift by ring1, ih]
      simp only [area_add_left, area_add_right, area_self]
      have skew : BoundaryRibbon.area shift start = -BoundaryRibbon.area start shift := by
        unfold BoundaryRibbon.area
        ring1
      rw [skew]
      ring1

/-- The trace area is the zero-start path area plus the starting point's skew area with total displacement. -/
theorem traceArea_eq (start : Gaussian) (increments : List Gaussian) :
    traceArea start increments = pathArea increments + BoundaryRibbon.area start
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum increments) := by
  simpa only [Basic.zero_add, pathArea] using traceArea_translate 0 start increments

/-- Prepending an increment adds its skew area with the remaining total to the tail path area. -/
theorem pathArea_cons (value : Gaussian) (remaining : List Gaussian) :
    pathArea (value :: remaining) = pathArea remaining + BoundaryRibbon.area value
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum remaining) := by
  simp only [pathArea, traceArea, area_zero_left, Basic.zero_add]
  exact traceArea_eq value remaining

/-- The area of concatenated increments splits at the first list's exact terminal displacement.

The second list starts at the first list's exact terminal displacement.
The equality retains both ordered tails and their original intermediate excursions. -/
theorem traceArea_append (start : Gaussian) (first last : List Gaussian) :
    traceArea start (first ++ last) = traceArea start first + traceArea (start
      + Data.Gaussian.Norm.Sum.Basic.gaussianSum first) last := by
  induction first generalizing start with
  | nil =>
      change traceArea start last =
        0 + traceArea (start + 0) last
      rewrite [Basic.add_zero]
      exact (Basic.zero_add _).symm
  | cons value first ih =>
      rewrite [List.cons_append, traceArea, traceArea,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum, ih, Basic.add_assoc, Basic.add_assoc]
      exact Eq.refl _

/-- Concatenating increment paths adds their areas and the skew area of their two exact totals. -/
theorem pathArea_append (first last : List Gaussian) :
    pathArea (first ++ last) = pathArea first + pathArea last +
      BoundaryRibbon.area (Data.Gaussian.Norm.Sum.Basic.gaussianSum first) (Data.Gaussian.Norm.Sum.Basic.gaussianSum
        last) := by
  rw [pathArea, traceArea_append, Basic.zero_add, traceArea_eq
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum first) last]
  exact (_root_.add_assoc _ _ _).symm

/-- Retain each increment's skew area with the sum of all later original increments. -/
private def pairTerms : List Gaussian → List Gaussian
  | [] => []
  | value :: remaining => BoundaryRibbon.area value (Data.Gaussian.Norm.Sum.Basic.gaussianSum remaining) ::
    pairTerms remaining

end

open Purelib.Integration.Path in
/-- The ordered pair-term list has the same length as the original increments. -/
private theorem pairTerms_length (values : List Gaussian) : (pairTerms values).length =
  values.length := by
  induction values with
  | nil => rfl
  | cons value values ih => exact congrArg Nat.succ ih

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
/-- Summing the retained pair terms gives the exact zero-start path area. -/
private theorem pairTerms_sum (values : List Gaussian) : Data.Gaussian.Norm.Sum.Basic.gaussianSum
  (pairTerms values) = pathArea values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    rw [pairTerms, Data.Gaussian.Norm.Sum.Basic.gaussianSum, ih, pathArea_cons,
      Basic.add_comm]

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Path
/-- A common nonnegative squared-norm bound and a length bound control the total increment norm by count squared times
that bound. -/
theorem sum_bound_of_length {values : List Gaussian} {bound : Coordinate}
    (nonnegative : 0 ≤ bound) (bounded : ∀ value ∈ values, Data.Gaussian.Norm.Basic.normSq value ≤ bound)
    {count : Nat} (countLe : values.length ≤ count) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum values) ≤ (count :
      Coordinate) ^ 2 * bound
      := by
  have le : (values.length : Coordinate) ≤ count := Fraction.Cast.Order.natCast_le_direct countLe
  have countNonnegative : (0 : Coordinate) ≤ count := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
    count)
  have lengthNonnegative : (0 : Coordinate) ≤ values.length := Fraction.Cast.Order.natCast_le_direct
    (Nat.zero_le values.length)
  have squared : (values.length : Coordinate) * values.length ≤ (count : Coordinate) * count
    :=
    Fraction.Order.Arithmetic.mul_le_mul_direct le le lengthNonnegative countNonnegative
  calc
    _ ≤ (values.length : Coordinate) * ((values.length : Coordinate) * bound) :=
      Norm.Sum.Bounds.normSq_sum_le values bound bounded
    _ = ((values.length : Coordinate) * values.length) * bound := by ring1
    _ ≤ ((count : Coordinate) * count) * bound :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct squared nonnegative
    _ = _ := by ring1

/-- Each retained pair term has squared norm at most four times count squared times the common increment bound squared.

The retained length bound controls each tail total. The common nonnegative
increment bound then pays its skew product with the displayed head increment. -/
private theorem pairTerms_bounded {values : List Gaussian} {bound : Coordinate}
    (nonnegative : 0 ≤ bound) (bounded : ∀ value ∈ values, Data.Gaussian.Norm.Basic.normSq value ≤ bound)
    {count : Nat} (countLe : values.length ≤ count) :
    ∀ value ∈ pairTerms values, Data.Gaussian.Norm.Basic.normSq value ≤ 4 * (count :
      Coordinate)
      ^ 2 * bound ^ 2 := by
  induction values with
  | nil => intro value member; cases member
  | cons first values ih =>
      have tailBound := fun value member => bounded value (List.mem_cons_of_mem first member)
      have tailCount : values.length ≤ count := (Nat.le_succ _).trans countLe
      intro value member
      rcases Membership.mem_cons.mp member with rfl | member
      · have product : Data.Gaussian.Norm.Basic.normSq first * Data.Gaussian.Norm.Basic.normSq
          (Data.Gaussian.Norm.Sum.Basic.gaussianSum
          values) ≤ bound * ((count : Coordinate) ^ 2 * bound) :=
          Fraction.Order.Arithmetic.mul_le_mul_direct
          (bounded first (List.mem_cons_self ..)) (sum_bound_of_length nonnegative tailBound tailCount)
          (Norm.Basic.normSq_nonneg _) nonnegative
        calc
          _ ≤ 4 * Data.Gaussian.Norm.Basic.normSq first * Data.Gaussian.Norm.Basic.normSq
            (Data.Gaussian.Norm.Sum.Basic.gaussianSum values)
            := BoundaryRibbon.area_bound first (Data.Gaussian.Norm.Sum.Basic.gaussianSum values)
          _ = 4 * (Data.Gaussian.Norm.Basic.normSq first * Data.Gaussian.Norm.Basic.normSq
            (Data.Gaussian.Norm.Sum.Basic.gaussianSum
            values)) := by
            ring1
          _ ≤ 4 * (bound * ((count : Coordinate) ^ 2 * bound)) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by decide)
          _ = _ := by ring1
      · exact ih tailBound tailCount value member

end

section
open Purelib.Data.Gaussian
open Purelib.Integration.Path
/-- A common nonnegative increment bound controls squared path area by four times the squared count-squared allowance.

The estimate depends on the exact original list length and the common nonnegative squared-norm bound. It applies without
an endpoint closure assumption. -/
theorem pathArea_bound (values : List Gaussian) {bound : Coordinate}
    (nonnegative : 0 ≤ bound) (bounded : ∀ value ∈ values, Data.Gaussian.Norm.Basic.normSq value ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (pathArea values) ≤ 4 * ((values.length : Coordinate) ^
      2 *
      bound) ^ 2 := by
  rw [← pairTerms_sum]
  have estimate := Norm.Sum.Bounds.normSq_sum_le (pairTerms values) _
    (pairTerms_bounded nonnegative bounded (count := values.length) le_rfl)
  rw [pairTerms_length] at estimate
  exact estimate.trans_eq (by ring1)

/-- Summing flattened increment blocks equals summing their exact block totals.

Each block contributes its exact total in the original block order.
Structural concatenation preserves every original increment, including repeats. -/
theorem sum_flatten (blocks : List (List Gaussian)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum blocks.flatten = Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map
      Data.Gaussian.Norm.Sum.Basic.gaussianSum) := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
      change Data.Gaussian.Norm.Sum.Basic.gaussianSum (block ++ blocks.flatten) =
        Data.Gaussian.Norm.Sum.Basic.gaussianSum block +
          Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map Data.Gaussian.Norm.Sum.Basic.gaussianSum)
      rewrite [sum_append, ih]
      exact Eq.refl _

/-- Flattened path area splits into the sum of internal block areas and the path area of their exact totals. -/
theorem pathArea_flatten (blocks : List (List Gaussian)) :
    pathArea blocks.flatten = Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map
      pathArea) +
      pathArea (blocks.map Data.Gaussian.Norm.Sum.Basic.gaussianSum) := by
  induction blocks with
  | nil => change (0 : Gaussian) = 0 + 0; ring1
  | cons block blocks ih =>
      simp only [List.flatten_cons, List.map_cons, pathArea_append,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum,
        pathArea_cons, ih, sum_flatten]
      ring1

end

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
set_option genInjectivity false in
/-- Cached total displacement and zero-start area for the exact ordered increment list.

Both caches retain defining equalities to the original list operations, allowing assembly to reuse the stored readings.
-/
structure Summary (increments : List Gaussian) where
  /-- The retained exact total displacement. -/ total : Gaussian
  /-- The total cache equals the original increment sum. -/ total_eq : total = Data.Gaussian.Norm.Sum.Basic.gaussianSum
    increments
  /-- The retained zero-start path area. -/ area : Gaussian
  /-- The area cache equals the original increment list's path area. -/ area_eq : area = pathArea
    increments

constructive_injectivity Summary

section
open Purelib.Data.Gaussian
open Purelib.Integration.Path
/-- Negating every retained increment negates its exact sum. -/
theorem negative_sum {α : Type} (value : α → Gaussian) (entries : List α) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => -value entry)) =
      -Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (entries.map value) := by
  induction entries with
  | nil => change (0 : Gaussian) = -0; ring1
  | cons head tail ih =>
      change -value head + Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.map _) = -(value head +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (tail.map value))
      rw [ih]
      ring1

/-- Negating every retained increment preserves its skew path area. -/
theorem negative_area {α : Type} (value : α → Gaussian) (entries : List α) :
    pathArea (entries.map (fun entry => -value entry)) = pathArea (entries.map value) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      rw [List.map_cons, List.map_cons, pathArea_cons, pathArea_cons, ih,
        negative_sum]
      congr 1
      apply Basic.ext <;> simp only [BoundaryRibbon.area, Data.Gaussian.Basic.conj, Basic.neg_re, Basic.neg_im,
        Basic.mul_re,
        Basic.mul_im, Basic.sub_re, Basic.sub_im] <;> ring1

end

namespace Summary

section
open Purelib.Integration.Path
/-- Compute the total and path area together in one recursion over the original increments.

Each step reuses the tail summary's cached total and area when constructing its own exact certificates. -/
@[expose] def build : (increments : List IncrementArea.Gaussian) → IncrementArea.Summary increments
  | [] => ⟨0, rfl, 0, rfl⟩
  | value :: remaining =>
      let tail := build remaining
      { total := value + tail.total
        total_eq := congrArg (value + ·) tail.total_eq
        area := tail.area + BoundaryRibbon.area value tail.total
        area_eq := by rw [tail.area_eq, tail.total_eq, IncrementArea.pathArea_cons] }

/-- Combine two retained summaries using their cached totals and areas and the exact cross-area term. -/
@[expose] def append {first last : List IncrementArea.Gaussian} (left : IncrementArea.Summary first) (right :
  IncrementArea.Summary last) : IncrementArea.Summary (first ++ last) where
  total := left.total + right.total
  total_eq := by rw [left.total_eq, right.total_eq, IncrementArea.sum_append]
  area := left.area + right.area + BoundaryRibbon.area left.total right.total
  area_eq := by rw [left.area_eq, right.area_eq, left.total_eq, right.total_eq, IncrementArea.pathArea_append]

end

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
/-- Construct the negated-increment summary by negating its cached total and retaining its cached area. -/
@[expose] def negate {increments : List IncrementArea.Gaussian} (summary : IncrementArea.Summary increments) :
    IncrementArea.Summary (increments.map (fun value => -value)) where
  total := -summary.total
  total_eq := by
    have negative := IncrementArea.negative_sum (fun value : IncrementArea.Gaussian => value) increments
    change Data.Gaussian.Norm.Sum.Basic.gaussianSum (increments.map (fun value => -value)) =
      -Data.Gaussian.Norm.Sum.Basic.gaussianSum (increments.map id) at negative
    rw [Map.map_id] at negative
    exact (congrArg (fun value : IncrementArea.Gaussian => -value) summary.total_eq).trans negative.symm
  area := summary.area
  area_eq := by
    have negative := IncrementArea.negative_area (fun value : IncrementArea.Gaussian => value) increments
    change IncrementArea.pathArea (increments.map (fun value => -value)) =
      IncrementArea.pathArea (increments.map id) at negative
    rw [Map.map_id] at negative
    exact summary.area_eq.trans negative.symm

end Summary
end Purelib.Integration.Path.IncrementArea
