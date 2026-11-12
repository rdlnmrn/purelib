module

public import Purelib.Approximation.Rational.Pi.Endpoint
public import Purelib.Geometry.Gaussian.UnitCircle.Polygon
public import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Algebra.NatCast
import Purelib.Algebra.Semiring.Normalization
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.List.Rat.Linear
import Purelib.Data.List.Fold
import Purelib.Data.List.Range.Basic
import Purelib.Data.Rat.Bounds.Abs
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Integration.Partition.Uniform.Grid
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Endpoint bounds for rational circle polygons

The signed fan area of each ordered stereographic edge lies between the
source readings at its two endpoints. Summing the original grid occurrences
compares the actual shoelace area with the retained source frontier.
-/

namespace Purelib.Approximation.Rational.Pi.Polygon

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.List
open Purelib.Geometry.Gaussian
open Purelib.Integration
open Purelib.Integration.Partition

/-- The exact oriented edge area lies between the two endpoint source readings.

The first parameter is nonnegative and the second is no smaller. The positive
denominators allow the comparisons to be checked by finite cross-products. -/
public theorem edge_bounds {first second : Fraction.Rational}
    (nonnegative : 0 ≤ first) (ordered : first ≤ second) :
    (second - first) * Source.value second ≤
      4 * ((second - first) * (1 + first * second) /
        ((first ^ 2 + 1) * (second ^ 2 + 1))) ∧
    4 * ((second - first) * (1 + first * second) /
        ((first ^ 2 + 1) * (second ^ 2 + 1))) ≤
      (second - first) * Source.value first := by
  have secondNonnegative : 0 ≤ second := nonnegative.trans ordered
  have gapNonnegative : 0 ≤ second - first := Arithmetic.sub_nonneg_direct ordered
  have firstPositive : 0 < first ^ 2 + 1 :=
    Arithmetic.add_pos_of_nonneg_of_pos_direct (Arithmetic.sq_nonneg_direct first) (by decide)
  have secondPositive : 0 < second ^ 2 + 1 :=
    Arithmetic.add_pos_of_nonneg_of_pos_direct (Arithmetic.sq_nonneg_direct second) (by decide)
  have firstMiddle : first ^ 2 + 1 ≤ 1 + first * second := by
    have product := Arithmetic.mul_le_mul_of_nonneg_left_direct ordered nonnegative
    have shifted := Arithmetic.add_le_add_right_direct product 1
    calc
      first ^ 2 + 1 = first * first + 1 := by ring1
      _ ≤ first * second + 1 := shifted
      _ = 1 + first * second := by ring1
  have middleSecond : 1 + first * second ≤ second ^ 2 + 1 := by
    have product := Arithmetic.mul_le_mul_of_nonneg_right_direct ordered secondNonnegative
    have shifted := Arithmetic.add_le_add_right_direct product 1
    calc
      1 + first * second = first * second + 1 := by ring1
      _ ≤ second * second + 1 := shifted
      _ = second ^ 2 + 1 := by ring1
  have lowerFactor : 0 ≤ 4 * (second - first) * (second ^ 2 + 1) :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide) gapNonnegative) secondPositive.le
  have upperFactor : 0 ≤ 4 * (second - first) * (first ^ 2 + 1) :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide) gapNonnegative) firstPositive.le
  have lowerCross := Arithmetic.mul_le_mul_of_nonneg_left_direct firstMiddle lowerFactor
  have upperCross := Arithmetic.mul_le_mul_of_nonneg_left_direct middleSecond upperFactor
  have lower : (4 * (second - first)) / (second ^ 2 + 1) ≤
      (4 * (second - first) * (1 + first * second)) /
        ((first ^ 2 + 1) * (second ^ 2 + 1)) := by
    apply Field.div_le_div_of_cross secondPositive (Arithmetic.mul_pos_direct firstPositive secondPositive)
    calc
      _ = (4 * (second - first) * (second ^ 2 + 1)) * (first ^ 2 + 1) := by ring1
      _ ≤ (4 * (second - first) * (second ^ 2 + 1)) * (1 + first * second) := lowerCross
      _ = _ := by ring1
  have upper : (4 * (second - first) * (1 + first * second)) /
        ((first ^ 2 + 1) * (second ^ 2 + 1)) ≤
      (4 * (second - first)) / (first ^ 2 + 1) := by
    apply Field.div_le_div_of_cross (Arithmetic.mul_pos_direct firstPositive secondPositive) firstPositive
    calc
      _ = (4 * (second - first) * (first ^ 2 + 1)) * (1 + first * second) := by ring1
      _ ≤ (4 * (second - first) * (first ^ 2 + 1)) * (second ^ 2 + 1) := upperCross
      _ = _ := by ring1
  have endpoint (parameter : Fraction.Rational) :
      (second - first) * Source.value parameter =
        (4 * (second - first)) / (parameter ^ 2 + 1) := by
    unfold Source.value Source.denominator
    rw [show 1 + parameter ^ 2 = parameter ^ 2 + 1 from by ring1]
    rw [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
    ring1
  have area : 4 * ((second - first) * (1 + first * second) /
      ((first ^ 2 + 1) * (second ^ 2 + 1))) =
      (4 * (second - first) * (1 + first * second)) /
        ((first ^ 2 + 1) * (second ^ 2 + 1)) := by
    rw [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
    ring1
  rw [endpoint, endpoint, area]
  exact ⟨lower, upper⟩

/-- The signed edge area is bounded by its unscaled endpoint values.

For ordered nonnegative parameters, the same edge lies between the mesh
length times `1 / (1 + t²)` at the right and left endpoints respectively. -/
public theorem edge_unscaled_bounds {first second : Fraction.Rational}
    (nonnegative : 0 ≤ first) (ordered : first ≤ second) :
    (second - first) * (1 / (1 + second ^ 2)) ≤
      (second - first) * (1 + first * second) /
        ((first ^ 2 + 1) * (second ^ 2 + 1)) ∧
    (second - first) * (1 + first * second) /
        ((first ^ 2 + 1) * (second ^ 2 + 1)) ≤
      (second - first) * (1 / (1 + first ^ 2)) := by
  have bounds := edge_bounds nonnegative ordered
  have endpoint (parameter : Fraction.Rational) :
      (second - first) * Source.value parameter =
        4 * ((second - first) * (1 / (1 + parameter ^ 2))) := by
    unfold Source.value Source.denominator
    rw [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
    ring1
  rw [endpoint, endpoint] at bounds
  constructor
  · apply Arithmetic.le_of_mul_le_mul_right_direct (c := 4) _ (by decide)
    calc
      _ = 4 * ((second - first) * (1 / (1 + second ^ 2))) := by ring1
      _ ≤ 4 * ((second - first) * (1 + first * second) /
          ((first ^ 2 + 1) * (second ^ 2 + 1))) := bounds.1
      _ = _ := by ring1
  · apply Arithmetic.le_of_mul_le_mul_right_direct (c := 4) _ (by decide)
    calc
      _ = 4 * ((second - first) * (1 + first * second) /
          ((first ^ 2 + 1) * (second ^ 2 + 1))) := by ring1
      _ ≤ 4 * ((second - first) * (1 / (1 + first ^ 2))) := bounds.2
      _ = _ := by ring1

/-- Four times an ordered finite sum is the sum of its fourfold terms. -/
private theorem sum_four (term : Nat → Fraction.Rational) (indices : List Nat) :
    (indices.map (fun index => 4 * term index)).sum = 4 * (indices.map term).sum := by
  calc
    _ = (indices.map (fun index => term index * 4)).sum :=
      Rat.Linear.sum_congr _ _ indices (fun index _ => by ring1)
    _ = (indices.map term).sum * 4 := Rat.Linear.sum_mul_right term 4 indices
    _ = _ := by ring1

/-- The actual polygon area lies in the original source-linked endpoint frontier.

The proof compares the same ordered grid occurrences in the shoelace
readback and in the lower and upper integrals of `Endpoint.frontier`. -/
public theorem area_endpoint_bounds (extra : Nat) :
    lowerIntegral (Endpoint.frontier extra).cells ≤ UnitCircle.Polygon.area extra ∧
    UnitCircle.Polygon.area extra ≤ upperIntegral (Endpoint.frontier extra).cells := by
  let indices := List.range (extra + 1)
  let point := Uniform.Grid.point (extra + 1)
  let weight : Fraction.Rational := 1 / ((extra + 1 : Nat) : Fraction.Rational)
  let edge : Nat → Fraction.Rational := fun index =>
    (point (index + 1) - point index) * (1 + point index * point (index + 1)) /
      ((point index ^ 2 + 1) * (point (index + 1) ^ 2 + 1))
  let lower : Nat → Fraction.Rational := fun index => weight * Source.value (point (index + 1))
  let upper : Nat → Fraction.Rational := fun index => weight * Source.value (point index)
  have bound (index : Nat) : lower index ≤ 4 * edge index ∧ 4 * edge index ≤ upper index := by
    have nonnegative : 0 ≤ point index := by
      by_cases zero : index = 0
      · subst index
        change 0 ≤ Uniform.Grid.point (extra + 1) 0
        rw [Uniform.Grid.point_zero]
      · calc
          (0 : Fraction.Rational) = Uniform.Grid.point (extra + 1) 0 := (Uniform.Grid.point_zero _).symm
          _ ≤ point index := (Uniform.Grid.point_lt (Nat.succ_pos extra) (Nat.pos_of_ne_zero zero)).le
    have ordered : point index ≤ point (index + 1) :=
      (Uniform.Grid.point_lt (Nat.succ_pos extra) (Nat.lt_succ_self index)).le
    have bounds := edge_bounds nonnegative ordered
    have step : point (index + 1) - point index = weight := Uniform.Grid.point_step (extra + 1) index
    constructor
    · calc
        lower index = (point (index + 1) - point index) * Source.value (point (index + 1)) :=
          congrArg (fun value => value * Source.value (point (index + 1))) step.symm
        _ ≤ 4 * edge index := bounds.1
    · calc
        4 * edge index ≤ (point (index + 1) - point index) * Source.value (point index) := bounds.2
        _ = upper index := congrArg (fun value => value * Source.value (point index)) step
  have lowerSum := Rat.Linear.sum_le lower (fun index => 4 * edge index) indices
    (fun index _ => (bound index).1)
  have upperSum := Rat.Linear.sum_le (fun index => 4 * edge index) upper indices
    (fun index _ => (bound index).2)
  rw [sum_four] at lowerSum upperSum
  constructor
  · rw [Endpoint.lowerIntegral_eq, UnitCircle.Polygon.area_eq_grid_sum]
    exact lowerSum
  · rw [Endpoint.upperIntegral_eq, UnitCircle.Polygon.area_eq_grid_sum]
    exact upperSum

/-- The original endpoint bound contains the actual polygon's shoelace area. -/
public theorem area_in_frontier (extra : Nat) :
    (integralBound (Endpoint.frontier extra).cells).Contains (UnitCircle.Polygon.area extra) :=
  area_endpoint_bounds extra

/-- Doubling a positive uniform mesh retains each endpoint and inserts an ordered midpoint.

The equalities identify the original grid points; the inequalities order the
new odd-index point between the original neighboring endpoints. -/
public theorem doubled_grid_points (extra index : Nat) :
    Uniform.Grid.point (2 * (extra + 1)) (2 * index) =
        Uniform.Grid.point (extra + 1) index ∧
      Uniform.Grid.point (extra + 1) index ≤
        Uniform.Grid.point (2 * (extra + 1)) (2 * index + 1) ∧
      Uniform.Grid.point (2 * (extra + 1)) (2 * index + 1) ≤
        Uniform.Grid.point (extra + 1) (index + 1) := by
  have aligned (i : Nat) : Uniform.Grid.point (2 * (extra + 1)) (2 * i) =
      Uniform.Grid.point (extra + 1) i := by
    unfold Uniform.Grid.point
    rw [Fraction.Cast.natCast_mul_direct, Fraction.Cast.natCast_mul_direct]
    exact Fraction.Field.mul_div_mul_left_direct 2 _ _ (by decide)
  have positive : 0 < 2 * (extra + 1) := by omega0
  have before := (Uniform.Grid.point_lt positive (show 2 * index < 2 * index + 1 by omega0)).le
  have after := (Uniform.Grid.point_lt positive (show 2 * index + 1 < 2 * (index + 1) by omega0)).le
  rw [aligned] at before after
  exact ⟨aligned index, before, after⟩

/-- The source value at a doubled-mesh midpoint lies between its coarse endpoint values.

This uses the original decreasing circle source and the aligned rational
grid points, including the first and last cells. -/
public theorem doubled_reading_bounds (extra index : Nat) :
    Source.value (Uniform.Grid.point (extra + 1) (index + 1)) ≤
        Source.value (Uniform.Grid.point (2 * (extra + 1)) (2 * index + 1)) ∧
      Source.value (Uniform.Grid.point (2 * (extra + 1)) (2 * index + 1)) ≤
        Source.value (Uniform.Grid.point (extra + 1) index) := by
  have grid := doubled_grid_points extra index
  have nonnegative : 0 ≤ Uniform.Grid.point (extra + 1) index := by
    by_cases zero : index = 0
    · rw [zero, Uniform.Grid.point_zero]
    · calc
        (0 : Fraction.Rational) = Uniform.Grid.point (extra + 1) 0 :=
          (Uniform.Grid.point_zero _).symm
        _ ≤ Uniform.Grid.point (extra + 1) index :=
          (Uniform.Grid.point_lt (Nat.succ_pos extra) (Nat.pos_of_ne_zero zero)).le
  exact ⟨Source.value_antitone (nonnegative.trans grid.2.1) grid.2.2,
    Source.value_antitone nonnegative grid.2.1⟩

/-- Pair consecutive entries of a doubled natural range without changing their order. -/
private theorem sum_doubled (term : Nat → Fraction.Rational) : ∀ count : Nat,
    ((List.range (2 * count)).map term).sum =
      ((List.range count).map (fun index => term (2 * index) + term (2 * index + 1))).sum
  | 0 => rfl
  | count + 1 => by
      have countEq : 2 * (count + 1) = (2 * count + 1) + 1 := by omega0
      rw [countEq, Range.Basic.range_succ, Range.Basic.range_succ, Range.Basic.range_succ]
      rw [Map.map_append, Map.map_append, Map.map_append]
      rw [Fold.sum_append Fraction.Field.zero_add Fraction.Field.add_assoc,
        Fold.sum_append Fraction.Field.zero_add Fraction.Field.add_assoc,
        Fold.sum_append Fraction.Field.zero_add Fraction.Field.add_assoc]
      rw [sum_doubled term count]
      change ((_ + (term (2 * count) + 0)) + (term (2 * count + 1) + 0)) =
        _ + ((term (2 * count) + term (2 * count + 1)) + 0)
      ring1

/-- Doubling a uniform endpoint mesh refines its original integral enclosure.

Each pair of fine source cells shares the coarse endpoints and has an
intermediate reading between them. Their equal half-weights therefore
improve both endpoint sums while retaining the original frontier owners. -/
public theorem doubled_frontier_refines (extra : Nat) :
    Interval.Refines (integralBound (Endpoint.frontier (2 * extra + 1)).cells)
      (integralBound (Endpoint.frontier extra).cells) := by
  let count := extra + 1
  let fineWeight : Fraction.Rational := 1 / ((2 * count : Nat) : Fraction.Rational)
  let coarseWeight : Fraction.Rational := 1 / (count : Fraction.Rational)
  have finePositive : 0 < fineWeight := by
    exact Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct (show 0 < 2 * count by omega0))
  have weights : 2 * fineWeight = coarseWeight := by
    change 2 * (1 / ((2 * count : Nat) : Fraction.Rational)) = 1 / (count : Fraction.Rational)
    rw [Fraction.Cast.natCast_mul_direct]
    calc
      2 * (1 / (2 * (count : Fraction.Rational))) =
          (2 * 1) / (2 * (count : Fraction.Rational)) := by
        rw [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
        ring1
      _ = 1 / (count : Fraction.Rational) :=
        Fraction.Field.mul_div_mul_left_direct 2 1 _ (by decide)
  let fine : Nat → Fraction.Rational := fun index =>
    fineWeight * Source.value (Uniform.Grid.point (2 * count) index)
  let lower : Nat → Fraction.Rational := fun index =>
    coarseWeight * Source.value (Uniform.Grid.point count (index + 1))
  let upper : Nat → Fraction.Rational := fun index =>
    coarseWeight * Source.value (Uniform.Grid.point count index)
  have paired (index : Nat) :
      lower index ≤ fine (2 * index + 1) + fine (2 * index + 2) ∧
      fine (2 * index) + fine (2 * index + 1) ≤ upper index := by
    have values := doubled_reading_bounds extra index
    have left := (doubled_grid_points extra index).1
    have right := (doubled_grid_points extra (index + 1)).1
    have indexEq : 2 * (index + 1) = 2 * index + 2 := by omega0
    rw [indexEq] at right
    have low := Arithmetic.mul_le_mul_of_nonneg_left_direct values.1 finePositive.le
    have high := Arithmetic.mul_le_mul_of_nonneg_left_direct values.2 finePositive.le
    have lowFine : fine (2 * index + 2) ≤ fine (2 * index + 1) := by
      change fineWeight * Source.value (Uniform.Grid.point (2 * count) (2 * index + 2)) ≤
        fineWeight * Source.value (Uniform.Grid.point (2 * count) (2 * index + 1))
      rw [right]
      exact low
    have highFine : fine (2 * index + 1) ≤ fine (2 * index) := by
      change fineWeight * Source.value (Uniform.Grid.point (2 * count) (2 * index + 1)) ≤
        fineWeight * Source.value (Uniform.Grid.point (2 * count) (2 * index))
      rw [left]
      exact high
    constructor
    · calc
        lower index = fine (2 * index + 2) + fine (2 * index + 2) := by
          change coarseWeight * Source.value (Uniform.Grid.point count (index + 1)) =
            fineWeight * Source.value (Uniform.Grid.point (2 * count) (2 * index + 2)) +
              fineWeight * Source.value (Uniform.Grid.point (2 * count) (2 * index + 2))
          rw [right, ← weights]
          ring1
        _ ≤ fine (2 * index + 1) + fine (2 * index + 2) :=
          Arithmetic.add_le_add_direct lowFine (Basic.le_refl (fine (2 * index + 2)))
    · calc
        fine (2 * index) + fine (2 * index + 1) ≤ fine (2 * index) + fine (2 * index) :=
          Arithmetic.add_le_add_direct (Basic.le_refl (fine (2 * index))) highFine
        _ = upper index := by
          change fineWeight * Source.value (Uniform.Grid.point (2 * count) (2 * index)) +
              fineWeight * Source.value (Uniform.Grid.point (2 * count) (2 * index)) =
            coarseWeight * Source.value (Uniform.Grid.point count index)
          rw [left, ← weights]
          ring1
  have lowerSum := Rat.Linear.sum_le lower (fun index => fine (2 * index + 1) + fine (2 * index + 2))
    (List.range count) (fun index _ => (paired index).1)
  have upperSum := Rat.Linear.sum_le (fun index => fine (2 * index) + fine (2 * index + 1)) upper
    (List.range count) (fun index _ => (paired index).2)
  constructor
  · change lowerIntegral (Endpoint.frontier extra).cells ≤ lowerIntegral (Endpoint.frontier (2 * extra + 1)).cells
    rw [Endpoint.lowerIntegral_eq, Endpoint.lowerIntegral_eq]
    have countEq : 2 * extra + 1 + 1 = 2 * count := by dsimp [count]; omega0
    rw [countEq]
    rw [sum_doubled (fun index => fine (index + 1)) count]
    exact lowerSum
  · change upperIntegral (Endpoint.frontier (2 * extra + 1)).cells ≤ upperIntegral (Endpoint.frontier extra).cells
    rw [Endpoint.upperIntegral_eq, Endpoint.upperIntegral_eq]
    have countEq : 2 * extra + 1 + 1 = 2 * count := by dsimp [count]; omega0
    rw [countEq]
    rw [sum_doubled fine count]
    exact upperSum

/-- The number of interior cuts on the dyadic mesh with `2 ^ stage` cells. -/
@[expose] public def dyadicExtra (stage : Nat) : Nat := 2 ^ stage - 1

/-- The dyadic mesh has the requested positive number of original cells. -/
public theorem dyadicExtra_cells (stage : Nat) : dyadicExtra stage + 1 = 2 ^ stage := by
  unfold dyadicExtra
  exact Nat.sub_add_cancel (Nat.pow_pos (by decide))

/-- The next dyadic stage doubles the preceding cell count. -/
public theorem dyadicExtra_succ (stage : Nat) :
    dyadicExtra (stage + 1) = 2 * dyadicExtra stage + 1 := by
  have cells := dyadicExtra_cells stage
  have next := dyadicExtra_cells (stage + 1)
  rw [Nat.pow_succ] at next
  omega0

/-- Every later dyadic endpoint frontier refines the original earlier frontier.

The induction composes the actual consecutive frontier refinements; it
preserves both original source-linked endpoint enclosures. -/
public theorem dyadic_frontier_refines {earlier later : Nat} (ordered : earlier ≤ later) :
    Interval.Refines (integralBound (Endpoint.frontier (dyadicExtra later)).cells)
      (integralBound (Endpoint.frontier (dyadicExtra earlier)).cells) := by
  have steps (count : Nat) :
      Interval.Refines (integralBound (Endpoint.frontier (dyadicExtra (earlier + count))).cells)
        (integralBound (Endpoint.frontier (dyadicExtra earlier)).cells) := by
    induction count with
    | zero => rw [Nat.add_zero]; exact Interval.Refines.refl _
    | succ count inductionHypothesis =>
        rw [Nat.add_succ, dyadicExtra_succ]
        exact (doubled_frontier_refines (dyadicExtra (earlier + count))).trans inductionHypothesis
  obtain ⟨count, equation⟩ := Nat.le.dest ordered
  rw [← equation]
  exact steps count

/-- Nested endpoint frontiers bound the difference of their actual polygon areas.

The hypothesis concerns the original source-linked intervals. Both shoelace
areas then belong to the coarser interval, whose exact width pays the bound. -/
public theorem area_abs_difference_le_of_refines (fine coarse : Nat)
    (nested : Interval.Refines (integralBound (Endpoint.frontier fine).cells)
      (integralBound (Endpoint.frontier coarse).cells)) :
    Fraction.abs (UnitCircle.Polygon.area fine - UnitCircle.Polygon.area coarse) ≤
      2 / ((coarse + 1 : Nat) : Fraction.Rational) := by
  have insideFine := nested.contains (area_in_frontier fine)
  have insideCoarse := area_in_frontier coarse
  have directed := Interval.pairwise_difference_le insideFine insideCoarse
  have absolute : Fraction.abs (UnitCircle.Polygon.area fine - UnitCircle.Polygon.area coarse) ≤
      (integralBound (Endpoint.frontier coarse).cells).width := by
    change max (UnitCircle.Polygon.area fine - UnitCircle.Polygon.area coarse)
      (-(UnitCircle.Polygon.area fine - UnitCircle.Polygon.area coarse)) ≤ _
    apply Basic.max_le directed.1
    have reverse : -(UnitCircle.Polygon.area fine - UnitCircle.Polygon.area coarse) =
        UnitCircle.Polygon.area coarse - UnitCircle.Polygon.area fine := by ring1
    rw [reverse]
    exact directed.2
  rw [Endpoint.frontier_width] at absolute
  exact absolute

/-- Nested endpoint frontiers bound the squared Gaussian distance of their polygon areas.

The real embeddings retain the actual polygon readings. The squared bound
is derived from the same coarse frontier width as the absolute bound. -/
public theorem area_normSq_difference_le_of_refines (fine coarse : Nat)
    (nested : Interval.Refines (integralBound (Endpoint.frontier fine).cells)
      (integralBound (Endpoint.frontier coarse).cells)) :
    Norm.Basic.normSq
      (RationalEmbedding.realPoint (UnitCircle.Polygon.area fine) -
        RationalEmbedding.realPoint (UnitCircle.Polygon.area coarse)) ≤
      (2 / ((coarse + 1 : Nat) : Fraction.Rational)) ^ 2 := by
  have absolute := area_abs_difference_le_of_refines fine coarse nested
  have squared := Arithmetic.pow_le_pow_direct
    (Arithmetic.abs_nonneg_direct (UnitCircle.Polygon.area fine - UnitCircle.Polygon.area coarse)) absolute 2
  rw [Bounds.Abs.abs_sq_direct] at squared
  rw [RationalEmbedding.realPoint_sub,
    RationalEmbedding.normSq_realPoint]
  exact squared

/-- Any later dyadic polygon area is within the earlier endpoint width. -/
public theorem dyadic_area_abs_difference_le {earlier later : Nat} (ordered : earlier ≤ later) :
    Fraction.abs (UnitCircle.Polygon.area (dyadicExtra later) -
      UnitCircle.Polygon.area (dyadicExtra earlier)) ≤
      2 / ((2 ^ earlier : Nat) : Fraction.Rational) := by
  have bound := area_abs_difference_le_of_refines (dyadicExtra later) (dyadicExtra earlier)
    (dyadic_frontier_refines ordered)
  rw [dyadicExtra_cells] at bound
  exact bound

/-- Squared Gaussian distance between later dyadic polygon areas uses the earlier mesh width. -/
public theorem dyadic_area_normSq_difference_le {earlier later : Nat} (ordered : earlier ≤ later) :
    Norm.Basic.normSq
      (RationalEmbedding.realPoint (UnitCircle.Polygon.area (dyadicExtra later)) -
        RationalEmbedding.realPoint (UnitCircle.Polygon.area (dyadicExtra earlier))) ≤
      (2 / ((2 ^ earlier : Nat) : Fraction.Rational)) ^ 2 := by
  have bound := area_normSq_difference_le_of_refines (dyadicExtra later) (dyadicExtra earlier)
    (dyadic_frontier_refines ordered)
  rw [dyadicExtra_cells] at bound
  exact bound

/-- The squared dyadic endpoint width is the scale-four quarter-radius allowance. -/
public theorem dyadic_mesh_width_sq (earlier : Nat) :
    (2 / ((2 ^ earlier : Nat) : Fraction.Rational)) ^ 2 =
      Geometric.Basic.quarterRadius 4 earlier := by
  have castPower : ((2 ^ earlier : Nat) : Fraction.Rational) = (2 : Fraction.Rational) ^ earlier :=
    Purelib.Algebra.NatCast.pow 2 earlier
  have powerSquare : ((2 : Fraction.Rational) ^ earlier) ^ 2 = (4 : Fraction.Rational) ^ earlier := by
    calc
      ((2 : Fraction.Rational) ^ earlier) ^ 2 =
          (2 : Fraction.Rational) ^ earlier * (2 : Fraction.Rational) ^ earlier := by ring1
      _ = ((2 : Fraction.Rational) * 2) ^ earlier :=
        (Purelib.Algebra.Semiring.Normalization.product_pow 2 2 earlier).symm
      _ = (4 : Fraction.Rational) ^ earlier :=
        congrArg (fun value : Fraction.Rational => value ^ earlier) (by decide)
  rw [castPower, Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.mul_pow_direct,
    ← Fraction.Field.inv_pow_direct, powerSquare]
  have fourSquare : (2 : Fraction.Rational) ^ 2 = 4 := by decide
  rw [fourSquare]
  change Geometric.Basic.quarterRadius 4 earlier = _
  rfl

/-- The dyadic polygon squared-distance bound is the original quarter-radius schedule. -/
public theorem dyadic_area_normSq_difference_le_quarter {earlier later : Nat} (ordered : earlier ≤ later) :
    Norm.Basic.normSq
      (RationalEmbedding.realPoint (UnitCircle.Polygon.area (dyadicExtra later)) -
        RationalEmbedding.realPoint (UnitCircle.Polygon.area (dyadicExtra earlier))) ≤
      4 * (1 / 4 : Fraction.Rational) ^ earlier := by
  have bound := dyadic_area_normSq_difference_le ordered
  rw [dyadic_mesh_width_sq, Geometric.Basic.quarterRadius_eq_mul_pow] at bound
  exact bound

end Purelib.Approximation.Rational.Pi.Polygon
