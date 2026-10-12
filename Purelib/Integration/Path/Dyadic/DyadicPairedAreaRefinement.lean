module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.Dyadic.DyadicAreaRefinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

/-! Two-differential area refinement on the actual common dyadic path.
The bound is independent of the later subdivision count. -/
namespace Purelib.Integration.Path.Dyadic.DyadicPairedAreaRefinement

open Purelib.Data.Rat
open Purelib.Integration.Path.Dyadic
open Purelib.Topology.Polygon
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Riemann.Readings
open Purelib.Integration.Path
open Purelib.Riemann.Periods
open Purelib.Geometry.Rectangle.Partition

public section

/-- The rational carrier for paired dyadic parameters and area bounds. -/
private abbrev Coordinate := Fraction.Rational

/-- The original paired dyadic increment list has exactly two to the depth entries.

The left-coordinate readback preserves every paired occurrence and its original dyadic position. -/
theorem increments_length (values : Fraction.Rational → Stokes.PrimitivePoint) (depth : Nat) (first last :
  Fraction.Rational) :
    (DyadicPairedPrimitivePaths.increments values depth first last).length = 2 ^ depth :=
  (Map.length_map Stokes.PrimitivePoint.left (DyadicPairedPrimitivePaths.increments values depth first last)).symm.trans
    ((congrArg List.length (DyadicPairedPrimitivePaths.increments_left values depth first last)).trans
      (DyadicPrimitivePaths.dyadicIncrements_length _ _ _ _))

/-- Both coordinates of every original paired dyadic increment satisfy the depth-scaled movement bound.

The ordered endpoints stay within the original certified interval, and each coordinate retains its own component of the
original paired movement certificate. -/
theorem increments_bounded (values : Fraction.Rational → Stokes.PrimitivePoint) {lower upper slope : Fraction.Rational}
    (bounded : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (values last) (values first)) (slope * (last
        - first) ^ 2))
    (depth : Nat) {first last : Fraction.Rational} (firstInside : lower ≤ first ∧ first ≤ upper)
    (lastInside : lower ≤ last ∧ last ≤ upper) (ordered : first ≤ last) :
    ∀ increment ∈ DyadicPairedPrimitivePaths.increments values depth first last,
      PrimitiveAreaBounds.PrimitivePoint.Bounded increment (Geometric.Basic.quarterRadius slope depth * (last - first) ^
        2) := by
  intro increment member
  constructor
  · rw [← Norm.Basic.normSq_eq_canonical]
    apply DyadicAreaRefinement.dyadicIncrements_bounded
      (lower := lower) (upper := upper) (slope := slope)
      (fun parameter => (values parameter).left)
      (fun a b ha hb => by
        have scalar := (bounded a b ha hb).1
        simpa only [Norm.Basic.normSq_eq_canonical, Stokes.PrimitivePoint.sub] using scalar)
      depth firstInside lastInside ordered
    rw [← DyadicPairedPrimitivePaths.increments_left]
    exact Map.mem_map_of_mem member
  · rw [← Norm.Basic.normSq_eq_canonical]
    apply DyadicAreaRefinement.dyadicIncrements_bounded
      (lower := lower) (upper := upper) (slope := slope)
      (fun parameter => (values parameter).right)
      (fun a b ha hb => by
        have scalar := (bounded a b ha hb).2
        simpa only [Norm.Basic.normSq_eq_canonical, Stokes.PrimitivePoint.sub] using scalar)
      depth firstInside lastInside ordered
    rw [← DyadicPairedPrimitivePaths.increments_right]
    exact Map.mem_map_of_mem member

/-- Paired dyadic area differs from its original endpoint chord by at most four times slope squared times width to the
fourth power.

The movement slope is nonnegative and both ordered endpoints lie within the original certified parameter interval. -/
theorem dyadicArea_chord_bound (values : Fraction.Rational → Stokes.PrimitivePoint) {lower upper slope :
  Fraction.Rational}
    (nonnegative : 0 ≤ slope)
    (bounded : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (values last) (values first)) (slope * (last
        - first) ^ 2))
    (depth : Nat) {first last : Fraction.Rational} (firstInside : lower ≤ first ∧ first ≤ upper)
    (lastInside : lower ≤ last ∧ last ≤ upper) (ordered : first ≤ last) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBilinearBoundaryRibbon.dyadicArea values depth first last - Stokes.edgeArea
      (values first) (values last)) ≤
      4 * slope ^ 2 * (last - first) ^ 4 := by
  rw [← DyadicPairedPrimitivePaths.increments_area]
  have estimate := PairedIncrementArea.area_bound (DyadicPairedPrimitivePaths.increments values depth first last)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Geometric.Basic.quarterRadius_nonneg nonnegative depth)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    (DyadicPairedAreaRefinement.increments_bounded values bounded depth firstInside lastInside ordered)
  rw [DyadicPairedAreaRefinement.increments_length] at estimate
  have cancel : (((2 ^ depth : Nat) : Fraction.Rational) ^ 2) * Geometric.Basic.quarterRadius slope depth = slope := by
    rw [pow_two, mul_assoc]
    exact Geometric.DyadicCount.dyadic_count_cancel slope depth
  exact estimate.trans_eq (by
    rw [← mul_assoc, cancel]
    ring1)

/-- Both exact midpoint subinterval widths are half the original width. -/
private theorem half_widths (first last : Fraction.Rational) :
    PreparedBoxPartitions.midpoint first last - first = (last - first) / 2 ∧
      last - PreparedBoxPartitions.midpoint first last = (last - first) / 2 := by
  have twiceHalf : ((last - first) / 2) * 2 = last - first :=
    Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  constructor
  · unfold PreparedBoxPartitions.midpoint; ring1
  · calc
      _ = (last - first) - (last - first) / 2 := by unfold PreparedBoxPartitions.midpoint; ring1
      _ = ((last - first) / 2) * 2 - (last - first) / 2 := by rw [twiceHalf]
      _ = _ := by ring1

/-- Combining the two half-width fourth-power costs gives one further quarter-radius decay step. -/
private theorem half_fourth (slope width : Fraction.Rational) (depth : Nat) :
    2 * (Geometric.Basic.quarterRadius slope depth * (width / 2) ^ 4 + Geometric.Basic.quarterRadius slope depth *
      (width / 2) ^ 4) =
      Geometric.Basic.quarterRadius slope (depth + 1) * width ^ 4 := by
  have step : Geometric.Basic.quarterRadius slope (depth + 1) * 4 = Geometric.Basic.quarterRadius slope depth := by
    rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ]
    calc
      _ = (slope * (1 / 4 : Fraction.Rational) ^ depth) * ((1 / 4 : Fraction.Rational) * 4) := by ring1
      _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]; ring1
  apply Fraction.Field.mul_right_cancel_of_ne (c := 4) (by decide)
  calc
    _ = Geometric.Basic.quarterRadius slope depth * ((width / 2) * 2) ^ 4 := by ring1
    _ = Geometric.Basic.quarterRadius slope depth * width ^ 4 := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
    _ = _ := by rw [← step]; ring1

/-- Further paired dyadic refinement changes area by the quarter-decaying coarse-depth movement bound.

The original endpoints, two-coordinate movement certificate and width remain fixed for every finer depth. -/
theorem dyadicArea_refinement_bound (values : Fraction.Rational → Stokes.PrimitivePoint) {lower upper slope :
  Fraction.Rational}
    (nonnegative : 0 ≤ slope)
    (bounded : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (values last) (values first)) (slope * (last
        - first) ^ 2))
    (coarse fine : Nat) {first last : Fraction.Rational} (firstInside : lower ≤ first ∧ first ≤ upper)
    (lastInside : lower ≤ last ∧ last ≤ upper) (ordered : first ≤ last) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBilinearBoundaryRibbon.dyadicArea values (coarse + fine) first last -
      DyadicBilinearBoundaryRibbon.dyadicArea values coarse first last) ≤
      Geometric.Basic.quarterRadius (4 * slope ^ 2) coarse * (last - first) ^ 4 := by
  induction coarse generalizing first last with
  | zero =>
      simpa only [Nat.zero_add, DyadicBilinearBoundaryRibbon.dyadicArea_zero, Geometric.Basic.quarterRadius_eq_mul_pow,
        pow_zero, mul_one] using
        DyadicPairedAreaRefinement.dyadicArea_chord_bound values nonnegative bounded fine firstInside lastInside ordered
  | succ coarse ih =>
      have between := PreparedBoxPartitions.midpoint_between ordered
      have middleInside := And.intro (firstInside.1.trans between.1) (between.2.trans lastInside.2)
      have left := ih firstInside middleInside between.1
      have right := ih middleInside lastInside between.2
      have split : DyadicBilinearBoundaryRibbon.dyadicArea values (coarse + 1 + fine) first last -
        DyadicBilinearBoundaryRibbon.dyadicArea values (coarse + 1) first last =
          (DyadicBilinearBoundaryRibbon.dyadicArea values (coarse + fine) first (PreparedBoxPartitions.midpoint first
            last) - DyadicBilinearBoundaryRibbon.dyadicArea values coarse first (PreparedBoxPartitions.midpoint first
            last)) +
          (DyadicBilinearBoundaryRibbon.dyadicArea values (coarse + fine) (PreparedBoxPartitions.midpoint first last)
            last - DyadicBilinearBoundaryRibbon.dyadicArea values coarse (PreparedBoxPartitions.midpoint first last)
            last) := by
        rw [Nat.add_right_comm coarse 1 fine, DyadicBilinearBoundaryRibbon.dyadicArea_succ,
          DyadicBilinearBoundaryRibbon.dyadicArea_succ]
        ring1
      rw [split]
      apply (Norm.Bounds.normSq_add_le_two _ _).trans
      apply (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add left right) (by decide)).trans_eq
      rw [(DyadicPairedAreaRefinement.half_widths first last).1, (DyadicPairedAreaRefinement.half_widths first last).2]
      exact DyadicPairedAreaRefinement.half_fourth _ _ _

end

end Purelib.Integration.Path.Dyadic.DyadicPairedAreaRefinement
