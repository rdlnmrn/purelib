module
import Purelib.Algebra.NatCast
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.IncrementArea
public import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Finite area error between actual dyadic subdivision depths

A squared increment bound pays the number of fine increments exactly.
Refining a coarse interval changes its full area by a fourth-width error;
aggregating the coarse intervals leaves a quarter-power bound independent
of the further finite refinement depth. No limiting area is introduced.
-/

namespace Purelib.Integration.Path.Dyadic.DyadicAreaRefinement

open Purelib.Algebra
open Purelib.Data.List

open Purelib.Data.Rat in
/-- The rational carrier for dyadic area bounds and parameters. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian carrier for dyadic area readings. -/
private abbrev Gaussian := Basic.Canonical

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle.Partition in
/-- Both midpoint subinterval widths are exactly half the original width. -/
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

section
open Purelib.Approximation.Rational
open Purelib.Data.Rat
/-- Quarter-radius decay at depth zero is the original scale. -/
private theorem quarter_zero (slope : Fraction.Rational) : Geometric.Basic.quarterRadius slope 0 = slope := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct]

/-- Four times the next quarter radius equals the previous radius. -/
private theorem quarter_step (slope : Fraction.Rational) (depth : Nat) :
    Geometric.Basic.quarterRadius slope (depth + 1) * 4 = Geometric.Basic.quarterRadius slope depth := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ]
  calc
    _ = (slope * (1 / 4 : Fraction.Rational) ^ depth) * ((1 / 4 : Fraction.Rational) * 4) := by ring1
    _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]; ring1

end

section
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Integration.Path.Dyadic
/-- Halving width squared is equivalent to one further quarter-radius decay step. -/
private theorem half_square (slope width : Fraction.Rational) (depth : Nat) :
    Geometric.Basic.quarterRadius slope depth * (width / 2) ^ 2 = Geometric.Basic.quarterRadius slope (depth + 1) *
      width ^ 2 := by
  apply Fraction.Field.mul_right_cancel_of_ne (c := 4) (by decide)
  calc
    _ = Geometric.Basic.quarterRadius slope depth * ((width / 2) * 2) ^ 2 := by ring1
    _ = Geometric.Basic.quarterRadius slope depth * width ^ 2 := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
    _ = _ := by rw [← DyadicAreaRefinement.quarter_step slope depth]; ring1

/-- The doubled sum of two half-width fourth-power costs equals one further quarter-radius decay step. -/
private theorem half_fourth (slope width : Fraction.Rational) (depth : Nat) :
    2 * (Geometric.Basic.quarterRadius slope depth * (width / 2) ^ 4 + Geometric.Basic.quarterRadius slope depth *
      (width / 2) ^ 4) =
      Geometric.Basic.quarterRadius slope (depth + 1) * width ^ 4 := by
  apply Fraction.Field.mul_right_cancel_of_ne (c := 4) (by decide)
  calc
    _ = Geometric.Basic.quarterRadius slope depth * ((width / 2) * 2) ^ 4 := by ring1
    _ = Geometric.Basic.quarterRadius slope depth * width ^ 4 := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
    _ = _ := by rw [← DyadicAreaRefinement.quarter_step slope depth]; ring1

/-- The squared dyadic count cancels the original quarter-radius decay.

The original natural power-of-two count is cast into the rational carrier.
Each successor count pays exactly one additional quarter-radius step. -/
private theorem count_cancel (slope : Fraction.Rational) (depth : Nat) :
    (((2 ^ depth : Nat) : Fraction.Rational) ^ 2) * Geometric.Basic.quarterRadius slope depth = slope := by
  induction depth with
  | zero => rw [DyadicAreaRefinement.quarter_zero]; change (1 : Fraction.Rational) ^ 2 * slope = slope; ring1
  | succ depth ih =>
      calc
        _ = (((2 ^ depth : Nat) : Fraction.Rational) ^ 2) * (Geometric.Basic.quarterRadius slope (depth + 1) * 4) := by
          rw [Nat.pow_succ, NatCast.mul, Nat.cast_ofNat]
          ring1
        _ = slope := by rw [DyadicAreaRefinement.quarter_step]; exact ih

end

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path.Dyadic in
/-- Every original dyadic increment satisfies the depth-scaled squared movement bound.

The ordered endpoints stay in the original parameter interval, and the pointwise movement certificate applies to both
exact subinterval endpoints. -/
theorem dyadicIncrements_bounded (value : Fraction.Rational → Basic.Canonical) {lower upper slope : Fraction.Rational}
    (bounded : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      Data.Gaussian.Norm.Basic.normSq (value last - value first) ≤ slope * (last - first) ^ 2)
    (depth : Nat) {first last : Fraction.Rational} (firstInside : lower ≤ first ∧ first ≤ upper)
    (lastInside : lower ≤ last ∧ last ≤ upper) (ordered : first ≤ last) :
    ∀ increment ∈ DyadicPrimitivePaths.dyadicIncrements value depth first last,
      Data.Gaussian.Norm.Basic.normSq increment ≤ Geometric.Basic.quarterRadius slope depth * (last - first) ^ 2 := by
  induction depth generalizing first last with
  | zero =>
      intro increment member
      have equal : increment = value last - value first := Membership.mem_singleton.mp member
      rw [equal, DyadicAreaRefinement.quarter_zero]
      exact bounded first last firstInside lastInside
  | succ depth ih =>
      have between := PreparedBoxPartitions.midpoint_between ordered
      have middleInside := And.intro (firstInside.1.trans between.1) (between.2.trans lastInside.2)
      intro increment member
      rcases Membership.mem_append.mp member with member | member
      · exact (ih firstInside middleInside between.1 increment member).trans_eq (by
          rw [(DyadicAreaRefinement.half_widths first last).1, DyadicAreaRefinement.half_square])
      · exact (ih middleInside lastInside between.2 increment member).trans_eq (by
          rw [(DyadicAreaRefinement.half_widths first last).2, DyadicAreaRefinement.half_square])

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
/-- Finite dyadic area differs from its original endpoint chord by at most four times slope squared times width to the
fourth power.

The original movement scale is nonnegative, and the ordered endpoints lie within its certified parameter interval. -/
theorem dyadicArea_chord_bound (value : Fraction.Rational → Basic.Canonical) {lower upper slope : Fraction.Rational}
    (nonnegative : 0 ≤ slope)
    (bounded : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      Data.Gaussian.Norm.Basic.normSq (value last - value first) ≤ slope * (last - first) ^ 2)
    (depth : Nat) {first last : Fraction.Rational} (firstInside : lower ≤ first ∧ first ≤ upper)
    (lastInside : lower ≤ last ∧ last ≤ upper) (ordered : first ≤ last) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBoundaryRibbon.dyadicArea value depth first last - BoundaryRibbon.area (value
      first) (value last)) ≤
      4 * slope ^ 2 * (last - first) ^ 4 := by
  have identity : DyadicBoundaryRibbon.dyadicArea value depth first last - BoundaryRibbon.area (value first) (value
    last) =
      IncrementArea.pathArea (DyadicPrimitivePaths.dyadicIncrements value depth first last) := by
    rw [← DyadicPrimitivePaths.traceArea_dyadicIncrements, IncrementArea.traceArea_eq,
      DyadicPrimitivePaths.dyadicIncrements_sum, BoundaryRibbon.area_sub_self_right]
    ring1
  rw [identity]
  have estimate := IncrementArea.pathArea_bound (DyadicPrimitivePaths.dyadicIncrements value depth first last)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Geometric.Basic.quarterRadius_nonneg nonnegative depth)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    (DyadicAreaRefinement.dyadicIncrements_bounded value bounded depth firstInside lastInside ordered)
  rw [DyadicPrimitivePaths.dyadicIncrements_length] at estimate
  apply estimate.trans_eq
  calc
    _ = 4 * (((((2 ^ depth : Nat) : Fraction.Rational) ^ 2) * Geometric.Basic.quarterRadius slope depth) * (last -
      first) ^ 2) ^ 2 := by
      ring1
    _ = _ := by rw [DyadicAreaRefinement.count_cancel]; ring1

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path.Dyadic in
/-- Further dyadic refinement changes area by a quarter-decaying bound at the original coarse depth.

The bound keeps the exact original endpoints and movement certificate, with scale four times slope squared and the
original width to the fourth power. -/
theorem dyadicArea_refinement_bound (value : Fraction.Rational → Basic.Canonical) {lower upper slope :
  Fraction.Rational}
    (nonnegative : 0 ≤ slope)
    (bounded : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      Data.Gaussian.Norm.Basic.normSq (value last - value first) ≤ slope * (last - first) ^ 2)
    (coarse fine : Nat) {first last : Fraction.Rational} (firstInside : lower ≤ first ∧ first ≤ upper)
    (lastInside : lower ≤ last ∧ last ≤ upper) (ordered : first ≤ last) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBoundaryRibbon.dyadicArea value (coarse + fine) first last -
      DyadicBoundaryRibbon.dyadicArea value coarse first last) ≤
      Geometric.Basic.quarterRadius (4 * slope ^ 2) coarse * (last - first) ^ 4 := by
  induction coarse generalizing first last with
  | zero =>
      simpa only [Nat.zero_add, DyadicBoundaryRibbon.dyadicArea_zero, DyadicAreaRefinement.quarter_zero] using
        DyadicAreaRefinement.dyadicArea_chord_bound value nonnegative bounded fine firstInside lastInside ordered
  | succ coarse ih =>
      have between := PreparedBoxPartitions.midpoint_between ordered
      have middleInside := And.intro (firstInside.1.trans between.1) (between.2.trans lastInside.2)
      have left := ih firstInside middleInside between.1
      have right := ih middleInside lastInside between.2
      have split : DyadicBoundaryRibbon.dyadicArea value (coarse + 1 + fine) first last -
        DyadicBoundaryRibbon.dyadicArea value (coarse + 1) first last =
          (DyadicBoundaryRibbon.dyadicArea value (coarse + fine) first (PreparedBoxPartitions.midpoint first last) -
            DyadicBoundaryRibbon.dyadicArea value coarse first (PreparedBoxPartitions.midpoint first last)) +
          (DyadicBoundaryRibbon.dyadicArea value (coarse + fine) (PreparedBoxPartitions.midpoint first last) last -
            DyadicBoundaryRibbon.dyadicArea value coarse (PreparedBoxPartitions.midpoint first last) last) := by
        rw [show coarse + 1 + fine = (coarse + fine) + 1 by omega, DyadicBoundaryRibbon.dyadicArea_succ,
          DyadicBoundaryRibbon.dyadicArea_succ]
        ring1
      rw [split]
      apply (Norm.Bounds.normSq_add_le_two _ _).trans
      apply (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add left right) (by decide)).trans_eq
      rw [(DyadicAreaRefinement.half_widths first last).1, (DyadicAreaRefinement.half_widths first last).2]
      exact DyadicAreaRefinement.half_fourth _ _ _

end Purelib.Integration.Path.Dyadic.DyadicAreaRefinement
