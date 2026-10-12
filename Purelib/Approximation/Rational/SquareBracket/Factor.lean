module

import Purelib.Data.Rat.Fraction.Constants
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Contraction
import Purelib.Approximation.Rational.SquareBracket.Basic
public import Purelib.Approximation.Rational.SquareBracket.Dyadic
import Purelib.Approximation.Rational.SquareBracket.Interval
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Approximation.Rational.SquareBracket.Refinement
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.SquareBracket

open Purelib.Approximation.Rational.SquareBracket.Basic

open Purelib.Data.Rat

public section

/-!
# Finite dyadic square brackets

A bounded natural recursion selects a positive dyadic rational whose square
lies immediately above a displayed target in `(0, 1)`.  It then performs a
coefficient-computed finite number of rational bisections.  Given any
displayed rational factor greater than one, the returned square lies above
the target and at most that factor times it.  No square root or limiting
object is used.
-/

namespace Purelib.Approximation.Rational.SquareBracket.Factor

/-- A conservative gap whose square expansion is bounded by the displayed factor.

The original rational minimum retains either one or a third of the excess
over one. For factors greater than one both inputs are strictly positive. -/
@[expose] def factorGap (factor : Fraction.Rational) : Fraction.Rational :=
  min 1 ((factor - 1) / 3)

/-- A factor greater than one gives a positive refinement gap. -/
theorem factorGap_pos {factor : Fraction.Rational} (factorGreater : 1 < factor) :
    0 < factorGap factor := by
  apply Fraction.Order.Basic.lt_min
  · decide
  · exact Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.sub_pos_direct factorGreater) (by decide)

/-- The squared expansion by the selected gap is at most the requested factor greater than one. -/
theorem one_add_factorGap_sq_le {factor : Fraction.Rational}
    (factorGreater : 1 < factor) :
    (1 + factorGap factor) ^ 2 ≤ factor := by
  let gap := factorGap factor
  have gapPositive : 0 < gap := factorGap_pos factorGreater
  have gapLeOne : gap ≤ 1 := Fraction.Order.Basic.min_le_left _ _
  have gapLeThird : gap ≤ (factor - 1) / 3 := Fraction.Order.Basic.min_le_right _ _
  have gapSqLeGap : gap ^ 2 ≤ gap := by
    rw [pow_two]
    simpa only [_root_.one_mul] using
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        gapLeOne gapPositive.le)
  have threeGapLe : 3 * gap ≤ factor - 1 := by
    have scaled :=
      (Fraction.Order.Field.le_div_iff_pos
        (show (0 : Fraction.Rational) < 3 by decide)).1 gapLeThird
    simpa only [Fraction.Field.mul_comm] using scaled
  calc
    (1 + factorGap factor) ^ 2 = 1 + 2 * gap + gap ^ 2 := by
      dsimp only [gap]
      ring1
    _ ≤ 1 + 2 * gap + gap := Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) gapSqLeGap
    _ = 1 + 3 * gap := by ring1
    _ ≤ 1 + (factor - 1) := Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) threeGapLe
    _ = factor := by ring1

set_option genInjectivity false in
/-- A positive rational scale whose square brackets the target within a displayed factor.

The retained radius carries strict lower and weak upper square comparisons
for the same target and factor; no completed square root is selected. -/
structure AdjustableBracket (target factor : Fraction.Rational) where
  /-- The retained positive rational radius. -/ radius : Fraction.Rational
  /-- The retained radius is strictly positive. -/ radiusPositive : 0 < radius
  /-- The radius squared strictly exceeds the target. -/ target_lt_square : target < radius ^ 2
  /-- The radius squared is at most the requested factor times the target. -/ square_le_factor_target : radius ^ 2 ≤
    factor * target

constructive_injectivity AdjustableBracket

/-- The coefficient-computed number of bisections required for a requested multiplicative square factor. -/
@[expose] def refinementFuel (factor : Fraction.Rational) : Nat :=
  Contraction.geometricDepth 1 (factorGap factor)

/-- Select a rational square bracket with any displayed factor greater than one.

The initial dyadic search and subsequent bisection count are bounded before
their recursions begin. The returned radius is the upper endpoint of that
retained refinement, with both square comparisons at the original target. -/
@[expose] def selectWithin (target factor : Fraction.Rational) (targetPositive : 0 < target)
    (target_lt_one : target < 1) (factorGreater : 1 < factor) :
    AdjustableBracket target factor := by
  let initial := (Dyadic.select target targetPositive target_lt_one).toSquareInterval
  let fuel := refinementFuel factor
  let interval := initial.refine fuel
  let gap := factorGap factor
  have gapPositive : 0 < gap := factorGap_pos factorGreater
  have halfPowerLeGap : (1 / 2 : Fraction.Rational) ^ fuel ≤ gap := by
    have geometric := Contraction.geometricDepth_sufficient
      (width := (1 : Fraction.Rational)) (epsilon := gap)
      (by decide) gapPositive
    change (2 / 3 : Fraction.Rational) ^ fuel * 1 ≤ gap at geometric
    have halfLeTwoThirds : (1 / 2 : Fraction.Rational) ^ fuel ≤
        (2 / 3 : Fraction.Rational) ^ fuel :=
      Fraction.Order.Arithmetic.pow_le_pow_direct
        (show (0 : Fraction.Rational) ≤ 1 / 2 by decide)
        (show (1 / 2 : Fraction.Rational) ≤ 2 / 3 by decide) fuel
    exact halfLeTwoThirds.trans (by
      simpa only [Fraction.Field.mul_one_direct] using geometric)
  have initialWidth : initial.upper - initial.lower = initial.lower := by
    dsimp only [initial, Bracket.toSquareInterval]
    calc
      (Dyadic.select target targetPositive target_lt_one).radius -
          (1 / 2 : Fraction.Rational) *
            (Dyadic.select target targetPositive target_lt_one).radius =
          (1 / 2 : Fraction.Rational) *
              ((Dyadic.select target targetPositive target_lt_one).radius +
                (Dyadic.select target targetPositive target_lt_one).radius) -
            (1 / 2 : Fraction.Rational) *
              (Dyadic.select target targetPositive target_lt_one).radius := by
        rw [Purelib.Data.Rat.Fraction.Constants.half_double]
      _ = (1 / 2 : Fraction.Rational) *
          (Dyadic.select target targetPositive target_lt_one).radius := by ring1
  have widthLeGapLower : interval.upper - interval.lower ≤
      gap * interval.lower := by
    have lowerNonnegative : 0 ≤ initial.lower := initial.lowerPositive.le
    have scaledPower :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        halfPowerLeGap lowerNonnegative
    have lowerMonotone : initial.lower ≤ interval.lower :=
      initial.lower_le_refine_lower fuel
    have scaledLower :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        lowerMonotone gapPositive.le
    calc
      interval.upper - interval.lower =
          (1 / 2 : Fraction.Rational) ^ fuel *
            (initial.upper - initial.lower) :=
        initial.refine_width fuel
      _ = (1 / 2 : Fraction.Rational) ^ fuel * initial.lower := by
        rw [initialWidth]
      _ ≤ gap * initial.lower := scaledPower
      _ ≤ gap * interval.lower := scaledLower
  have upperLe : interval.upper ≤ (1 + gap) * interval.lower := by
    calc
      interval.upper = interval.lower +
          (interval.upper - interval.lower) := by ring1
      _ ≤ interval.lower + gap * interval.lower :=
        Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) widthLeGapLower
      _ = (1 + gap) * interval.lower := by ring1
  have upperSqLe : interval.upper ^ 2 ≤
      ((1 + gap) * interval.lower) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      interval.upperPositive.le upperLe 2
  have coefficientLe : (1 + gap) ^ 2 ≤ factor := by
    simpa only [gap] using one_add_factorGap_sq_le factorGreater
  have productLe : (1 + gap) ^ 2 * interval.lower ^ 2 ≤
      factor * target :=
    Fraction.Order.Arithmetic.mul_le_mul_direct coefficientLe
      interval.lowerSq_le_target
      (Fraction.Order.Arithmetic.pow_nonneg_direct
        interval.lowerPositive.le 2)
      ((show (0 : Fraction.Rational) ≤ 1 by decide).trans factorGreater.le)
  exact
    { radius := interval.upper
      radiusPositive := interval.upperPositive
      target_lt_square := interval.target_lt_upperSq
      square_le_factor_target := by
        calc
          interval.upper ^ 2 ≤ ((1 + gap) * interval.lower) ^ 2 :=
            upperSqLe
          _ = (1 + gap) ^ 2 * interval.lower ^ 2 := by ring1
          _ ≤ factor * target := productLe }

end Purelib.Approximation.Rational.SquareBracket.Factor

end
