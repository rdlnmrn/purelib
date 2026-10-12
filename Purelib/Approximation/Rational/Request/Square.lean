module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

section
public section

/-!
# One-sided rational pairs as ordinary CCL processes

This CCL-side bridge converts a lower/upper rational pair only when it carries
the explicit finite gap modulus in `FiniteMeasure.LocatedPair`.  The bare
one-sided processes remain rate-free.

The requested CCL squared-error target is translated to the strictly smaller
rational gap `target / (target + 1)`.  Its square is below `target`, so the
construction needs no square root, completion, limit, or unbounded search.
-/

namespace Purelib.Approximation.Rational.Request.Square

/-- A positive, subunit rational gap budget computed from a CCL squared-error target without taking a square root. -/
@[expose] def gapTarget (target : Fraction.Rational) : Fraction.Rational :=
  target / (target + 1)

/-- A positive squared-error target gives a positive rational gap target. -/
theorem gapTarget_pos {target : Fraction.Rational} (positive : 0 < target) :
    0 < Approximation.Rational.Request.Square.gapTarget target :=
  Fraction.Order.Field.div_pos_direct positive
    (Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct positive (by decide))

/-- The gap target associated with a positive target is strictly below one. -/
theorem gapTarget_lt_one {target : Fraction.Rational} (positive : 0 < target) :
    Approximation.Rational.Request.Square.gapTarget target < 1 := by
  apply (Fraction.Order.Field.div_lt_iff_pos
    (Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct positive (by decide))).2
  calc
    target < target + 1 :=
      (by
        have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct (by decide : (0 : Fraction.Rational) < 1)
          target
        exact (show target = target + 0 by ring1).trans_lt shifted)
    _ = 1 * (target + 1) := by ring1

/-- The gap target is strictly smaller than its positive input target. -/
theorem gapTarget_lt_target {target : Fraction.Rational} (positive : 0 < target) :
    Approximation.Rational.Request.Square.gapTarget target < target := by
  apply (Fraction.Order.Field.div_lt_iff_pos
    (Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct positive (by decide))).2
  have squarePositive : 0 < target ^ 2 := by
    exact Fraction.Order.Arithmetic.pow_pos_direct positive 2
  calc
    target < target + target ^ 2 := (by
      have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct squarePositive target
      exact (show target = target + 0 by ring1).trans_lt shifted)
    _ = target * (target + 1) := by ring1

/-- The square of the gap target lies strictly below its positive input target. -/
theorem gapTarget_sq_lt_target {target : Fraction.Rational} (positive : 0 < target) :
    Approximation.Rational.Request.Square.gapTarget target ^ 2 < target := by
  have gapPositive := Approximation.Rational.Request.Square.gapTarget_pos positive
  have squareLtGap : Approximation.Rational.Request.Square.gapTarget target ^ 2 <
    Approximation.Rational.Request.Square.gapTarget target := by
    rw [pow_two]
    calc
      Approximation.Rational.Request.Square.gapTarget target * Approximation.Rational.Request.Square.gapTarget target <
        1 * Approximation.Rational.Request.Square.gapTarget target :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
          (Approximation.Rational.Request.Square.gapTarget_lt_one positive) gapPositive
      _ = Approximation.Rational.Request.Square.gapTarget target := by ring1
  exact squareLtGap.trans (Approximation.Rational.Request.Square.gapTarget_lt_target positive)

/-- A nonnegative rational below the gap target has square strictly below the positive target. -/
theorem square_lt_target_of_gap_lt {value target : Fraction.Rational}
    (valueNonnegative : 0 ≤ value) (targetPositive : 0 < target)
    (small : value < Approximation.Rational.Request.Square.gapTarget target) : value ^ 2 < target := by
  have gapPositive := Approximation.Rational.Request.Square.gapTarget_pos targetPositive
  have firstStep : value * value ≤ value * Approximation.Rational.Request.Square.gapTarget target :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      small.le valueNonnegative
  have secondStep : value * Approximation.Rational.Request.Square.gapTarget target <
      Approximation.Rational.Request.Square.gapTarget target * Approximation.Rational.Request.Square.gapTarget target :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      small gapPositive
  rw [pow_two]
  exact firstStep.trans_lt
    (secondStep.trans (by
      simpa only [pow_two] using Approximation.Rational.Request.Square.gapTarget_sq_lt_target targetPositive))

end Purelib.Approximation.Rational.Request.Square

end
