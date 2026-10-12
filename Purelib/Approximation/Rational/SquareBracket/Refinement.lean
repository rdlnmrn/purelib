module

import Purelib.Data.Rat.Fraction.Constants
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.SquareBracket.Basic
public import Purelib.Approximation.Rational.SquareBracket.Interval
import Purelib.Data.Rat.Fraction.Arithmetic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.SquareBracket

open Purelib.Approximation.Rational.SquareBracket.Basic

open Purelib.Approximation.Rational.SquareBracket.Interval

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

namespace Purelib.Approximation.Rational.SquareBracket.Interval.SquareInterval

/-- Perform exactly the displayed finite number of rational bisections.

Zero fuel retains the complete original interval. Each successor step bisects
the complete interval returned by the preceding finite refinement. -/
@[expose] def refine {target : Fraction.Rational}
    (interval : Interval.SquareInterval target) : Nat → Interval.SquareInterval target
  | 0 => interval
  | fuel + 1 => (interval.refine fuel).bisect

/-- One square-interval bisection cannot decrease its lower endpoint. -/
theorem lower_le_bisect_lower {target : Fraction.Rational}
    (interval : Interval.SquareInterval target) :
    interval.lower ≤ interval.bisect.lower := by
  by_cases midpointAbove : target < interval.midpoint ^ 2
  · unfold bisect
    rewrite [dif_pos midpointAbove]
    exact Fraction.Order.Basic.le_refl _
  · unfold bisect
    rewrite [dif_neg midpointAbove]
    exact interval.lower_le_midpoint

/-- Finite repeated bisection cannot decrease the original lower endpoint. -/
theorem lower_le_refine_lower {target : Fraction.Rational}
    (interval : Interval.SquareInterval target) (fuel : Nat) :
    interval.lower ≤ (interval.refine fuel).lower := by
  induction fuel with
  | zero => exact Fraction.Order.Basic.le_refl _
  | succ fuel inductionHypothesis =>
      exact inductionHypothesis.trans
        (lower_le_bisect_lower (interval.refine fuel))

/-- One square-interval bisection halves the endpoint width exactly. -/
theorem bisect_width {target : Fraction.Rational}
    (interval : Interval.SquareInterval target) :
    interval.bisect.upper - interval.bisect.lower =
      (1 / 2 : Fraction.Rational) * (interval.upper - interval.lower) := by
  by_cases midpointAbove : target < interval.midpoint ^ 2
  · unfold bisect
    rewrite [dif_pos midpointAbove]
    calc
      interval.midpoint -
          interval.lower =
          (1 / 2 : Fraction.Rational) * (interval.lower + interval.upper) -
            (1 / 2 : Fraction.Rational) *
              (interval.lower + interval.lower) := by
        simp only [SquareInterval.midpoint,
          Fraction.Arithmetic.normalizedMul_eq,
          Fraction.Arithmetic.normalizedAdd_eq]
        rw [Purelib.Data.Rat.Fraction.Constants.half_double interval.lower]
      _ = (1 / 2 : Fraction.Rational) *
          (interval.upper - interval.lower) := by ring1
  · unfold bisect
    rewrite [dif_neg midpointAbove]
    calc
      interval.upper -
          interval.midpoint =
          (1 / 2 : Fraction.Rational) *
              (interval.upper + interval.upper) -
            (1 / 2 : Fraction.Rational) *
              (interval.lower + interval.upper) := by
        simp only [SquareInterval.midpoint,
          Fraction.Arithmetic.normalizedMul_eq,
          Fraction.Arithmetic.normalizedAdd_eq]
        rw [Purelib.Data.Rat.Fraction.Constants.half_double interval.upper]
      _ = (1 / 2 : Fraction.Rational) *
          (interval.upper - interval.lower) := by ring1

/-- After the given finite number of bisections, the width is its original value times the corresponding half-power. -/
theorem refine_width {target : Fraction.Rational}
    (interval : Interval.SquareInterval target) (fuel : Nat) :
    (interval.refine fuel).upper - (interval.refine fuel).lower =
      (1 / 2 : Fraction.Rational) ^ fuel *
        (interval.upper - interval.lower) := by
  induction fuel with
  | zero =>
      simp only [refine, pow_zero, one_mul, -eq_self, -iff_self]
      rfl
  | succ fuel inductionHypothesis =>
      rw [refine, bisect_width,
        inductionHypothesis, pow_succ]
      ring1

end Purelib.Approximation.Rational.SquareBracket.Interval.SquareInterval

end
