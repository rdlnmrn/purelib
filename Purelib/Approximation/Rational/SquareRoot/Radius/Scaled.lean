module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic

open Purelib.Data.Rat

@[expose] public section

/-!
# Finite rational square-root under-approximations at arbitrary scale

The original dyadic radius is at most one.  Above one, scan the reciprocal
target and rescale its radius, so the result does not discard the magnitude
of a large positive target.  Both branches are bounded rational calculations;
neither introduces a square-root object or a completed number.
-/

namespace Purelib.Approximation.Rational.SquareRoot.Radius.Scaled

/-- Compute a rational square-radius that respects the magnitude of a large target.

Below one it uses the bounded dyadic selector directly; at or above one it selects for the reciprocal target and
rescales the result. -/
def radius (target : Fraction.Rational) :
  Fraction.Rational :=
  if 1 ≤ target then target * Geometric.dyadicSquareRadius (1 / target)
  else Geometric.dyadicSquareRadius target

/-- A positive target gives a positive scaled square-radius. -/
theorem positive {target : Fraction.Rational} (positive :
  0 < target) : 0 < radius target := by
  unfold radius
  split
  · exact Fraction.Order.Arithmetic.mul_pos_direct positive (Geometric.dyadicSquareRadius_positive _)
  · exact Geometric.dyadicSquareRadius_positive _

/-- For a positive target, the scaled radius has square strictly below the target. -/
theorem sq_lt {target : Fraction.Rational} (positive : 0
  < target) : radius target ^ 2 < target := by
  unfold radius
  split
  · have smaller := Geometric.dyadicSquareRadius_sq_lt
      (Fraction.Order.Field.div_pos_direct (show (0 : Fraction.Rational) < 1 by decide) positive)
    have bound := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (Fraction.Order.Arithmetic.pow_pos_direct positive 2) smaller
    have cancel : target ^ 2 * (1 / target) = target := by
      calc
        target ^ 2 * (1 / target) = ((1 / target) * target) * target := by ring1
        _ = target := by
          rw [Fraction.Field.div_mul_cancel_of_ne 1 target (ne_of_gt positive),
            Fraction.Field.one_mul]
    rw [cancel] at bound
    exact (show (target * Geometric.dyadicSquareRadius (1 / target)) ^ 2 =
      target ^ 2 * Geometric.dyadicSquareRadius (1 / target) ^ 2 by ring1).symm ▸ bound
  · exact Geometric.dyadicSquareRadius_sq_lt positive

end Purelib.Approximation.Rational.SquareRoot.Radius.Scaled

end
