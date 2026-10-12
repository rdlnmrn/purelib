module
import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Calculus.Jet.Quadratic.Bounds
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Field.Defs

section
@[expose] public section

/-!
# Compositional quadratic-remainder certificates

A certificate is a finite tuple of displayed Gaussian rationals.  It records
an exact first-order expansion at one displayed increment and a rational
quadrance bound for its remainder.  Addition, negation, scalar multiplication,
and composition compute new factors from old ones.  Thus a composite
calculation retains an executable remainder budget instead of appealing to
limits, infinitesimals, or an unspecified big-O relation.
-/

namespace Purelib.Calculus.Jet.Quadratic.Basic
namespace Certificate

open Purelib.Calculus.Jet.Quadratic.Basic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Compose an inner expansion with an outer expansion at its actual displacement.

The inner increment must have quadrance at most one. The composed slope is the product of slopes, the remainder is the
inner remainder times the outer slope plus the outer remainder, and the factor uses the inner sensitivity to transport
the outer bound. -/
def compose {increment : Basic.Canonical}
    (inner : Certificate increment)
    (outer : Certificate (inner.output - inner.base))
    (unit : Basic.Canonical.normSq increment ≤ 1) : Certificate increment := by
  let sensitivity := inner.sensitivity
  let factor := 2 *
    (Basic.Canonical.normSq outer.slope * inner.factor + outer.factor * sensitivity ^ 2)
  let remainder := inner.remainder * outer.slope + outer.remainder
  have factorNonnegative : 0 ≤ factor := by
    dsimp only [factor]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          (Basic.Canonical.normSq_nonneg outer.slope) inner.factor_nonneg)
        (Fraction.Order.Arithmetic.mul_nonneg_direct outer.factor_nonneg
          (Fraction.Order.Arithmetic.pow_nonneg_direct
            inner.sensitivity_nonneg 2)))
  refine
    { base := outer.base
      slope := inner.slope * outer.slope
      output := outer.output
      remainder := remainder
      expansion := ?_
      factor := factor
      factor_nonneg := factorNonnegative
      remainder_le := ?_ }
  · dsimp only [remainder]
    rw [← outer.expansion, ← inner.expansion]
    apply Basic.ext <;>
      simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1
  · have innerMovement := inner.movement_le unit
    have movementSquare :
        Basic.Canonical.normSq (inner.output - inner.base) ^ 2 ≤
          (sensitivity * Basic.Canonical.normSq increment) ^ 2 :=
      Fraction.Order.Arithmetic.pow_le_pow_direct
        (Basic.Canonical.normSq_nonneg (inner.output - inner.base)) innerMovement 2
    have firstBound :
        Basic.Canonical.normSq (inner.remainder * outer.slope) ≤
          (Basic.Canonical.normSq outer.slope * inner.factor) * Basic.Canonical.normSq increment ^ 2 := by
      rw [Basic.Canonical.normSq_mul]
      calc
        Basic.Canonical.normSq inner.remainder * Basic.Canonical.normSq outer.slope ≤
            (inner.factor * Basic.Canonical.normSq increment ^ 2) *
              Basic.Canonical.normSq outer.slope :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            inner.remainder_le (Basic.Canonical.normSq_nonneg outer.slope)
        _ = (Basic.Canonical.normSq outer.slope * inner.factor) *
            Basic.Canonical.normSq increment ^ 2 := by ring1
    have secondBound : Basic.Canonical.normSq outer.remainder ≤
        (outer.factor * sensitivity ^ 2) * Basic.Canonical.normSq increment ^ 2 := by
      calc
        Basic.Canonical.normSq outer.remainder ≤
            outer.factor * Basic.Canonical.normSq (inner.output - inner.base) ^ 2 :=
          outer.remainder_le
        _ ≤ outer.factor * (sensitivity * Basic.Canonical.normSq increment) ^ 2 :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            movementSquare outer.factor_nonneg
        _ = (outer.factor * sensitivity ^ 2) *
            Basic.Canonical.normSq increment ^ 2 := by ring1
    dsimp only [remainder, factor]
    calc
      Basic.Canonical.normSq (inner.remainder * outer.slope + outer.remainder) ≤
          2 * (Basic.Canonical.normSq (inner.remainder * outer.slope) +
            Basic.Canonical.normSq outer.remainder) := by
              simpa only [Norm.Basic.normSq_eq_canonical] using
                Norm.Bounds.normSq_add_le_two (inner.remainder * outer.slope) outer.remainder
      _ ≤ 2 *
          (((Basic.Canonical.normSq outer.slope * inner.factor) *
              Basic.Canonical.normSq increment ^ 2) +
            ((outer.factor * sensitivity ^ 2) *
              Basic.Canonical.normSq increment ^ 2)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstBound secondBound) (by decide)
      _ = 2 *
          (Basic.Canonical.normSq outer.slope * inner.factor +
            outer.factor * sensitivity ^ 2) * Basic.Canonical.normSq increment ^ 2 := by
        ring1
end Certificate

end Purelib.Calculus.Jet.Quadratic.Basic

end
