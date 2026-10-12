module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Choice-free completed-block chordal contraction

This file proves the affine two-tail part of the companion paper's completed
CCL block contraction.  The proof is entirely cross-multiplied over explicit
fractions; no square root, limit, supremum, or inherited ordered-field
division theorem is used.
-/

@[expose] public section

namespace Purelib.Data.Rat.BalancedRatio

open Purelib.Data
open Purelib.Data.Rat
/-- Compute twice a canonical Gaussian squared norm divided by the square of one plus that norm.

The denominator is the square of one plus the nonnegative squared norm, so it is strictly positive. The exact rational
factor lies at most one half and is positive precisely away from the zero input. -/
def factor (scale : Gaussian.Basic.Canonical) : Fraction.Rational :=
  2 * Gaussian.Basic.Canonical.normSq scale / (1 + Gaussian.Basic.Canonical.normSq scale) ^ 2

/-- The balanced squared-norm ratio is positive for a nonzero canonical Gaussian input. -/
theorem factor_pos {scale : Gaussian.Basic.Canonical} (scaleNonzero : scale ≠ 0) :
    0 < factor scale := by
  have scalePositive : 0 < Gaussian.Basic.Canonical.normSq scale := by
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
      Gaussian.Norm.Basic.normSq_pos scaleNonzero
  have numeratorPositive : 0 < 2 * Gaussian.Basic.Canonical.normSq scale :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) scalePositive
  have sumPositive : 0 < 1 + Gaussian.Basic.Canonical.normSq scale :=
    add_pos_of_pos_of_nonneg (by decide) (Gaussian.Basic.Canonical.normSq_nonneg scale)
  have denominatorPositive : 0 < (1 + Gaussian.Basic.Canonical.normSq scale) ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct sumPositive 2
  exact Fraction.Order.Field.div_pos_direct numeratorPositive
    denominatorPositive

/-- The balanced squared-norm ratio is at most one half for every canonical Gaussian input. -/
theorem factor_le_half (scale : Gaussian.Basic.Canonical) : factor
  scale ≤ 1 / 2 := by
  let length := Gaussian.Basic.Canonical.normSq scale
  have lengthNonnegative : 0 ≤ length := Gaussian.Basic.Canonical.normSq_nonneg scale
  have sumPositive : 0 < 1 + length :=
    add_pos_of_pos_of_nonneg (by decide) lengthNonnegative
  have denominatorPositive : 0 < (1 + length) ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct sumPositive 2
  rw [factor]
  apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := (2 : Fraction.Rational)) _ (by decide)
  have squareNonnegative :=
    Fraction.Order.Arithmetic.sq_nonneg_direct (1 - length)
  calc
    (2 * length) * 2 = 4 * length := by ring1
    _ ≤ 4 * length + (1 - length) ^ 2 :=
      le_add_of_nonneg_right squareNonnegative
    _ = (1 + length) ^ 2 := by ring1
    _ = ((1 / 2 : Fraction.Rational) * (1 + length) ^ 2) * 2 := by
      calc
        (1 + length) ^ 2 = 1 * (1 + length) ^ 2 := by ring1
        _ = ((1 / 2 : Fraction.Rational) * 2) * (1 + length) ^ 2 := by
          rw [show (1 / 2 : Fraction.Rational) * 2 = 1 by decide]
        _ = ((1 / 2 : Fraction.Rational) * (1 + length) ^ 2) * 2 := by ring1
end Purelib.Data.Rat.BalancedRatio

end
