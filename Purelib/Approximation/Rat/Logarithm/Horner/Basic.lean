module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

public section

/-!
# Finite logarithm Horner approximation

For a displayed positive rational input in `[1/2,2]`, this module computes only
finite truncations of `2z(1 + z²/3 + z⁴/5 + ⋯)`, where
`z = (x - 1)/(x + 1)`.  The ellipsis is descriptive only: every definition
below is structural recursion with a natural depth, and every semantic
predicate has an explicit later finite index witness.  No completed logarithm,
infinite series, or limit is introduced.
-/

namespace Purelib.Approximation.Rat.Logarithm.Horner.Basic

/-- The rational Horner coefficient `(2 * index - 1) / (2 * index + 1)`.

At every positive index it lies between zero and one and is shared by the rational and Gaussian logarithm recurrences.
-/
@[expose] def Log.coefficient (index : Nat) : Fraction.Rational :=
  (2 * (index : Fraction.Rational) - 1) / (2 * (index : Fraction.Rational) + 1)

/-- At a positive natural index, the logarithm Horner coefficient is nonnegative.

At a positive index the retained numerator and denominator are nonnegative; the original rational division preserves
that bound. -/
theorem Log.coefficient_nonneg {index : Nat} (positive : 1 ≤ index) :
    0 ≤ Log.coefficient index := by
  have indexNonnegative : (0 : Fraction.Rational) ≤ (index : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct (Nat.zero_le index)
  have oneLeIndex : (1 : Fraction.Rational) ≤ (index : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct positive
  have indexLeTwice : (index : Fraction.Rational) ≤ 2 * (index : Fraction.Rational) := by
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide : (1 : Fraction.Rational) ≤ 2) indexNonnegative
    simpa only [Fraction.Field.one_mul] using scaled
  have numeratorNonnegative :
      0 ≤ 2 * (index : Fraction.Rational) - 1 :=
    Fraction.Order.Arithmetic.sub_nonneg_direct (oneLeIndex.trans indexLeTwice)
  have denominatorNonnegative :
      0 ≤ 2 * (index : Fraction.Rational) + 1 :=
    Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) indexNonnegative)
      (show (0 : Fraction.Rational) ≤ 1 by decide)
  exact Fraction.Order.Field.div_nonneg_direct numeratorNonnegative
    denominatorNonnegative

/-- Every logarithm Horner coefficient is at most one.

The retained positive denominator permits a direct scalar comparison of the same coefficient numerator with its
denominator. -/
theorem Log.coefficient_le_one (index : Nat) :
    Log.coefficient index ≤ 1 := by
  have indexNonnegative : (0 : Fraction.Rational) ≤ (index : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct (Nat.zero_le index)
  have denominatorPositive :
      0 < 2 * (index : Fraction.Rational) + 1 :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) indexNonnegative)
      (by decide)
  apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).mpr
  rw [Fraction.Field.one_mul]
  have constants : (-1 : Fraction.Rational) ≤ 1 := by decide
  have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct constants
    (2 * (index : Fraction.Rational))
  calc
    2 * (index : Fraction.Rational) - 1 = -1 + 2 * (index : Fraction.Rational) := by ring1
    _ ≤ 1 + 2 * (index : Fraction.Rational) := shifted
    _ = 2 * (index : Fraction.Rational) + 1 := by ring1

/-- Compute one canonical rational logarithm Horner step from the retained tail.

The step adds one to the product of the indexed coefficient, reduced squared argument and supplied tail. -/
@[expose] def step (w : Fraction.Rational) (index : Nat) (tail : Fraction.Rational) : Fraction.Rational :=
  Fraction.Basic.canonical (1 + Log.coefficient index * w * tail)

/-- The canonical Horner step equals its defining scalar expression. -/
theorem step_eq (w : Fraction.Rational) (index : Nat) (tail : Fraction.Rational) :
    step w index tail = 1 + Log.coefficient index * w * tail :=
  Fraction.Basic.canonical_eq _

/-- Evaluate the finite rational logarithm Horner recurrence.

The zero-depth value is one; each further step advances the coefficient index and consumes the recursively computed
tail. -/
@[expose] def horner (w : Purelib.Data.Rat.Fraction.Rational) : Nat → Nat → Purelib.Data.Rat.Fraction.Rational
  | _, 0 => 1
  | index, depth + 1 => Purelib.Approximation.Rat.Logarithm.Horner.Basic.step w index
    (Purelib.Approximation.Rat.Logarithm.Horner.Basic.horner w (index + 1) depth)

/-- The zero-depth rational logarithm Horner value is one. -/
@[simp] theorem horner_zero (w : Fraction.Rational) (index : Nat) :
    horner w index 0 = 1 := rfl

/-- A successor-depth Horner value applies one step to the next-index tail. -/
@[simp] theorem horner_succ (w : Fraction.Rational) (index depth : Nat) :
    horner w index (depth + 1) =
      step w index (horner w (index + 1) depth) := rfl
end Purelib.Approximation.Rat.Logarithm.Horner.Basic

end

public section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

namespace Purelib.Approximation.Rat.Logarithm.Horner.Basic.ComplexLog

/-- The shared rational coefficient used in the Gaussian logarithm Horner recurrence. -/
@[expose] def coefficient (index : Nat) : Fraction.Rational :=
  Log.coefficient index

/-- At a positive natural index, the logarithm Horner coefficient is nonnegative. -/
theorem coefficient_nonneg {index : Nat} (positive : 1 ≤ index) :
    0 ≤ ComplexLog.coefficient index :=
  Log.coefficient_nonneg positive

/-- Every logarithm Horner coefficient is at most one. -/
theorem coefficient_le_one (index : Nat) : ComplexLog.coefficient index ≤ 1 :=
  Log.coefficient_le_one index
end Purelib.Approximation.Rat.Logarithm.Horner.Basic.ComplexLog

end
