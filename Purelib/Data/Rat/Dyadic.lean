module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Affine semantics of constructive raw-parser states

Parser constraints are evaluated on the current affine tail.  These finite
algebraic lemmas prove that decoder homographies compose in parser order and
that completing a raw block preserves the represented original input.
-/

namespace Purelib.Data.Rat.Dyadic

open Purelib.Data.Rat in
/-- A natural rational power of two is at most its successor power. -/
theorem two_pow_le_succ (count : Nat) :
    (2 : Fraction.Rational) ^ count ≤ (2 : Fraction.Rational) ^ (count + 1) := by
  have powerNonnegative : 0 ≤ (2 : Fraction.Rational) ^ count :=
    Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) count
  calc
    (2 : Fraction.Rational) ^ count = (2 : Fraction.Rational) ^ count * 1 := by ring1
    _ ≤ (2 : Fraction.Rational) ^ count * 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (by decide) powerNonnegative
    _ = (2 : Fraction.Rational) ^ (count + 1) := by
      rw [pow_succ]

open Purelib.Data
open Purelib.Data.Rat
/-- A successor dyadic power times a Gaussian squared norm below two gives a previous product below one. -/
theorem lower_low_active_of_radial_upper
    (count : Nat) (value : Gaussian.Basic.Canonical)
    (upper : (2 : Fraction.Rational) ^ (count + 1) * Gaussian.Basic.Canonical.normSq value < 2) :
    (2 : Fraction.Rational) ^ count * Gaussian.Basic.Canonical.normSq value < 1 := by
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := (2 : Fraction.Rational)) _ (by decide)
  calc
    ((2 : Fraction.Rational) ^ count * Gaussian.Basic.Canonical.normSq value) * 2 =
        (2 : Fraction.Rational) ^ (count + 1) * Gaussian.Basic.Canonical.normSq value := by
      rw [pow_succ]
      ring1
    _ < 2 := upper
    _ = (1 : Fraction.Rational) * 2 := by ring1

/-- A successor dyadic power times a Gaussian squared norm below one gives a previous product below one. -/
theorem lower_low_active_of_next
    (count : Nat) (value : Gaussian.Basic.Canonical)
    (next : (2 : Fraction.Rational) ^ (count + 1) * Gaussian.Basic.Canonical.normSq value < 1) :
    (2 : Fraction.Rational) ^ count * Gaussian.Basic.Canonical.normSq value < 1 := by
  let oldValue := (2 : Fraction.Rational) ^ count * Gaussian.Basic.Canonical.normSq value
  have oldNonnegative : 0 ≤ oldValue :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) count)
      (Gaussian.Basic.Canonical.normSq_nonneg value)
  have oneLeTwo : (1 : Fraction.Rational) ≤ 2 := by decide
  calc
    oldValue = oldValue * 1 := by ring1
    _ ≤ oldValue * 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        oneLeTwo oldNonnegative
    _ = (2 : Fraction.Rational) ^ (count + 1) * Gaussian.Basic.Canonical.normSq value := by
      dsimp only [oldValue]
      rw [pow_succ]
      ring1
    _ < 1 := next
end Purelib.Data.Rat.Dyadic

end

section
@[expose] public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

namespace Purelib.Data.Rat.Dyadic

open Purelib.Data.Rat in
/-- Multiplying the reciprocal of a power of two by one half gives the reciprocal of the successor power. -/
public theorem half_mul_inversePower (exponent : Nat) :
    (1 / 2 : Fraction.Rational) * (1 / (2 : Fraction.Rational) ^ exponent) =
      1 / (2 : Fraction.Rational) ^ (exponent + 1) := by
  rw [pow_succ]
  simp only [Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.one_mul]
  rw [Fraction.Field.inv_mul_direct,
    Fraction.Field.mul_comm]

end Purelib.Data.Rat.Dyadic

end

section
@[expose] public section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

namespace Purelib.Data.Rat.Dyadic

open Purelib.Data.Rat in
/-- The square of a natural power of one half equals the same power of one quarter. -/
public theorem half_pow_sq (depth : Nat) :
    ((1 / 2 : Fraction.Rational) ^ depth) ^ 2 =
      (1 / 4 : Fraction.Rational) ^ depth := by
  induction depth with
  | zero => decide
  | succ depth inductionHypothesis =>
      rw [pow_succ, pow_succ]
      calc
        (((1 / 2 : Fraction.Rational) ^ depth) * (1 / 2)) ^ 2 =
            (((1 / 2 : Fraction.Rational) ^ depth) ^ 2) * (1 / 2) ^ 2 := by
          ring1
        _ = (1 / 4 : Fraction.Rational) ^ depth * (1 / 2) ^ 2 := by
          rw [inductionHypothesis]
        _ = (1 / 4 : Fraction.Rational) ^ depth * (1 / 4) := by
          rw [show (1 / 2 : Fraction.Rational) ^ 2 = 1 / 4 by decide]

end Purelib.Data.Rat.Dyadic

end
