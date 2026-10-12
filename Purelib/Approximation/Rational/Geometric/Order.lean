module

import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation.Rational

open Purelib.Data.Rat

/-!
# Finite stage order for quarter-radius allowances

At a nonnegative scale, advancing one finite quarter-power stage cannot increase
the original displayed radius.
-/

@[expose] public section

namespace Purelib.Approximation.Rational.Geometric.Order

/-- A successor stage has no larger quarter-radius at a nonnegative scale. -/
theorem quarterRadius_succ_le (scale :
  Fraction.Rational)
    (scaleNonnegative : 0 ≤ scale) (index : Nat) :
    Geometric.Basic.quarterRadius scale (index + 1) ≤
      Geometric.Basic.quarterRadius scale index := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ]
  calc
    scale * ((1 / 4 : Fraction.Rational) ^ index * (1 / 4)) =
        (scale * (1 / 4 : Fraction.Rational) ^ index) * (1 / 4) := by ring1
    _ ≤ (scale * (1 / 4 : Fraction.Rational) ^ index) * 1 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide)
        (Fraction.Order.Arithmetic.mul_nonneg_direct scaleNonnegative
          (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) index))
    _ = scale * (1 / 4 : Fraction.Rational) ^ index :=
      Fraction.Field.mul_one_direct _

end Purelib.Approximation.Rational.Geometric.Order
