module

import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation.Rational

open Purelib.Data.Rat

/-!
# Exact scale arithmetic for quarter-radius allowances

The retained finite index is shared by every original radius. Multiplication,
addition and a compensating factor four preserve their displayed scalar equations.
-/

@[expose] public section

namespace Purelib.Approximation.Rational.Geometric.Scale

/-- Move a rational amplification of the scale-ten quarter-radius into its scale. -/
theorem amplified_quarter (factor : Fraction.Rational) (depth :
  Nat) :
    factor * Geometric.Basic.quarterRadius 10 depth = Geometric.Basic.quarterRadius (10 * factor) depth := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

/-- Scaling by four exactly compensates for one additional quarter-radius stage. -/
theorem
  quarterRadius_four_mul_succ
  (scale : Fraction.Rational)
    (index : Nat) :
    Geometric.Basic.quarterRadius (4 * scale) (index + 1) =
      Geometric.Basic.quarterRadius scale index := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ]
  have quarterFour : (4 : Fraction.Rational) * (1 / 4) = 1 := by decide
  calc
    (4 * scale) * ((1 / 4 : Fraction.Rational) ^ index * (1 / 4)) =
        (scale * (1 / 4 : Fraction.Rational) ^ index) * (4 * (1 / 4)) := by
      ring1
    _ = scale * (1 / 4 : Fraction.Rational) ^ index := by
      rw [quarterFour]
      ring1

/-- Scaling a quarter-radius scale by four scales the radius by four. -/
theorem
  quarterRadius_four_mul
  (scale : Fraction.Rational) (index : Nat) :
    Geometric.Basic.quarterRadius (4 * scale) index =
      4 * Geometric.Basic.quarterRadius scale index := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

/-- The quarter-radius at twice the summed scale is twice the sum of the two quarter-radii. -/
theorem quarterRadius_sum_scale (left right
  : Fraction.Rational)
    (index : Nat) :
    Geometric.Basic.quarterRadius
        (2 * (left + right)) index =
      2 * (Geometric.Basic.quarterRadius left index +
        Geometric.Basic.quarterRadius right index) := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

end Purelib.Approximation.Rational.Geometric.Scale
