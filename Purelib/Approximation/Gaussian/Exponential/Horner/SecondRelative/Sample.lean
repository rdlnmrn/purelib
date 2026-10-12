module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Exponential.Horner.Basic
import Purelib.Approximation.Gaussian.Exponential.Horner.Bounds
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Exponential

open Purelib.Approximation.Rational

open Purelib.Data.Gaussian

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the exponential

The relative exponential is not introduced by dividing by its argument.
Instead, `expRelSample z n` is the already finite inner Horner program, and
the factorization

`expSample z n - 1 = z * expRelSample z n`

is proved at every displayed depth, including `z = 0`.  A second shifted
Horner program gives a quadratic remainder.  All approximation objects below
contain only Gaussian-rational samples, rational squared-error allowances,
and terminating natural-number refinement programs.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Horner.SecondRelative.Sample

/-! ## A quadratic relative remainder -/

/-- The finite program for the second relative exponential. Its intended identity is `expRel z - 1 = z * expSecondRel
z`; the definition itself is a shifted finite Horner program, not a quotient. -/
def expSecondRelSample (z :
  Canonical) (index : Nat) : Canonical :=
  Scale.scale (1 / 2)
    (Horner.Basic.horner z 3 index)

/-- The rational error scale for second-relative exponential samples is five halves. -/
def expSecondRelErrorScale :
  Fraction.Rational := 5 / 2

/-- The second-relative exponential error scale is nonnegative. -/
theorem expSecondRelErrorScale_nonneg :
    0 ≤ expSecondRelErrorScale := by decide

/-- Subtracting second-relative exponential samples equals one half of the difference between their inner Horner
samples. -/
private theorem expSecondRelSample_sub (z
  : Canonical) (left right : Nat) :
    expSecondRelSample z left -
      expSecondRelSample z right =
      Scale.scale (1 / 2)
        (Horner.Basic.horner z 3 left -
          Horner.Basic.horner z 3 right) := by
  apply Data.Gaussian.Basic.ext <;>
    simp only [expSecondRelSample, Scale.scale_re,
      Scale.scale_im, Basic.sub_re, Basic.sub_im] <;> ring1

/-- Later second-relative exponential samples on the unit disk stay within the earlier index's scale-five-halves
quarter-radius allowance. -/
theorem expSecondRelSample_later_close {z
  : Canonical}
    (unitInput : Data.Gaussian.Norm.Basic.normSq z ≤ 1) {earlier later : Nat}
    (order : earlier ≤ later) :
    Data.Gaussian.Norm.Basic.normSq
        (expSecondRelSample z later -
          expSecondRelSample z earlier) ≤
      Geometric.Basic.quarterRadius
        expSecondRelErrorScale earlier := by
  obtain ⟨extra, rfl⟩ : ∃ extra, later = earlier + extra :=
    ⟨later - earlier, (Data.Nat.Subtraction.add_sub_of_le order).symm⟩
  rw [expSecondRelSample_sub, Scale.normSq_scale]
  have close := Horner.Bounds.horner_add_depth_close z unitInput
    earlier extra 3 (by decide)
  calc
    (1 / 2 : Fraction.Rational) ^ 2 *
          Data.Gaussian.Norm.Basic.normSq
            (Horner.Basic.horner z 3 (earlier + extra) -
              Horner.Basic.horner z 3 earlier) ≤
        (1 / 2 : Fraction.Rational) ^ 2 *
          (10 * (1 / 4 : Fraction.Rational) ^ earlier) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct close
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    _ = Geometric.Basic.quarterRadius
        expSecondRelErrorScale earlier := by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow]
      dsimp only [expSecondRelErrorScale]
      rw [← Fraction.Field.mul_assoc,
        show (1 / 2 : Fraction.Rational) ^ 2 * 10 = 5 / 2 by decide]

/-- Every second-relative exponential sample on the unit disk has squared norm at most one. -/
theorem expSecondRelSample_bounded {z :
  Canonical}
    (unitInput : Data.Gaussian.Norm.Basic.normSq z ≤ 1) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (expSecondRelSample z index) ≤ 1 := by
  rw [expSecondRelSample, Scale.normSq_scale]
  calc
    (1 / 2 : Fraction.Rational) ^ 2 *
          Data.Gaussian.Norm.Basic.normSq (Horner.Basic.horner z 3 index) ≤
        (1 / 2 : Fraction.Rational) ^ 2 * 4 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Horner.Bounds.horner_bounded z unitInput index 3
          (by decide))
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    _ = 1 := by decide
end Purelib.Approximation.Gaussian.Exponential.Horner.SecondRelative.Sample

end
