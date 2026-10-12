module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Rat.Logarithm.Horner.Basic
import Purelib.Approximation.Rat.Logarithm.Horner.Bounds
public import Purelib.Approximation.Rat.Logarithm.Horner.Sample
import Purelib.Approximation.Rat.Logarithm.Reduction
public import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rat.Logarithm

open Purelib.Approximation.Rat.Logarithm.Horner

open Purelib.Approximation.Rational

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.RationalEmbedding

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite logarithm Horner approximation

For a displayed positive rational input in `[1/2,2]`, this module computes only
finite truncations of `2z(1 + z²/3 + z⁴/5 + ⋯)`, where
`z = (x - 1)/(x + 1)`.  The ellipsis is descriptive only: every definition
below is structural recursion with a natural depth, and every semantic
predicate has an explicit later finite index witness.  No completed logarithm,
infinite series, or limit is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Rational.Sample

/-- Embed the finite rational logarithm Horner sample on the Gaussian real axis. -/
def sample (x : Fraction.Rational) (index : Nat) :
  Data.Gaussian.Basic.Canonical :=
  Log.real (Sample.sampleCoordinate x index)

/-- On the interval from one half to two, sample squared differences are bounded by those of the retained inner Horner
values. -/
theorem sample_difference_le_inner {x :
  Fraction.Rational} (halfLe : 1 / 2 ≤ x)
    (leTwo : x ≤ 2) (left right : Nat) :
    Data.Gaussian.Norm.Basic.normSq (sample x left -
      sample x right) ≤
      (Horner.Basic.horner (Reduction.squaredArgument x) 1 left -
        Horner.Basic.horner (Reduction.squaredArgument x) 1 right) ^ 2 := by
  rw [sample, sample,
    RationalEmbedding.normSq_real_sub, Sample.sampleCoordinate_eq, Sample.sampleCoordinate_eq]
  have factorSq : Sample.outputFactor x ^ 2 ≤ 1 :=
    Sample.outputFactor_sq_le_one halfLe leTwo
  rw [show Sample.outputFactor x * Horner.Basic.horner (Reduction.squaredArgument x) 1 left -
      Sample.outputFactor x * Horner.Basic.horner (Reduction.squaredArgument x) 1 right =
      Sample.outputFactor x * (Horner.Basic.horner (Reduction.squaredArgument x) 1 left -
        Horner.Basic.horner (Reduction.squaredArgument x) 1 right) by ring1,
    Fraction.Field.mul_pow_direct]
  have multiplied := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    factorSq
    (Fraction.Order.Arithmetic.sq_nonneg_direct
      (Horner.Basic.horner (Reduction.squaredArgument x) 1 left -
        Horner.Basic.horner (Reduction.squaredArgument x) 1 right))
  simpa only [Fraction.Field.one_mul] using multiplied

/-- Later finite logarithm samples stay within the earlier stage's scale-one quarter-radius allowance.

The original rational input lies between one half and two, and both indices remain explicit finite data. -/
theorem sample_later_close {x : Fraction.Rational}
  (halfLe : 1 / 2 ≤ x)
    (leTwo : x ≤ 2)
    {earlier later : Nat} (order : earlier ≤ later) :
    Data.Gaussian.Norm.Basic.normSq (sample x later -
      sample x earlier) ≤
      Geometric.Basic.quarterRadius 1 earlier := by
  let extra := later - earlier
  have laterEq : earlier + extra = later := Data.Nat.Subtraction.add_sub_of_le order
  rw [← laterEq]
  calc
    Data.Gaussian.Norm.Basic.normSq (sample x (earlier +
      extra) - sample x earlier) ≤
        (Horner.Basic.horner (Reduction.squaredArgument x) 1 (earlier + extra) -
          Horner.Basic.horner (Reduction.squaredArgument x) 1 earlier) ^ 2 :=
      sample_difference_le_inner halfLe leTwo _ _
    _ ≤ (1 / 4 : Fraction.Rational) ^ earlier :=
      Horner.Bounds.horner_add_depth_close (Reduction.squaredArgument_nonneg x)
        (Reduction.squaredArgument_le_ninth halfLe leTwo) earlier extra 1 (by decide)
    _ = Geometric.Basic.quarterRadius 1 earlier := by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow,
        Fraction.Field.one_mul]

/-- Every finite logarithm sample of an input between one half and two has squared norm at most four. -/
theorem sample_bounded {x : Fraction.Rational} (halfLe :
  1 / 2 ≤ x) (leTwo : x ≤ 2)
    (index : Nat) : Data.Gaussian.Norm.Basic.normSq (sample x
      index) ≤ 4 := by
  have inner := Horner.Bounds.horner_bounds (Reduction.squaredArgument_nonneg x)
    (Reduction.squaredArgument_le_ninth halfLe leTwo) index 1 (by decide)
  have innerSq : Horner.Basic.horner (Reduction.squaredArgument x) 1 index ^ 2 ≤ 4 := by
    calc
      Horner.Basic.horner (Reduction.squaredArgument x) 1 index ^ 2 ≤ (2 : Fraction.Rational) ^ 2 :=
        Fraction.Order.Arithmetic.pow_le_pow_direct
          ((by decide : (0 : Fraction.Rational) ≤ 1).trans inner.1) inner.2 2
      _ = 4 := by decide
  have innerSqNonnegative :
      0 ≤ Horner.Basic.horner (Reduction.squaredArgument x) 1 index ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  rw [sample, Data.Gaussian.Norm.Basic.normSq]
  change Sample.sampleCoordinate x index ^ 2 + 0 ^ 2 ≤ 4
  rw [Sample.sampleCoordinate_eq]
  calc
    (Sample.outputFactor x * Horner.Basic.horner (Reduction.squaredArgument x) 1 index) ^ 2 + 0 ^ 2 =
        (Sample.outputFactor x * Horner.Basic.horner (Reduction.squaredArgument x) 1 index) ^ 2 := by ring1
    _ = Sample.outputFactor x ^ 2 * Horner.Basic.horner (Reduction.squaredArgument x) 1 index ^ 2 := by
      rw [Fraction.Field.mul_pow_direct]
    _ ≤ 1 * 4 :=
      Fraction.Order.Arithmetic.mul_le_mul_direct
        (Sample.outputFactor_sq_le_one halfLe leTwo) innerSq
        innerSqNonnegative
        (by decide)
    _ = 4 := by decide
end Purelib.Approximation.Gaussian.Logarithm.Rational.Sample

end
