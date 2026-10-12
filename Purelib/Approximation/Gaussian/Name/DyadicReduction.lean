module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.Bounds
public import Purelib.Approximation.Gaussian.Name.UnitDisk
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
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
import Purelib.Algebra.Semiring.Normalization

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Rat

open Purelib.Algebra

section
public section

/-!
# Automatic finite range reduction for the progressive exponential

This module makes the local construction a total exponential operator on
arithmetic CCL names.  One finite input ball from the CCL accuracy sidechannel
supplies a rational norm bound.  A logarithmic bounded scan chooses a
displayed natural exponent `k` for which division by `2^k` puts every
candidate in the unit disk.  The local exponential CCL name is then squared
exactly `k` times by the already proved CCL arithmetic operation.  The result
is again a productive CCL name.  No magnitude limit, completed input value,
or infinite functional equation is used; the bare raw bitstream is not asked
to provide quantitative accuracy by itself.
-/

namespace Purelib.Approximation.Gaussian.Name.DyadicReduction

/-- Computed dyadic range exponent.

The finite quarter-radius search reads the retained input quadrance bound and keeps its original starting index and unit
threshold. -/
@[expose] def rangeExponent (input : Gaussian.Name.Basic.Named) : Nat :=
  Search.firstQuarterBelow (Gaussian.Name.Bounds.inputBound input) 0 1

/-- The computed dyadic exponent reduces the retained input quadrance bound strictly below one. -/
theorem rangeExponent_accurate (input : Gaussian.Name.Basic.Named) :
    Geometric.Basic.quarterRadius (Gaussian.Name.Bounds.inputBound input)
      (rangeExponent input) < 1 :=
  Search.firstQuarterBelow_accurate
    (Gaussian.Name.Bounds.inputBound input) (Gaussian.Name.Bounds.inputBound_nonneg input) 0 1 (by decide)

/-- The positive power of two selected by the computed range-reduction exponent.

The denominator uses the retained range exponent and the original rational natural-power operation. -/
@[expose] def dyadicDenominator (input : Gaussian.Name.Basic.Named) : Fraction.Rational :=
  (2 : Fraction.Rational) ^ rangeExponent input

/-- The computed dyadic denominator is strictly positive. -/
theorem dyadicDenominator_pos (input : Gaussian.Name.Basic.Named) :
    0 < dyadicDenominator input :=
  Fraction.Order.Arithmetic.pow_pos_direct (by decide) (rangeExponent input)

/-- The real Gaussian reciprocal of the computed power-of-two denominator.

The exact Gaussian factor retains reciprocal real coordinate and zero imaginary coordinate. -/
@[expose] def inverseDyadic (input : Gaussian.Name.Basic.Named) : Data.Gaussian.Basic.Canonical :=
  ⟨1 / dyadicDenominator input, 0⟩

/-- The squared norm of the inverse dyadic factor is the scale-one quarter-radius at the computed exponent.

The original reciprocal denominator is the computed natural power of two; its squared norm equals the retained power of
one quarter. -/
theorem normSq_inverseDyadic (input : Gaussian.Name.Basic.Named) :
    Data.Gaussian.Norm.Basic.normSq (inverseDyadic input) =
      Geometric.Basic.quarterRadius 1
        (rangeExponent input) := by
  change (1 / dyadicDenominator input) ^ 2 + 0 ^ 2 =
    1 / (4 : Fraction.Rational) ^ rangeExponent input
  rw [show (0 : Fraction.Rational) ^ 2 = 0 by decide,
    Fraction.Field.add_comm _ 0,
    Fraction.Field.zero_add]
  rw [pow_two]
  calc
    1 / dyadicDenominator input * (1 / dyadicDenominator input) =
        (1 * 1) / (dyadicDenominator input * dyadicDenominator input) :=
      Fraction.Field.div_mul_div_direct _ _ _ _
    _ = 1 / (4 : Fraction.Rational) ^ rangeExponent input := by
      rw [Fraction.Field.one_mul]
      congr 1
      rw [dyadicDenominator, ← Semiring.Normalization.product_pow]
      congr 1

/-- Multiply the original input name by its exact computed inverse dyadic factor.

The original name multiplication consumes the exact cached dyadic factor and the original input owner. -/
@[expose] def scaledInput (input : Gaussian.Name.Basic.Named) : Gaussian.Name.Basic.Named :=
  Named.mul
    (Named.exact (inverseDyadic input))
    input

/-- The automatically scaled input satisfies the local unit-disk contract. -/
theorem scaledDomain (input : Gaussian.Name.Basic.Named) :
    UnitDisk (scaledInput input) where
  possible_unit := by
    intro value possible
    rcases possible with ⟨scaleValue, sourceValue,
      scalePossible, sourcePossible, rfl⟩
    change scaleValue = inverseDyadic input at scalePossible
    subst scaleValue
    rw [Data.Gaussian.Norm.Basic.normSq_mul, normSq_inverseDyadic]
    calc
      Geometric.Basic.quarterRadius 1 (rangeExponent input) *
          Data.Gaussian.Norm.Basic.normSq sourceValue ≤
        Geometric.Basic.quarterRadius 1 (rangeExponent input) *
          Gaussian.Name.Bounds.inputBound input :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Gaussian.Name.Bounds.possible_normSq_le_inputBound input sourcePossible)
          (Geometric.Basic.quarterRadius_nonneg (by decide) _)
      _ = Geometric.Basic.quarterRadius (Gaussian.Name.Bounds.inputBound input)
          (rangeExponent input) := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
      _ ≤ 1 := (rangeExponent_accurate input).le
end Purelib.Approximation.Gaussian.Name.DyadicReduction

end
