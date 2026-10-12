module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.Gaussian.Field
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Data.GaussianInt.Nearest
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Tactic.Ring
import Purelib.Algebra.NatCast

public section

namespace Purelib.Data.GaussianInt.Division.Nearest

open Purelib.Algebra

open Purelib.Data

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Basic

open Purelib.Data.Gaussian.Norm

open Purelib.Data.GaussianInt

open Purelib.Data.Rat.Fraction

open Purelib.Data.Rat.Fraction.Basic

open Purelib.Data.Rat.Fraction.Cast

open Purelib.Data.Rat.Fraction.Order

/-- Select the deterministic nearest Gaussian integer to the exact value of a displayed
fraction. -/
@[expose] def digit (fraction : Fraction) : GaussianInt :=
  Nearest.nearest fraction.value

/-- Compute the integral Euclidean remainder from the retained numerator, denominator and
selected digit. -/
@[expose] def remainder (fraction : Fraction) : GaussianInt :=
  fraction.numerator - Division.Nearest.digit fraction * fraction.denominator

/-- The selected digit times the original denominator plus the integral remainder
recovers the original numerator. -/
theorem digit_mul_denominator_add_remainder (fraction : Fraction) :
    Division.Nearest.digit fraction * fraction.denominator + Division.Nearest.remainder fraction =
      fraction.numerator := by
  apply GaussianInt.ext <;>
    simp only [Division.Nearest.remainder,
      GaussianInt.add_re,
      GaussianInt.add_im,
      GaussianInt.sub_re,
      GaussianInt.sub_im,
      GaussianInt.mul_re,
      GaussianInt.mul_im] <;>
    ring1

/-- Read the centered-square rational residual of the displayed fraction's exact value. -/
@[expose] def residual (fraction : Fraction) : Canonical :=
  GaussianInt.Nearest.remainder fraction.value

/-- The embedded integral remainder is the rational residual times the original embedded
denominator. -/
theorem remainder_toGaussian (fraction : Fraction) :
    GaussianInt.toGaussian (Division.Nearest.remainder fraction) =
      Division.Nearest.residual fraction * GaussianInt.toGaussian fraction.denominator := by
  rw [Division.Nearest.remainder, GaussianInt.toGaussian_sub, GaussianInt.toGaussian_mul]
  rw [← fraction.value_mul_denominator]
  apply Basic.ext <;>
    simp only [Division.Nearest.residual, Division.Nearest.digit, GaussianInt.Nearest.remainder,
      Basic.sub_re,
      Basic.sub_im,
      Basic.mul_re,
      Basic.mul_im] <;>
    ring1

/-- The integral remainder quadrance equals residual quadrance times the original
denominator quadrance.

Both natural quadrances are cast into the exact Rational carrier, preserving the
displayed residual and original denominator. -/
theorem remainder_norm_identity (fraction : Fraction) :
    (GaussianInt.normNat (Division.Nearest.remainder fraction) : Rat.Fraction.Basic.Rational) =
      Canonical.normSq (Division.Nearest.residual fraction) *
        (GaussianInt.normNat fraction.denominator : Rat.Fraction.Basic.Rational) := by
  rw [← GaussianInt.normSq_toGaussian, Division.Nearest.remainder_toGaussian, Basic.normSq_mul,
    GaussianInt.normSq_toGaussian]
  rw [Basic.normSq_eq_canonical]

/-- Nearest Gaussian division strictly decreases the nonzero denominator's natural
quadrance.

The rational residual quadrance is at most one half, so multiplying by the positive
denominator norm gives a strict natural remainder bound. -/
theorem remainder_norm_lt_denominator (fraction : Fraction) :
    GaussianInt.normNat (Division.Nearest.remainder fraction) < GaussianInt.normNat fraction.denominator := by
  have denominatorPositive :
      (0 : Rat.Fraction.Basic.Rational) < (GaussianInt.normNat fraction.denominator : Rat.Fraction.Basic.Rational) :=
    Order.natCast_pos_direct
      (GaussianInt.normNat_pos fraction.denominatorNonzero)
  have residualBound :=
    Nearest.remainder_normSq_le_half fraction.value
  rw [Basic.normSq_eq_canonical] at residualBound
  have scaledBound :=
    Arithmetic.mul_le_mul_of_nonneg_right_direct
      residualBound denominatorPositive.le
  have halfStrict :=
    Arithmetic.mul_lt_mul_of_pos_right_direct
      (show (1 / 2 : Rat.Fraction.Basic.Rational) < 1 by decide) denominatorPositive
  have castStrict :
      (GaussianInt.normNat (Division.Nearest.remainder fraction) : Rat.Fraction.Basic.Rational) <
        (GaussianInt.normNat fraction.denominator : Rat.Fraction.Basic.Rational) := by
    calc
      (GaussianInt.normNat (Division.Nearest.remainder fraction) : Rat.Fraction.Basic.Rational) =
          Canonical.normSq (Division.Nearest.residual fraction) *
            (GaussianInt.normNat fraction.denominator : Rat.Fraction.Basic.Rational) :=
        Division.Nearest.remainder_norm_identity fraction
      _ ≤ (1 / 2 : Rat.Fraction.Basic.Rational) *
          (GaussianInt.normNat fraction.denominator : Rat.Fraction.Basic.Rational) := scaledBound
      _ < 1 * (GaussianInt.normNat fraction.denominator : Rat.Fraction.Basic.Rational) := halfStrict
      _ = (GaussianInt.normNat fraction.denominator : Rat.Fraction.Basic.Rational) := by ring1
  exact (Order.natCast_lt_iff_direct).1 castStrict

/-- A nonzero integral remainder forces the corresponding rational residual to be
nonzero. -/
theorem residual_ne_zero {fraction : Fraction}
    (remainderNonzero : Division.Nearest.remainder fraction ≠ 0) :
    Division.Nearest.residual fraction ≠ 0 := by
  intro residualZero
  have identity := Division.Nearest.remainder_toGaussian fraction
  rw [residualZero, Basic.zero_mul] at identity
  exact remainderNonzero (toGaussian_eq_zero.mp identity)

/-- Twice the integral remainder quadrance is at most the original denominator quadrance.

This exact natural inequality transports the centered-square residual bound through
the nonzero displayed denominator. -/
theorem twice_remainder_norm_le_denominator (fraction : Fraction) :
    2 * GaussianInt.normNat (Division.Nearest.remainder fraction) ≤ GaussianInt.normNat fraction.denominator := by
  apply (Order.natCast_le_iff_direct).1
  have denominatorNonnegative : (0 : Rat.Fraction.Basic.Rational) ≤
      (GaussianInt.normNat fraction.denominator : Rat.Fraction.Basic.Rational) := by
    exact Order.natCast_le_direct (Nat.zero_le _)
  have residualBound :=
    Nearest.remainder_normSq_le_half fraction.value
  rw [Basic.normSq_eq_canonical] at residualBound
  have scaledBound :=
    Arithmetic.mul_le_mul_of_nonneg_right_direct
      residualBound denominatorNonnegative
  calc
    ((2 * GaussianInt.normNat (Division.Nearest.remainder fraction) : Nat) : Rat.Fraction.Basic.Rational) =
        2 * (GaussianInt.normNat (Division.Nearest.remainder fraction) : Rat.Fraction.Basic.Rational) := by
      rw [NatCast.mul, Nat.cast_ofNat]
    _ = 2 *
        (Canonical.normSq (Division.Nearest.residual fraction) *
          (GaussianInt.normNat fraction.denominator : Rat.Fraction.Basic.Rational)) := by
      rw [Division.Nearest.remainder_norm_identity]
    _ ≤ 2 *
        ((1 / 2 : Rat.Fraction.Basic.Rational) *
          (GaussianInt.normNat fraction.denominator : Rat.Fraction.Basic.Rational)) := by
      exact Arithmetic.mul_le_mul_of_nonneg_left_direct
        scaledBound (by decide)
    _ = ((2 : Rat.Fraction.Basic.Rational) * (1 / 2)) *
        (GaussianInt.normNat fraction.denominator : Rat.Fraction.Basic.Rational) := by ring1
    _ = (GaussianInt.normNat fraction.denominator : Rat.Fraction.Basic.Rational) := by
      have twoHalf : (2 : Rat.Fraction.Basic.Rational) * (1 / 2) = 1 := by decide
      rw [twoHalf, Field.one_mul]

/-- The displayed fraction's exact value is its selected integral digit plus its rational
residual. -/
theorem value_eq_digit_add_residual (fraction : Fraction) :
    fraction.value = GaussianInt.toGaussian (Division.Nearest.digit fraction) + Division.Nearest.residual fraction := by
  apply Basic.ext <;>
    simp only [Division.Nearest.residual, Division.Nearest.digit, GaussianInt.Nearest.remainder,
      Basic.add_re,
      Basic.add_im,
      Basic.sub_re,
      Basic.sub_im] <;>
    ring1

end Purelib.Data.GaussianInt.Division.Nearest
