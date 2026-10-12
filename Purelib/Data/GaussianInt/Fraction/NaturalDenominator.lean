module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Conjugate
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Norm.Basic
import Mathlib.Algebra.Group.Nat.Defs

open Purelib.Data

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Basic.Canonical.Fraction

open Purelib.Data.GaussianInt

open Purelib.Data.GaussianInt.Fraction

section
@[expose] public section

/-!
# Intrinsic Gaussian-denominator residual bounds

This module repeats the finite homogeneous-evaluation argument with a
displayed Gaussian-integer denominator.  It also gives exact conversions in
both directions between Gaussian-denominator records and the older positive
natural common-denominator records.
-/

namespace Purelib.Data.GaussianInt.Fraction.NaturalDenominator

/-! ## Exact presentation conversions -/

/-- Convert a positive natural common denominator into the corresponding real
Gaussian-integer denominator.

Retain the original numerator and derive denominator nonzeroness directly from the
original positive natural bound. -/
def ofCommon (fraction : NaturalDenominator) : Fraction :=
  { numerator := fraction.numerator
    denominator := GaussianInt.ofNat fraction.denominator
    denominatorNonzero := by
      intro zero
      have realZero := congrArg (fun value : GaussianInt => value.re) zero
      exact (Nat.ne_of_gt fraction.denominatorPositive)
        (Int.ofNat.inj realZero) }

/-- Embedding a natural common denominator preserves the original squared denominator
height. -/
@[simp] theorem ofCommon_height (fraction :
  NaturalDenominator) :
    (ofCommon fraction).height = fraction.height := by
  exact GaussianInt.normNat_ofNat fraction.denominator

/-- Embedding a natural common denominator preserves the original exact Gaussian fraction
value. -/
theorem ofCommon_value (fraction : NaturalDenominator) :
    (ofCommon fraction).value = fraction.value := by
  apply Field.mul_right_cancel_of_ne
    (show GaussianInt.toGaussian (GaussianInt.ofNat fraction.denominator) ≠ 0 by
      intro zero
      exact (ofCommon fraction).denominatorNonzero
        (toGaussian_eq_zero.mp zero))
  calc
    (ofCommon fraction).value * GaussianInt.toGaussian (GaussianInt.ofNat fraction.denominator) =
        GaussianInt.toGaussian fraction.numerator := by
      simpa only [ofCommon] using (ofCommon fraction).value_mul_denominator
    _ = fraction.value * GaussianInt.toGaussian (GaussianInt.ofNat fraction.denominator) :=
      fraction.value_mul_denominator.symm

/-- Rationalize a displayed Gaussian denominator by multiplying through by its conjugate.

The new numerator retains that explicit product and the positive natural denominator
is the original Gaussian denominator's quadrance. -/
def toCommon (fraction : Fraction) : NaturalDenominator :=
  { numerator := fraction.numerator *
      GaussianInt.conj fraction.denominator
    denominator := GaussianInt.normNat fraction.denominator
    denominatorPositive := GaussianInt.normNat_pos fraction.denominatorNonzero }

/-- Conjugate rationalization squares the original displayed denominator height. -/
@[simp] theorem toCommon_height (fraction : Fraction) :
    (toCommon fraction).height = fraction.height ^ 2 := by
  rfl

/-- Conjugate rationalization preserves the exact Gaussian fraction value. -/
theorem toCommon_value (fraction : Fraction) :
    (toCommon fraction).value = fraction.value := by
  let denominatorNorm := GaussianInt.normNat fraction.denominator
  have denominatorGaussianNonzero : GaussianInt.toGaussian (GaussianInt.ofNat denominatorNorm) ≠ 0 := by
    intro zero
    have integerZero := toGaussian_eq_zero.mp zero
    have realZero := congrArg (fun value : GaussianInt => value.re) integerZero
    exact (Nat.ne_of_gt (GaussianInt.normNat_pos fraction.denominatorNonzero))
      (Int.ofNat.inj realZero)
  apply Field.mul_right_cancel_of_ne
    denominatorGaussianNonzero
  calc
    (toCommon fraction).value * GaussianInt.toGaussian (GaussianInt.ofNat denominatorNorm) =
        GaussianInt.toGaussian
          (fraction.numerator *
            GaussianInt.conj
              fraction.denominator) :=
      (toCommon fraction).value_mul_denominator
    _ = GaussianInt.toGaussian fraction.numerator *
          GaussianInt.toGaussian
            (GaussianInt.conj
              fraction.denominator) :=
      GaussianInt.toGaussian_mul _ _
    _ = (fraction.value * GaussianInt.toGaussian fraction.denominator) *
          GaussianInt.toGaussian
            (GaussianInt.conj
              fraction.denominator) := by
      rw [fraction.value_mul_denominator]
    _ = fraction.value *
          (GaussianInt.toGaussian fraction.denominator *
            GaussianInt.toGaussian
              (GaussianInt.conj
                fraction.denominator)) := by
      rw [Basic.mul_assoc]
    _ = fraction.value * GaussianInt.toGaussian (GaussianInt.ofNat denominatorNorm) := by
      rw [← GaussianInt.toGaussian_mul,
        GaussianInt.mul_conj]

end Purelib.Data.GaussianInt.Fraction.NaturalDenominator

end
