module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.NatCast
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Field

public import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Conjugate

import Purelib.Elab.Deriving.Repr
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Cast.Basic
import Purelib.Tactic.Ring

@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical.Fraction

open Purelib.Data.GaussianInt
open Purelib.Data (GaussianInt)

set_option genInjectivity false in
/-- Retain a Gaussian-integer numerator and a positive natural denominator.

The denominator positivity witness belongs to the stored denominator. The numerator is the original nominal
Gaussian-integer carrier; value and height are exact readbacks from these retained fields. -/
structure NaturalDenominator where
  /-- The retained Gaussian-integer numerator. -/ numerator : GaussianInt
  /-- The retained natural denominator. -/ denominator : Nat
  /-- Evidence that the retained natural denominator is strictly positive. -/ denominatorPositive : 0 < denominator

constructive_injectivity NaturalDenominator

derive_exposed_repr NaturalDenominator

namespace NaturalDenominator

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Read the Gaussian fraction by dividing both integer numerator coordinates by the retained natural denominator. -/
def value (fraction :
  NaturalDenominator) : Basic.Canonical :=
  ⟨(fraction.numerator.re : Fraction.Rational) / (fraction.denominator : Fraction.Rational),
    (fraction.numerator.im : Fraction.Rational) / (fraction.denominator : Fraction.Rational)⟩

open Purelib.Data.Gaussian in
/-- Compute the fraction height as the square of its retained natural denominator. -/
def height (fraction :
  NaturalDenominator) : Nat := fraction.denominator ^ 2

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained positive natural denominator has nonzero canonical rational cast. -/
theorem denominatorCast_ne (fraction :
  NaturalDenominator) :
    (fraction.denominator : Fraction.Rational) ≠ 0 := by
  intro zero
  have := Fraction.Cast.Compatibility.natCast_injective_direct
    (zero.trans (Nat.cast_zero).symm)
  exact (Nat.ne_of_gt fraction.denominatorPositive) this

section
open Purelib.Algebra
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Multiplying the Gaussian readback by the embedded denominator recovers the embedded numerator. -/
theorem value_mul_denominator (fraction :
  NaturalDenominator) :
    fraction.value * GaussianInt.toGaussian
        (GaussianInt.ofNat fraction.denominator) =
      GaussianInt.toGaussian fraction.numerator := by
  apply Basic.ext
  · simp only [-eq_self, -iff_self, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    change
      ((fraction.numerator.re : Fraction.Rational) /
          (fraction.denominator : Fraction.Rational)) *
            (fraction.denominator : Fraction.Rational) - _ * 0 =
        (fraction.numerator.re : Fraction.Rational)
    rw [Field.ExplicitField.div_mul_cancel _ fraction.denominatorCast_ne]
    ring1
  · simp only [-eq_self, -iff_self, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    change
      ((fraction.numerator.re : Fraction.Rational) / _ : Fraction.Rational) * 0 +
          ((fraction.numerator.im : Fraction.Rational) /
            (fraction.denominator : Fraction.Rational)) *
              (fraction.denominator : Fraction.Rational) =
        (fraction.numerator.im : Fraction.Rational)
    rw [Field.ExplicitField.div_mul_cancel _ fraction.denominatorCast_ne]
    ring1

/-- The fraction's squared norm is the natural numerator norm divided by its retained height. -/
theorem normSq_value (fraction :
  NaturalDenominator) :
    Norm.Basic.normSq fraction.value =
      (GaussianInt.normNat fraction.numerator : Fraction.Rational) /
        fraction.height := by
  simp only [value, height,
    Norm.Basic.normSq]
  rw [NatCast.pow]
  change
    ((fraction.numerator.re : Fraction.Rational) /
          (fraction.denominator : Fraction.Rational)) ^ 2 +
        ((fraction.numerator.im : Fraction.Rational) /
          (fraction.denominator : Fraction.Rational)) ^ 2 =
      (GaussianInt.normNat fraction.numerator : Fraction.Rational) /
        (fraction.denominator : Fraction.Rational) ^ 2
  have numeratorNorm := GaussianInt.normSq_toGaussian fraction.numerator
  simp only [-eq_self, -iff_self, Norm.Basic.normSq, GaussianInt.toGaussian,
    ← Rat.Fraction.Cast.intCast_eq_fromInt] at numeratorNorm
  change
    (fraction.numerator.re : Fraction.Rational) ^ 2 +
        (fraction.numerator.im : Fraction.Rational) ^ 2 =
      (GaussianInt.normNat fraction.numerator : Fraction.Rational) at numeratorNorm
  rw [Field.ExplicitField.div_eq_mul_inv,
    Field.ExplicitField.div_eq_mul_inv,
    Field.ExplicitField.div_eq_mul_inv, ← numeratorNorm]
  simp only [pow_two]
  rw [Fraction.Field.inv_mul_direct]
  generalize ((fraction.denominator : Fraction.Rational)⁻¹) = denominatorInverse
  ring1

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Construct a common positive natural denominator for the two reduced rational coordinates.

Read the exact reduced representatives of both rational coordinates, multiply their positive denominators and
cross-multiply their numerators. The resulting fraction keeps that product denominator without an additional
normalization step. -/
def ofGaussian (source : Basic.Canonical) :
  NaturalDenominator := by
  let real := Fraction.Basic.representative source.re
  let imaginary := Fraction.Basic.representative source.im
  let denominator := real.den * imaginary.den
  exact
    { numerator :=
        ⟨real.num * (imaginary.den : Int),
          imaginary.num * (real.den : Int)⟩
      denominator := denominator
      denominatorPositive := Nat.mul_pos real.den_pos imaginary.den_pos }

section
open Purelib.Data Purelib.Algebra

/-- The computed common-denominator presentation denotes its source exactly.

The retained coordinate numerators are scaled by the opposite denominators;
their shared denominator is the original product of those two denominators. -/
theorem ofGaussian_value (source :
  Basic.Canonical) :
    (ofGaussian source).value = source := by
  let real := Rat.Fraction.Basic.representative source.re
  let imaginary := Rat.Fraction.Basic.representative source.im
  have realClear := Rat.Fraction.Cast.representative_mul_den source.re
  have imaginaryClear :=
    Rat.Fraction.Cast.representative_mul_den source.im
  change source.re * (real.den : Rat.Fraction.Rational) = (real.num : Rat.Fraction.Rational) at realClear
  change source.im * (imaginary.den : Rat.Fraction.Rational) =
    (imaginary.num : Rat.Fraction.Rational) at imaginaryClear
  apply Gaussian.Basic.ext
  · change
      ((real.num * (imaginary.den : Int) : Int) : Rat.Fraction.Rational) /
          ((real.den * imaginary.den : Nat) : Rat.Fraction.Rational) = source.re
    rw [Ring.IntCast.intCast_mul, Int.cast_natCast, NatCast.mul]
    apply Rat.Fraction.Field.mul_right_cancel_of_ne
      (show ((real.den : Rat.Fraction.Rational) * (imaginary.den : Rat.Fraction.Rational)) ≠ 0 by
        exact Rat.Fraction.Field.mul_ne_zero_direct
          (fun zero => (Nat.ne_of_gt real.den_pos)
            (Rat.Fraction.Cast.Compatibility.natCast_injective_direct
              (zero.trans (Nat.cast_zero).symm)))
          (fun zero => (Nat.ne_of_gt imaginary.den_pos)
            (Rat.Fraction.Cast.Compatibility.natCast_injective_direct
              (zero.trans (Nat.cast_zero).symm))))
    rw [Field.ExplicitField.div_mul_cancel _
      (Rat.Fraction.Field.mul_ne_zero_direct
        (fun zero => (Nat.ne_of_gt real.den_pos)
          (Rat.Fraction.Cast.Compatibility.natCast_injective_direct
            (zero.trans (Nat.cast_zero).symm)))
        (fun zero => (Nat.ne_of_gt imaginary.den_pos)
          (Rat.Fraction.Cast.Compatibility.natCast_injective_direct
            (zero.trans (Nat.cast_zero).symm))))]
    rw [← realClear]
    ring1
  · change
      ((imaginary.num * (real.den : Int) : Int) : Rat.Fraction.Rational) /
          ((real.den * imaginary.den : Nat) : Rat.Fraction.Rational) = source.im
    rw [Ring.IntCast.intCast_mul, Int.cast_natCast, NatCast.mul]
    apply Rat.Fraction.Field.mul_right_cancel_of_ne
      (show ((real.den : Rat.Fraction.Rational) * (imaginary.den : Rat.Fraction.Rational)) ≠ 0 by
        exact Rat.Fraction.Field.mul_ne_zero_direct
          (fun zero => (Nat.ne_of_gt real.den_pos)
            (Rat.Fraction.Cast.Compatibility.natCast_injective_direct
              (zero.trans (Nat.cast_zero).symm)))
          (fun zero => (Nat.ne_of_gt imaginary.den_pos)
            (Rat.Fraction.Cast.Compatibility.natCast_injective_direct
              (zero.trans (Nat.cast_zero).symm))))
    rw [Field.ExplicitField.div_mul_cancel _
      (Rat.Fraction.Field.mul_ne_zero_direct
        (fun zero => (Nat.ne_of_gt real.den_pos)
          (Rat.Fraction.Cast.Compatibility.natCast_injective_direct
            (zero.trans (Nat.cast_zero).symm)))
        (fun zero => (Nat.ne_of_gt imaginary.den_pos)
          (Rat.Fraction.Cast.Compatibility.natCast_injective_direct
            (zero.trans (Nat.cast_zero).symm))))]
    rw [← imaginaryClear]
    ring1

end

/-- Construct a natural-denominator Gaussian fraction from explicit integer coordinates and a positive denominator. -/
def grid (real imaginary : Int) (denominator :
  Nat)
    (positive : 0 < denominator) : NaturalDenominator :=
  ⟨⟨real, imaginary⟩, denominator, positive⟩

open Purelib.Data.Gaussian in
/-- The height of an explicit Gaussian grid fraction is the denominator squared. -/
@[simp] theorem grid_height (real imaginary :
  Int) (denominator : Nat)
    (positive : 0 < denominator) :
    (grid real imaginary denominator positive).height = denominator ^ 2 :=
      rfl

open Purelib.Data in
open Purelib.Data.Gaussian in
/-- Embed the retained positive natural denominator into a Gaussian-integer displayed fraction. -/
def toDisplayed (fraction :
  NaturalDenominator) : GaussianInt.Fraction :=
  ⟨fraction.numerator, GaussianInt.ofNat fraction.denominator, by
    intro zero
    have realZero := congrArg GaussianInt.re zero
    exact (Nat.ne_of_gt fraction.denominatorPositive) (Int.ofNat.inj realZero)⟩

open Purelib.Data.Gaussian in
/-- The displayed-fraction conversion preserves the exact integer numerator. -/
@[simp] theorem toDisplayed_numerator (fraction
  : NaturalDenominator) :
    fraction.toDisplayed.numerator = fraction.numerator := rfl
open Purelib.Data
open Purelib.Data.Gaussian
/-- The displayed-fraction conversion uses the natural denominator's Gaussian-integer embedding. -/
@[simp] theorem toDisplayed_denominator
  (fraction : NaturalDenominator) :
    fraction.toDisplayed.denominator = GaussianInt.ofNat fraction.denominator := rfl

/-- The displayed-fraction conversion preserves the original natural-denominator height. -/
@[simp] theorem toDisplayed_height (fraction :
  NaturalDenominator) :
    fraction.toDisplayed.height = fraction.height := by
  change GaussianInt.normNat (GaussianInt.ofNat fraction.denominator) = fraction.denominator ^ 2
  exact GaussianInt.normNat_ofNat fraction.denominator

/-- The displayed-fraction conversion preserves the original Gaussian readback. -/
@[simp] theorem toDisplayed_value (fraction :
  NaturalDenominator) :
    fraction.toDisplayed.value = fraction.value := by
  apply Field.mul_right_cancel_of_ne fraction.toDisplayed.denominatorGaussianNonzero
  calc
    _ = GaussianInt.toGaussian fraction.numerator :=
      fraction.toDisplayed.value_mul_denominator
    _ = fraction.value * GaussianInt.toGaussian
        (GaussianInt.ofNat fraction.denominator) :=
      fraction.value_mul_denominator.symm

end NaturalDenominator

end Purelib.Data.Gaussian.Basic.Canonical.Fraction
end
