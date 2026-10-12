module
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Algebra.NatCast

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.SignedFraction.Arithmetic
public import Purelib.Data.Rat.SignedFraction.Normalization
meta import Purelib.Elab.Deriving.Repr
import Purelib.Tactic.QuotientFreeOmega

import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.Data.GaussianInt

open Purelib.Algebra
open Purelib.Algebra.Field
open Purelib.Data
open Purelib.Data.Gaussian.Basic
open Purelib.Data.Gaussian.Norm
open Purelib.Data.Gaussian.Norm.Basic
open Purelib.Data.GaussianInt
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.SignedFraction
open Purelib.Data.Gaussian

set_option genInjectivity false in
/-- Retain an uncancelled Gaussian-integer numerator and a certified nonzero denominator.

The exact value uses their coordinatewise Gaussian-rational embeddings. Denominator
height is its natural squared norm; no reduction certificate is required. -/
structure Fraction where
  /-- The retained Gaussian-integer numerator. -/ numerator : GaussianInt
  /-- The retained Gaussian-integer denominator. -/ denominator : GaussianInt
  /-- The exact retained denominator is nonzero. -/ denominatorNonzero : denominator ≠ 0

constructive_injectivity Fraction

namespace Fraction

derive_exposed_repr Fraction

end Fraction
namespace Fraction

namespace Basic

/-- The displayed Gaussian-integer fraction with its certified nonzero denominator. -/
abbrev SourceEncodingEncoderFracAlias := Fraction

end Basic

/-- Compute the exact Gaussian-rational value from the retained integral numerator and
denominator. -/
@[expose] def value (fraction : Fraction) : Gaussian.Basic.Canonical :=
  GaussianInt.toGaussian fraction.numerator * (GaussianInt.toGaussian fraction.denominator)⁻¹

/-- The embedded denominator of a retained Gaussian fraction is nonzero. -/
theorem denominatorGaussianNonzero (fraction : Fraction) :
    GaussianInt.toGaussian fraction.denominator ≠ 0 := by
  intro zero
  exact fraction.denominatorNonzero (toGaussian_eq_zero.mp zero)

/-- Compute the natural quadrance of the displayed, potentially unreduced Gaussian
denominator. -/
@[expose] def height (fraction : Fraction) : Nat :=
  GaussianInt.normNat fraction.denominator

/-- Multiplying a rational by its computed representative denominator recovers the cast
representative numerator. -/
private theorem representative_mul_den (value : Rational) :
    value * ((Basic.representative value).den :
      Rational) =
      ((Basic.representative value).num : Rational) := by
  let representative := Basic.representative value
  calc
    value * (representative.den : Rational) =
        Normalization.ofFraction (Normalization.toFraction representative) *
          (representative.den : Rational) := by
      exact congrArg (fun coordinate =>
        coordinate * (representative.den : Rational))
          (Normalization.representative_spec value).symm
    _ = (representative.num : Rational) := by
      simpa only [representative,
        Normalization.toFraction,
        Int.cast_natCast] using
        Arithmetic.ofFraction_mul_den
          (Normalization.toFraction representative)

/-- Multiplying the exact fraction value by its embedded denominator recovers its
embedded numerator. -/
theorem value_mul_denominator (fraction : Fraction) :
    fraction.value * GaussianInt.toGaussian fraction.denominator =
      GaussianInt.toGaussian fraction.numerator := by
  dsimp only [value]
  rw [Gaussian.Basic.mul_assoc,
    Gaussian.Field.inv_eq,
    Gaussian.Field.inv_mul _
      fraction.denominatorGaussianNonzero,
    _root_.mul_one]

/-- The squared norm of an exact Gaussian fraction is the quotient of its retained
integral quadrances. -/
theorem normSq_value (fraction : Fraction) :
    Gaussian.Norm.Basic.normSq fraction.value =
      (GaussianInt.normNat fraction.numerator : Rational) /
        GaussianInt.normNat fraction.denominator := by
  rw [value, Basic.normSq_mul, Gaussian.Field.inv_eq, Gaussian.Field.normSq_inv _ fraction.denominatorGaussianNonzero,
    GaussianInt.normSq_toGaussian, GaussianInt.normSq_toGaussian]
  exact (ExplicitField.div_eq_mul_inv _ _).symm

/-- Identify a Gaussian fraction's exact value from a displayed cross-multiplication
equality.

The stored nonzero denominator permits cancellation, so the proposed value is
certified without replacing the original presentation. -/
theorem value_eq_of_mul_den (fraction : Fraction) (candidate : Gaussian.Basic.Canonical)
    (identity : candidate * GaussianInt.toGaussian fraction.denominator =
      GaussianInt.toGaussian fraction.numerator) :
    fraction.value = candidate := by
  apply Gaussian.Field.mul_right_cancel_of_ne
    fraction.denominatorGaussianNonzero
  rw [fraction.value_mul_denominator]
  exact identity.symm

/-- Compute an uncancelled Gaussian-integer fraction for an exact Gaussian rational.

Use the two computed canonical coordinate representatives, multiply their positive
denominators and cross-scale their integral numerators. The result retains the exact
nonzero denominator evidence. -/
@[expose] def ofGaussian (value : Gaussian.Basic.Canonical) : Fraction := by
  let real := Basic.representative value.re
  let imaginary := Basic.representative value.im
  let denominatorNat := real.den * imaginary.den
  have denominatorNatPositive : 0 < denominatorNat :=
    Nat.mul_pos real.den_pos imaginary.den_pos
  let numerator : GaussianInt :=
    ⟨real.num * (imaginary.den : Int),
      imaginary.num * (real.den : Int)⟩
  let denominator : GaussianInt := ⟨(denominatorNat : Int), 0⟩
  have denominatorNonzero : denominator ≠ 0 := by
    intro zero
    have realZero := congrArg GaussianInt.re zero
    dsimp only [denominator] at realZero
    simp only [GaussianInt.zero_re] at realZero
    have denominatorNatZero : denominatorNat = 0 := Int.ofNat.inj realZero
    exact (Nat.ne_of_gt denominatorNatPositive) denominatorNatZero
  exact ⟨numerator, denominator, denominatorNonzero⟩

/-- The computed integral fraction represents its supplied Gaussian-rational value
exactly. -/
theorem ofGaussian_value (source : Gaussian.Basic.Canonical) :
    (ofGaussian source).value = source := by
  let real := Basic.representative source.re
  let imaginary := Basic.representative source.im
  let denominatorNat := real.den * imaginary.den
  have denominatorNonzero : GaussianInt.toGaussian (ofGaussian source).denominator ≠ 0 :=
    (ofGaussian source).denominatorGaussianNonzero
  apply Gaussian.Field.mul_right_cancel_of_ne
    denominatorNonzero
  rw [(ofGaussian source).value_mul_denominator]
  apply Gaussian.Basic.ext
  · simp only [-eq_self, -iff_self, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    change
      ((real.num * (imaginary.den : Int) : Int) : Rational) =
        source.re * (denominatorNat : Rational) - source.im * 0
    dsimp only [denominatorNat]
    rw [Ring.IntCast.intCast_mul, Int.cast_natCast, NatCast.mul]
    calc
      ((real.num : Int) : Rational) * (imaginary.den : Rational) =
          (source.re * (real.den : Rational)) *
            (imaginary.den : Rational) := by
        rw [representative_mul_den source.re]
      _ = source.re *
          ((real.den : Rational) * (imaginary.den : Rational)) := by
        ring1
      _ = source.re *
          ((real.den : Rational) * (imaginary.den : Rational)) -
            source.im * 0 := by ring1
  · simp only [-eq_self, -iff_self, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    change
      ((imaginary.num * (real.den : Int) : Int) : Rational) =
        source.re * 0 + source.im * (denominatorNat : Rational)
    dsimp only [denominatorNat]
    rw [Ring.IntCast.intCast_mul, Int.cast_natCast, NatCast.mul]
    calc
      ((imaginary.num : Int) : Rational) * (real.den : Rational) =
          (source.im * (imaginary.den : Rational)) *
            (real.den : Rational) := by
        rw [representative_mul_den source.im]
      _ = source.im *
          ((real.den : Rational) * (imaginary.den : Rational)) := by
        ring1
      _ = source.re * 0 + source.im *
          ((real.den : Rational) * (imaginary.den : Rational)) := by
        ring1

/-- A nonzero Gaussian-rational input gives a nonzero numerator in its computed integral
fraction. -/
theorem ofGaussian_numerator_ne_zero {source : Gaussian.Basic.Canonical} (nonzero : source ≠ 0) :
    (ofGaussian source).numerator ≠ 0 := by
  intro numeratorZero
  have valueZero : (ofGaussian source).value = 0 := by
    rw [value, numeratorZero, toGaussian_zero,
      Gaussian.Basic.zero_mul]
  exact nonzero ((ofGaussian_value source).symm.trans valueZero)

/-- A retained fraction with nonzero numerator has nonzero exact Gaussian value. -/
theorem value_ne_zero (fraction : Fraction)
    (numeratorNonzero : fraction.numerator ≠ 0) : fraction.value ≠ 0 := by
  intro valueZero
  have productZero := congrArg
    (fun value => value * GaussianInt.toGaussian fraction.denominator) valueZero
  rw [fraction.value_mul_denominator,
    Gaussian.Basic.zero_mul] at productZero
  exact numeratorNonzero (toGaussian_eq_zero.mp productZero)

namespace Basic

/-- The canonical Gaussian-rational carrier with exact rational coordinates. -/
abbrev Gaussian := Canonical

-- This retained public carrier alias intentionally includes its owner name.
/-- The Gaussian-integer carrier as an exact reducible fraction-coordinate
alias. -/
abbrev Integer := GaussianInt

/-- Equal exact Gaussian fraction values have equal retained integral cross-products.

Multiply each retained value by its nonzero displayed denominator, then
transport the same scalar identity through the injective integral embedding. -/
theorem crossProduct_of_value_eq
    (left right : Fraction) (valueEqual : left.value = right.value) :
    left.numerator * right.denominator =
      right.numerator * left.denominator := by
  apply GaussianInt.toGaussian_injective
  rw [GaussianInt.toGaussian_mul, GaussianInt.toGaussian_mul]
  calc
    GaussianInt.toGaussian left.numerator * GaussianInt.toGaussian right.denominator =
        (left.value * GaussianInt.toGaussian left.denominator) *
          GaussianInt.toGaussian right.denominator := by
      rw [left.value_mul_denominator]
    _ = left.value *
          (GaussianInt.toGaussian left.denominator * GaussianInt.toGaussian right.denominator)
            := by
      rw [Purelib.Data.Gaussian.Basic.mul_assoc]
    _ = right.value *
          (GaussianInt.toGaussian left.denominator * GaussianInt.toGaussian right.denominator)
            := by
      rw [valueEqual]
    _ = (right.value * GaussianInt.toGaussian right.denominator) *
          GaussianInt.toGaussian left.denominator := by
      apply Purelib.Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.mul_re,
          Purelib.Data.Gaussian.Basic.mul_im] <;>
        ring1
    _ = GaussianInt.toGaussian right.numerator * GaussianInt.toGaussian left.denominator := by
      rw [right.value_mul_denominator]

/-- Equal integral cross-products certify equal exact Gaussian fraction values.

Both original denominators remain nonzero; cancelling their embedded product
identifies the two retained presentations. -/
theorem value_eq_of_crossProduct
    (left right : Fraction)
    (crossProduct :
      left.numerator * right.denominator =
        right.numerator * left.denominator) :
    left.value = right.value := by
  have denominatorProductNonzero :
      GaussianInt.toGaussian left.denominator * GaussianInt.toGaussian right.denominator ≠ 0
        :=
    Purelib.Data.Gaussian.Field.mul_ne_zero_direct
      left.denominatorGaussianNonzero right.denominatorGaussianNonzero
  apply Purelib.Data.Gaussian.Field.mul_right_cancel_of_ne
    denominatorProductNonzero
  calc
    left.value *
          (GaussianInt.toGaussian left.denominator * GaussianInt.toGaussian right.denominator)
            =
        (left.value * GaussianInt.toGaussian left.denominator) *
          GaussianInt.toGaussian right.denominator := by
      rw [Purelib.Data.Gaussian.Basic.mul_assoc]
    _ = GaussianInt.toGaussian left.numerator * GaussianInt.toGaussian right.denominator := by
      rw [left.value_mul_denominator]
    _ = GaussianInt.toGaussian (left.numerator * right.denominator) := by
      rw [GaussianInt.toGaussian_mul]
    _ = GaussianInt.toGaussian (right.numerator * left.denominator) := by
      rw [crossProduct]
    _ = GaussianInt.toGaussian right.numerator * GaussianInt.toGaussian left.denominator := by
      rw [GaussianInt.toGaussian_mul]
    _ = (right.value * GaussianInt.toGaussian right.denominator) *
          GaussianInt.toGaussian left.denominator := by
      rw [right.value_mul_denominator]
    _ = right.value *
          (GaussianInt.toGaussian left.denominator * GaussianInt.toGaussian right.denominator)
            := by
      apply Purelib.Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.mul_re,
          Purelib.Data.Gaussian.Basic.mul_im] <;>
        ring1

/-- The displayed Gaussian-integer fraction with its retained numerator and
denominator. -/
abbrev SourceEncodingPrefixTowerFracAlias := Fraction

end Basic

end Fraction

end Purelib.Data.GaussianInt
