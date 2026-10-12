module
import Purelib.Tactic.Ring

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Gaussian.Field
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
-- The exposed coordinate conversion retains the denominator-one cast owner.
public import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Int.Order
import Purelib.Algebra.Ring.Multiplication

/-!
# Exact Gaussian-integer coordinate embeddings

Integral coordinates embed directly as denominator-one exact rational coordinates.
The embedding preserves arithmetic, detects zero and reads natural norm as rational
quadrance. The same coordinate construction realizes the original integer lattice
carrier as Gaussian rationals.
-/

@[expose] public section
namespace Purelib.Data.GaussianInt

open Purelib
open Data Data.Gaussian Data.Gaussian.Basic Data.Rat Data.Rat.Fraction
open Data.Rat.Fraction.Cast
open Algebra.Ring

/-- The canonical exact rational coordinate carrier. -/
abbrev Coordinate := Rational
/-- The canonical Gaussian-rational carrier with exact rational coordinates. -/
abbrev Gaussian := Canonical

/-- Embed a Gaussian integer as two exact denominator-one rational coordinates.

The direct signed casts retain each integral coordinate without iterating rational
addition over its magnitude. -/
def toGaussian (z : GaussianInt) : Gaussian :=
  ⟨Fraction.Cast.fromInt z.re, Fraction.Cast.fromInt z.im⟩

/-- The Gaussian-integer embedding sends zero to rational Gaussian zero. -/
@[simp] theorem toGaussian_zero : toGaussian 0 = 0 := rfl
/-- The Gaussian-integer embedding sends one to rational Gaussian one. -/
@[simp] theorem toGaussian_one : toGaussian 1 = 1 := rfl

/-- Coordinate embedding preserves Gaussian integer addition. -/
@[simp] theorem toGaussian_add (z w : GaussianInt) :
    toGaussian (z + w) = toGaussian z + toGaussian w := by
  simp only [-eq_self, -iff_self, toGaussian, ← Fraction.Cast.intCast_eq_fromInt]
  apply Data.Gaussian.Basic.ext
  · change ((z.re + w.re : Int) : Coordinate) = (z.re : Coordinate) + (w.re : Coordinate)
    exact IntCast.add _ _
  · change ((z.im + w.im : Int) : Coordinate) = (z.im : Coordinate) + (w.im : Coordinate)
    exact IntCast.add _ _

/-- Coordinate embedding preserves Gaussian integer negation. -/
@[simp] theorem toGaussian_neg (z : GaussianInt) :
    toGaussian (-z) = -toGaussian z := by
  simp only [-eq_self, -iff_self, toGaussian, ← Fraction.Cast.intCast_eq_fromInt]
  apply Data.Gaussian.Basic.ext
  · change ((-z.re : Int) : Coordinate) = -(z.re : Coordinate)
    exact IntCast.neg _
  · change ((-z.im : Int) : Coordinate) = -(z.im : Coordinate)
    exact IntCast.neg _

/-- Coordinate embedding preserves Gaussian integer subtraction. -/
@[simp] theorem toGaussian_sub (z w : GaussianInt) :
    toGaussian (z - w) = toGaussian z - toGaussian w := by
  simp only [-eq_self, -iff_self, toGaussian, ← Fraction.Cast.intCast_eq_fromInt]
  apply Data.Gaussian.Basic.ext
  · change ((z.re - w.re : Int) : Coordinate) = (z.re : Coordinate) - (w.re : Coordinate)
    rw [Int.sub_eq_add_neg, IntCast.add]
    change (z.re : Coordinate) + ((Int.neg w.re : Int) : Coordinate) = _
    rw [IntCast.neg, Fraction.Arithmetic.sub_eq_add_neg_direct]
  · change ((z.im - w.im : Int) : Coordinate) = (z.im : Coordinate) - (w.im : Coordinate)
    rw [Int.sub_eq_add_neg, IntCast.add]
    change (z.im : Coordinate) + ((Int.neg w.im : Int) : Coordinate) = _
    rw [IntCast.neg, Fraction.Arithmetic.sub_eq_add_neg_direct]

/-- Coordinate embedding preserves Gaussian integer multiplication.

The real difference and imaginary sum use the original displayed integer
products and their direct ring-cast equations. -/
@[simp] theorem toGaussian_mul (z w : GaussianInt) :
    toGaussian (z * w) = toGaussian z * toGaussian w := by
  simp only [-eq_self, -iff_self, toGaussian, ← Fraction.Cast.intCast_eq_fromInt]
  apply Data.Gaussian.Basic.ext
  · change ((z.re * w.re - z.im * w.im : Int) : Coordinate) =
      (z.re : Coordinate) * (w.re : Coordinate) - (z.im : Coordinate) * (w.im : Coordinate)
    rw [Int.sub_eq_add_neg, IntCast.add]
    change ((z.re * w.re : Int) : Coordinate) +
      ((Int.neg (z.im * w.im) : Int) : Coordinate) = _
    rw [IntCast.neg, IntCast.intCast_mul,
      IntCast.intCast_mul, Fraction.Arithmetic.sub_eq_add_neg_direct]
  · change ((z.re * w.im + z.im * w.re : Int) : Coordinate) =
      (z.re : Coordinate) * (w.im : Coordinate) + (z.im : Coordinate) * (w.re : Coordinate)
    rw [IntCast.add, IntCast.intCast_mul, IntCast.intCast_mul]

/-- Coordinatewise embedding of Gaussian integers into Gaussian rationals is injective. -/
theorem toGaussian_injective : Function.Injective toGaussian := by
  intro z w equal
  simp only [-eq_self, -iff_self, toGaussian, ← Fraction.Cast.intCast_eq_fromInt] at equal
  apply GaussianInt.ext
  · exact Compatibility.intCast_injective_direct
      (congrArg Data.Gaussian.Basic.re equal)
  · exact Compatibility.intCast_injective_direct
      (congrArg Data.Gaussian.Basic.im equal)

/-- An embedded Gaussian integer is zero exactly when its original integral value is
zero. -/
theorem toGaussian_eq_zero {z : GaussianInt} :
    toGaussian z = 0 ↔ z = 0 := by
  constructor
  · intro zero
    exact toGaussian_injective (zero.trans toGaussian_zero.symm)
  · rintro rfl
    exact toGaussian_zero

/-- Coordinate embedding reads the natural integer norm as rational quadrance.

Nonnegativity retains the original integer norm under magnitude readback.
Direct integer-cast equations identify its two displayed coordinate squares. -/
theorem normSq_toGaussian (z : GaussianInt) :
    Gaussian.Norm.Basic.normSq (toGaussian z) =
      (GaussianInt.normNat z : Rational) := by
  simp only [-eq_self, -iff_self, toGaussian, ← Fraction.Cast.intCast_eq_fromInt]
  rw [← Int.cast_natCast]
  rw [GaussianInt.normNat, Int.Order.natAbs_of_nonneg (normInt_nonneg z)]
  change (z.re : Coordinate) ^ 2 + (z.im : Coordinate) ^ 2 =
    ((z.re * z.re + z.im * z.im : Int) : Coordinate)
  rw [pow_two, pow_two, IntCast.add, IntCast.intCast_mul, IntCast.intCast_mul]

/-- Embedding a natural Gaussian integer gives that natural as a real rational
coordinate. -/
@[simp] theorem toGaussian_ofNat (value : Nat) :
    toGaussian (ofNat value) = ⟨(value : Rational), 0⟩ := by
  simp only [-eq_self, -iff_self, toGaussian, ← Fraction.Cast.intCast_eq_fromInt]
  rfl

section Embedding

namespace Embedding

/-- The original Gaussian-integer carrier retained as an exact reducible alias. -/
abbrev Integer := Data.GaussianInt

/-- Gaussian integer norm is multiplicative. -/
theorem normNat_mul (left right : Data.GaussianInt) :
    Data.GaussianInt.normNat (left * right) = Data.GaussianInt.normNat left * Data.GaussianInt.normNat right :=
  Data.GaussianInt.normNat_mul left right

/-- Integral conjugation retains the natural Gaussian norm. -/
@[simp] theorem normNat_conjugate (value : Data.GaussianInt) :
    Data.GaussianInt.normNat (Data.GaussianInt.Norm.Basic.conjugate value) = Data.GaussianInt.normNat value := by
  apply Rat.Fraction.Cast.Compatibility.natCast_injective_direct
  rw [← Data.GaussianInt.normSq_toGaussian, ← Data.GaussianInt.normSq_toGaussian]
  simp only [-eq_self, -iff_self, Data.GaussianInt.toGaussian,
    ← Rat.Fraction.Cast.intCast_eq_fromInt]
  change (value.re : Rat.Fraction.Rational) ^ 2 +
      ((Int.neg value.im : Int) : Rat.Fraction.Rational) ^ 2 =
    (value.re : Rat.Fraction.Rational) ^ 2 + (value.im : Rat.Fraction.Rational) ^ 2
  apply congrArg ((value.re : Rat.Fraction.Rational) ^ 2 + ·)
  rw [IntCast.neg, pow_two, pow_two, Multiplication.neg_mul_neg]

end Embedding
section GaussianInt

/-- Embedding a Gaussian-integer power equals the same power of its embedded value. -/
@[simp] theorem toGaussian_pow (value : Data.GaussianInt) (exponent :
  Nat) :
    toGaussian
        (value ^ exponent) =
      toGaussian value ^ exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent inductionHypothesis =>
      rw [pow_succ, pow_succ,
        toGaussian_mul,
        inductionHypothesis]

end GaussianInt
end Embedding

namespace LatticePoint

open _root_.Purelib.Data.GaussianInt (LatticePoint)

/-- Realize an integer lattice point as the exact Gaussian rational with the same two
coordinates. -/
def gaussian (point : LatticePoint) : Canonical where
  re := (point.x : Rational)
  im := (point.y : Rational)

/-- The coordinatewise Gaussian-rational realization of integer lattice points is
injective. -/
theorem gaussian_injective : Function.Injective gaussian
  := by
  intro left right equal
  cases left with
  | mk leftX leftY =>
      cases right with
      | mk rightX rightY =>
          have xEqual : leftX = rightX := by
            apply Compatibility.intCast_injective_direct
            exact congrArg Data.Gaussian.Basic.re equal
          have yEqual : leftY = rightY := by
            apply Compatibility.intCast_injective_direct
            exact congrArg Data.Gaussian.Basic.im equal
          subst rightX
          subst rightY
          rfl

end LatticePoint
end Purelib.Data.GaussianInt
