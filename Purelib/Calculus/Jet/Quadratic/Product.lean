module

public import Purelib.Calculus.Jet.Quadratic.Bounds
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Product Taylor certificates with explicit unit-disk factors

The original two certificates supply their retained base values, slopes,
outputs and remainder payments. Their original movement factors bound the
product rule's cross term. The constructed factor contains no division by
the displayed increment and remains uniform under fixed input budgets.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.Product

open Purelib.Calculus.Jet.Quadratic.Basic
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- The product-rule remainder pays both original base-weighted remainders and the movement cross term. -/
@[expose] def factor {increment : Canonical} (left right : Certificate increment) : Fraction.Rational :=
  4 * (Canonical.normSq right.base * left.factor + Canonical.normSq left.base * right.factor +
    left.sensitivity * right.sensitivity)

/-- The computed product-rule factor is nonnegative. -/
theorem factor_nonnegative {increment : Canonical} (left right : Certificate increment) :
    0 ≤ factor left right :=
  Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Arithmetic.add_le_add_direct
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_nonneg_direct (Canonical.normSq_nonneg _) left.factor_nonneg)
        (Arithmetic.mul_nonneg_direct (Canonical.normSq_nonneg _) right.factor_nonneg))
      (Arithmetic.mul_nonneg_direct left.sensitivity_nonneg right.sensitivity_nonneg))

/-- The actual product remainder retains both original remainders and the original displacement cross term. -/
@[expose] def remainder {increment : Canonical} (left right : Certificate increment) : Canonical :=
  left.remainder * right.base + left.base * right.remainder +
    (left.output - left.base) * (right.output - right.base)

/-- The retained product remainder is exactly the original product-rule expansion error. -/
theorem expansion {increment : Canonical} (left right : Certificate increment) :
    left.output * right.output - left.base * right.base -
      increment * (left.slope * right.base + left.base * right.slope) = remainder left right := by
  unfold remainder
  rewrite [← left.expansion, ← right.expansion]
  ring1

/-- The original movement and remainder certificates pay the explicit product remainder factor on the unit disk. -/
theorem remainder_le {increment : Canonical} (left right : Certificate increment)
    (unit : Norm.Basic.normSq increment ≤ 1) :
    Canonical.normSq (remainder left right) ≤ factor left right * Canonical.normSq increment ^ 2 := by
  let first := left.remainder * right.base
  let last := left.base * right.remainder
  let cross := (left.output - left.base) * (right.output - right.base)
  let remainder := first + last + cross
  let firstFactor := Norm.Basic.normSq right.base * left.factor
  let lastFactor := Norm.Basic.normSq left.base * right.factor
  let crossFactor := left.sensitivity * right.sensitivity
  have leftMovement : Norm.Basic.normSq (left.output - left.base) ≤
      left.sensitivity * Norm.Basic.normSq increment := by
    simpa only [Norm.Basic.normSq_eq_canonical] using
      left.movement_le (by simpa only [Norm.Basic.normSq_eq_canonical] using unit)
  have rightMovement : Norm.Basic.normSq (right.output - right.base) ≤
      right.sensitivity * Norm.Basic.normSq increment := by
    simpa only [Norm.Basic.normSq_eq_canonical] using
      right.movement_le (by simpa only [Norm.Basic.normSq_eq_canonical] using unit)
  have firstBound : Norm.Basic.normSq first ≤ firstFactor * Norm.Basic.normSq increment ^ 2 := by
    dsimp only [first, firstFactor]
    rewrite [Norm.Basic.normSq_mul]
    have paid : Norm.Basic.normSq left.remainder ≤ left.factor * Norm.Basic.normSq increment ^ 2 := by
      simpa only [Norm.Basic.normSq_eq_canonical] using left.remainder_le
    exact (Arithmetic.mul_le_mul_of_nonneg_right_direct paid (Norm.Basic.normSq_nonneg _)).trans_eq
      (by ring1)
  have lastBound : Norm.Basic.normSq last ≤ lastFactor * Norm.Basic.normSq increment ^ 2 := by
    dsimp only [last, lastFactor]
    rewrite [Norm.Basic.normSq_mul]
    have paid : Norm.Basic.normSq right.remainder ≤ right.factor * Norm.Basic.normSq increment ^ 2 := by
      simpa only [Norm.Basic.normSq_eq_canonical] using right.remainder_le
    exact (Arithmetic.mul_le_mul_of_nonneg_left_direct paid (Norm.Basic.normSq_nonneg _)).trans_eq
      (by ring1)
  have crossBound : Norm.Basic.normSq cross ≤ crossFactor * Norm.Basic.normSq increment ^ 2 := by
    dsimp only [cross, crossFactor]
    rewrite [Norm.Basic.normSq_mul]
    exact (Arithmetic.mul_le_mul_direct leftMovement rightMovement (Norm.Basic.normSq_nonneg _)
      ((Norm.Basic.normSq_nonneg _).trans leftMovement)).trans_eq (by ring1)
  have remainderBound : Norm.Basic.normSq remainder ≤
      2 * (2 * (firstFactor + lastFactor) + crossFactor) * Norm.Basic.normSq increment ^ 2 := by
    dsimp only [remainder]
    exact (Norm.Bounds.normSq_add_le_two _ _).trans
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct
          ((Norm.Bounds.normSq_add_le_two _ _).trans
            (Arithmetic.mul_le_mul_of_nonneg_left_direct
              (Arithmetic.add_le_add_direct firstBound lastBound) (by decide +kernel)))
          crossBound) (by decide +kernel)).trans_eq (by ring1))
  have factorBound : 2 * (2 * (firstFactor + lastFactor) + crossFactor) ≤ factor left right := by
    have crossNonnegative := Arithmetic.mul_nonneg_direct
      left.sensitivity_nonneg right.sensitivity_nonneg
    calc
      _ = 4 * (firstFactor + lastFactor) + 2 * crossFactor := by ring1
      _ ≤ 4 * (firstFactor + lastFactor) + 4 * crossFactor :=
        Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
          (Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel :
            (2 : Fraction.Rational) ≤ 4) crossNonnegative)
      _ = _ := by
        unfold factor
        simp only [← Norm.Basic.normSq_eq_canonical]
        dsimp only [firstFactor, lastFactor, crossFactor]
        ring1
  simp only [← Norm.Basic.normSq_eq_canonical]
  exact remainderBound.trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct factorBound
      (Arithmetic.pow_nonneg_direct (Norm.Basic.normSq_nonneg _) 2))

/-- Construct the actual product expansion with its explicit finite factor on the unit increment disk.

Both original inputs remain unchanged. The slope is their product rule, and
the remainder uses their actual retained remainders and output displacements.
The bound follows from their original movement and remainder certificates.
-/
@[expose] def certificate {increment : Canonical} (left right : Certificate increment)
    (unit : Norm.Basic.normSq increment ≤ 1) : Certificate increment :=
  { base := left.base * right.base
    output := left.output * right.output
    slope := left.slope * right.base + left.base * right.slope
    remainder := remainder left right
    expansion := expansion left right
    factor := factor left right
    factor_nonneg := factor_nonnegative left right
    remainder_le := remainder_le left right unit }

end Purelib.Calculus.Jet.Quadratic.Product
