module
import Purelib.Data.Nat.Subtraction
import Purelib.Algebra.Semiring.Normalization
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Dyadic
public import Purelib.Data.Rat.Dyadic.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Finite dyadic range reduction for the progressive logarithm

A logarithm needs branch information.  This module records that information
as one finite dyadic chart: a natural exponent, a scaling direction, and a
proof that every candidate at the displayed input state is carried into the
overlapping real interval `[1/2,2]`.

The output is the local finite logarithm of the scaled input plus or minus an
explicit natural multiple of the independently generated finite `log 2`
samples.  No completed logarithm, limiting value, or infinite functional
equation appears in the construction.
-/

namespace Purelib.Data.Gaussian.Dyadic

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Embed the retained directed rational dyadic scalar into the Gaussian real axis. -/
@[expose] def dyadicFactor : Dyadic.Basic.Direction → Nat → Basic.Canonical
  | direction, exponent => ⟨Dyadic.Basic.dyadicScalar direction exponent, 0⟩

/-- The real coordinate of multiplication by a dyadic factor is the real coordinate scaled by its rational dyadic
scalar. -/
theorem dyadicFactor_mul_re (direction : Dyadic.Basic.Direction) (exponent : Nat)
    (value : Basic.Canonical) :
    (dyadicFactor direction exponent * value).re =
      Dyadic.Basic.dyadicScalar direction exponent * value.re := by
  simp only [dyadicFactor, Basic.mul_re]
  ring1

/-- Multiplication of a real Gaussian by a dyadic factor still has zero imaginary coordinate. -/
theorem dyadicFactor_mul_im_of_real (direction : Dyadic.Basic.Direction) (exponent : Nat)
    {value : Basic.Canonical} (real : value.im = 0) :
    (dyadicFactor direction exponent * value).im = 0 := by
  simp only [dyadicFactor, Basic.mul_im, real]
  ring1
end Purelib.Data.Gaussian.Dyadic

end

public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

namespace Purelib.Data.Gaussian.Dyadic

section
open Purelib.Data.Gaussian
/-- The canonical Gaussian with real coordinate one half and imaginary coordinate zero. -/
@[expose] def dyadicHalf : Basic.Canonical := ⟨1 / 2, 0⟩

/-- Apply the real Gaussian half-factor the supplied number of times.

The zero depth returns the original Gaussian. Each successor left-multiplies the preceding value by the retained real
half-factor, preserving the exact recursive computation. -/
@[expose] def dyadicScale : Nat → Basic.Canonical → Basic.Canonical
  | 0, value => value
  | exponent + 1, value => dyadicHalf * dyadicScale exponent value

end

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Recursive dyadic scaling equals multiplication by the real inverse power of two. -/
theorem dyadicScale_eq_inversePower (exponent : Nat) (value : Basic.Canonical) :
    dyadicScale exponent value =
      (⟨1 / (2 : Fraction.Rational) ^ exponent, 0⟩ : Basic.Canonical) * value := by
  induction exponent with
  | zero =>
      change value = (⟨1 / (1 : Fraction.Rational), 0⟩ : Basic.Canonical) * value
      have oneDivOne : (1 / (1 : Fraction.Rational)) = 1 := by
        have canceled :
            ((1 : Fraction.Rational) / (1 : Fraction.Rational)) * (1 : Fraction.Rational) = 1 :=
          Fraction.Field.div_mul_cancel_of_ne
            (1 : Fraction.Rational) (1 : Fraction.Rational) (by decide)
        calc
          (1 : Fraction.Rational) / 1 = (1 / 1) * 1 :=
            (Fraction.Field.mul_one_direct _).symm
          _ = 1 := canceled
      rw [oneDivOne]
      exact (Basic.one_mul value).symm
  | succ exponent inductionHypothesis =>
      rw [dyadicScale, inductionHypothesis]
      have scaleProduct :
          dyadicHalf * (⟨1 / (2 : Fraction.Rational) ^ exponent, 0⟩ : Basic.Canonical) =
            (⟨1 / (2 : Fraction.Rational) ^ (exponent + 1), 0⟩ : Basic.Canonical) := by
        apply Basic.ext
        · change (1 / 2 : Fraction.Rational) * (1 / 2 ^ exponent) - 0 * 0 =
            1 / 2 ^ (exponent + 1)
          rw [Fraction.Field.mul_zero_direct,
            Dyadic.half_mul_inversePower]
          ring1
        · change (1 / 2 : Fraction.Rational) * 0 + 0 * (1 / 2 ^ exponent) = 0
          ring1
      calc
        dyadicHalf *
            ((⟨1 / (2 : Fraction.Rational) ^ exponent, 0⟩ : Basic.Canonical) * value) =
          (dyadicHalf *
            (⟨1 / (2 : Fraction.Rational) ^ exponent, 0⟩ : Basic.Canonical)) * value :=
          (Basic.mul_assoc _ _ _).symm
        _ = (⟨1 / (2 : Fraction.Rational) ^ (exponent + 1), 0⟩ : Basic.Canonical) *
            value := by rw [scaleProduct]

/-- The squared norm of the real half-factor is one quarter. -/
@[simp] theorem normSq_dyadicHalf : Norm.Basic.normSq dyadicHalf = 1 / 4 := by
  change (1 / 2 : Fraction.Rational) ^ 2 + 0 ^ 2 = 1 / 4
  rw [pow_two, show (0 : Fraction.Rational) ^ 2 = 0 by decide,
    _root_.add_comm _ 0,
    Fraction.Field.zero_add]
  calc
    (1 / 2 : Fraction.Rational) * (1 / 2) = (1 * 1) / (2 * 2) :=
      Fraction.Field.div_mul_div_direct _ _ _ _
    _ = 1 / 4 := rfl

/-- Adding two copies of the next dyadic scaling recovers the preceding scaling. -/
@[simp] theorem dyadicScale_succ_add_self (exponent : Nat)
    (value : Basic.Canonical) :
    dyadicScale (exponent + 1) value + dyadicScale (exponent + 1) value =
      dyadicScale exponent value := by
  change dyadicHalf * dyadicScale exponent value +
      dyadicHalf * dyadicScale exponent value = dyadicScale exponent value
  have halfDouble : (1 / 2 : Fraction.Rational) * 2 = 1 :=
    Fraction.Field.div_mul_cancel_of_ne 1 2 (by decide)
  apply Basic.ext
  · simp only [dyadicHalf, Basic.mul_re, Basic.add_re]
    calc
      (1 / 2 * (dyadicScale exponent value).re -
            0 * (dyadicScale exponent value).im) +
          (1 / 2 * (dyadicScale exponent value).re -
            0 * (dyadicScale exponent value).im) =
        ((1 / 2 : Fraction.Rational) * 2) *
          (dyadicScale exponent value).re := by ring1
      _ = (dyadicScale exponent value).re := by
        rw [halfDouble, Fraction.Field.one_mul]
  · simp only [dyadicHalf, Basic.mul_im, Basic.add_im]
    calc
      (1 / 2 * (dyadicScale exponent value).im +
            0 * (dyadicScale exponent value).re) +
          (1 / 2 * (dyadicScale exponent value).im +
            0 * (dyadicScale exponent value).re) =
        ((1 / 2 : Fraction.Rational) * 2) *
          (dyadicScale exponent value).im := by ring1
      _ = (dyadicScale exponent value).im := by
        rw [halfDouble, Fraction.Field.one_mul]

/-- Embed one divided by the supplied natural power of two into the Gaussian real axis. -/
@[expose] def inverseDyadicAt (exponent : Nat) : Basic.Canonical :=
  ⟨1 / (2 : Fraction.Rational) ^ exponent, 0⟩

end

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The inverse dyadic Gaussian has the exact retained quarter-geometric squared norm. -/
@[simp] theorem normSq_inverseDyadicAt (exponent : Nat) :
    Norm.Basic.normSq (inverseDyadicAt exponent) =
      Geometric.Basic.quarterRadius 1 exponent := by
  change (1 / (2 : Fraction.Rational) ^ exponent) ^ 2 + 0 ^ 2 =
    1 / (4 : Fraction.Rational) ^ exponent
  rw [show (0 : Fraction.Rational) ^ 2 = 0 by decide,
    _root_.add_comm _ 0,
    Fraction.Field.zero_add, pow_two]
  calc
    (1 / (2 : Fraction.Rational) ^ exponent) * (1 / (2 : Fraction.Rational) ^ exponent) =
        (1 * 1) / ((2 : Fraction.Rational) ^ exponent * 2 ^ exponent) :=
      Fraction.Field.div_mul_div_direct _ _ _ _
    _ = 1 / (4 : Fraction.Rational) ^ exponent := by
      rw [Fraction.Field.one_mul, ← Purelib.Algebra.Semiring.Normalization.product_pow]
      rw [show (2 : Fraction.Rational) * 2 = 4 by decide]

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
/-- Every inverse dyadic Gaussian has squared norm at most one. -/
theorem normSq_inverseDyadicAt_le_one (exponent : Nat) :
    Norm.Basic.normSq (inverseDyadicAt exponent) ≤ 1 := by
  rw [normSq_inverseDyadicAt]
  exact Geometric.Basic.quarterRadius_le_scale
    (by decide) exponent

open Purelib.Data.Gaussian in
/-- The inverse dyadic Gaussian at exponent zero is one. -/
@[simp] theorem inverseDyadicAt_zero : inverseDyadicAt 0 = 1 := by
  decide

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The next inverse dyadic Gaussian is the real half-factor times the current one. -/
theorem inverseDyadicAt_succ (exponent : Nat) :
    dyadicHalf * inverseDyadicAt exponent =
      inverseDyadicAt (exponent + 1) := by
  apply Basic.ext
  · change (1 / 2 : Fraction.Rational) * (1 / 2 ^ exponent) - 0 * 0 =
      1 / 2 ^ (exponent + 1)
    rw [Fraction.Field.mul_zero_direct,
      Dyadic.half_mul_inversePower]
    ring1
  · change (1 / 2 : Fraction.Rational) * 0 + 0 * (1 / 2 ^ exponent) = 0
    ring1

open Purelib.Data.Gaussian in
/-- Multiplying inverse dyadic Gaussians adds their natural exponents. -/
theorem inverseDyadicAt_mul (base extra : Nat) :
    inverseDyadicAt extra * inverseDyadicAt base =
      inverseDyadicAt (base + extra) := by
  induction extra with
  | zero =>
      rw [inverseDyadicAt_zero,
        Basic.one_mul, Nat.add_zero]
  | succ extra inductionHypothesis =>
      calc
        inverseDyadicAt (extra + 1) * inverseDyadicAt base =
            (dyadicHalf * inverseDyadicAt extra) * inverseDyadicAt base := by
          rw [inverseDyadicAt_succ]
        _ = dyadicHalf *
              (inverseDyadicAt extra * inverseDyadicAt base) :=
          Basic.mul_assoc _ _ _
        _ = dyadicHalf * inverseDyadicAt (base + extra) := by
          rw [inductionHypothesis]
        _ = inverseDyadicAt ((base + extra) + 1) :=
          inverseDyadicAt_succ (base + extra)
        _ = inverseDyadicAt (base + (extra + 1)) :=
          congrArg inverseDyadicAt (Nat.add_succ base extra).symm

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A dyadic scaling with squared norm at most one stays within that bound after another halving. -/
theorem dyadicScale_unit_succ {exponent : Nat} {value : Basic.Canonical}
    (unit : Norm.Basic.normSq (dyadicScale exponent value) ≤ 1) :
    Norm.Basic.normSq (dyadicScale (exponent + 1) value) ≤ 1 := by
  rw [dyadicScale, Norm.Basic.normSq_mul, normSq_dyadicHalf]
  calc
    (1 / 4 : Fraction.Rational) * Norm.Basic.normSq (dyadicScale exponent value) ≤
        (1 / 4 : Fraction.Rational) * 1 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct unit (by decide)
    _ ≤ 1 := by decide

open Purelib.Data.Gaussian
/-- A dyadic scaling within the unit norm bound stays within it after any additional number of halvings. -/
theorem dyadicScale_unit_add (base extra : Nat) (value : Basic.Canonical)
    (unit : Norm.Basic.normSq (dyadicScale base value) ≤ 1) :
    Norm.Basic.normSq (dyadicScale (base + extra) value) ≤ 1 := by
  induction extra with
  | zero => exact unit
  | succ extra inductionHypothesis =>
      rw [Nat.add_succ]
      exact dyadicScale_unit_succ inductionHypothesis

/-- Recursive dyadic scaling preserves Gaussian addition. -/
@[simp] theorem dyadicScale_add (exponent : Nat) (left right : Basic.Canonical) :
    dyadicScale exponent (left + right) =
      dyadicScale exponent left + dyadicScale exponent right := by
  induction exponent with
  | zero => rfl
  | succ exponent inductionHypothesis =>
      rw [dyadicScale, dyadicScale, dyadicScale, inductionHypothesis]
      exact Basic.left_distrib _ _ _

/-- Increasing a dyadic scaling depth preserves a squared-norm bound of one. -/
theorem dyadicScale_unit_of_le {lower upper : Nat} (value : Basic.Canonical)
    (order : lower ≤ upper)
    (unit : Norm.Basic.normSq (dyadicScale lower value) ≤ 1) :
    Norm.Basic.normSq (dyadicScale upper value) ≤ 1 := by
  have reconstructed : lower + (upper - lower) = upper :=
    Purelib.Data.Nat.Subtraction.add_sub_of_le order
  rw [← reconstructed]
  exact dyadicScale_unit_add lower (upper - lower) value unit
end Purelib.Data.Gaussian.Dyadic

end
