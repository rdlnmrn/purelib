module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Residual
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Geometry.Projective.Chordal.DyadicTail

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Finite residual-small-or-apart decisions

After a redundant sector is emitted, an arithmetic result may equal the
sector representative without that equality being decidable from opaque
input names.  The controller therefore never asks for equality.  At a fixed
positive residual threshold, a sufficiently fine rational ball either proves
that every realization is small enough to justify unary padding, or supplies
a positive norm lower bound making affine inversion sound.
-/

namespace Purelib.Data.CCL.Encoding.Padding.Residual

/-! ## Converting a small residual into finite unary padding -/

open Purelib.Data.Rat in
/-- The residual squared-norm target one divided by two to the successor padding count. -/
def paddingTarget (count : Nat) : Fraction.Rational :=
  1 / (2 : Fraction.Rational) ^ (count + 1)

open Purelib.Data in
open Purelib.Data.Rat in
/-- Every finite padding target is strictly positive. -/
theorem paddingTarget_pos (count : Nat) : 0 <
  paddingTarget count :=
  Fraction.Order.Field.div_pos_direct (by decide)
    (Fraction.Order.Arithmetic.pow_pos_direct (by decide) (count + 1))

open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A nonzero residual below the retained padding target has inverse gamma-scaled squared norm above two to that count.

The strict estimate uses the same residual and count through multiplication by gamma and inversion, retaining the
nonzero witness needed for the inverse norm formula. -/
theorem inverseTail_large {count : Nat} {residual : Basic.Canonical}
    (residualNonzero : residual ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq residual < paddingTarget count) :
    (2 : Fraction.Rational) ^ count < Data.Gaussian.Norm.Basic.normSq ((Basic.Canonical.gamma * residual)⁻¹) := by
  have productNonzero : Basic.Canonical.gamma * residual ≠ 0 :=
    Field.mul_ne_zero_direct (by decide) residualNonzero
  have productNormPositive := Norm.Basic.normSq_pos productNonzero
  have powerPositive : 0 < (2 : Fraction.Rational) ^ (count + 1) :=
    Fraction.Order.Arithmetic.pow_pos_direct (by decide) (count + 1)
  have residualProduct :
      Data.Gaussian.Norm.Basic.normSq residual * (2 : Fraction.Rational) ^ (count + 1) < 1 := by
    exact (Fraction.Order.Field.lt_div_iff_pos powerPositive).1 small
  have targetProduct :
      (2 : Fraction.Rational) ^ count * Data.Gaussian.Norm.Basic.normSq (Basic.Canonical.gamma * residual) < 1 := by
    rw [Norm.Basic.normSq_mul, Constants.normSq_gamma]
    calc
      (2 : Fraction.Rational) ^ count * (2 * Data.Gaussian.Norm.Basic.normSq residual) =
          Data.Gaussian.Norm.Basic.normSq residual * (2 : Fraction.Rational) ^ (count + 1) := by
        rw [pow_succ]
        ring1
      _ < 1 := residualProduct
  rw [Field.inv_eq, Field.normSq_inv _ productNonzero]
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := Data.Gaussian.Norm.Basic.normSq (Basic.Canonical.gamma * residual)) _ productNormPositive
  calc
    (2 : Fraction.Rational) ^ count * Data.Gaussian.Norm.Basic.normSq (Basic.Canonical.gamma * residual) < 1 :=
      targetProduct
    _ = (Data.Gaussian.Norm.Basic.normSq (Basic.Canonical.gamma * residual))⁻¹ *
          Data.Gaussian.Norm.Basic.normSq (Basic.Canonical.gamma * residual) :=
      (Fraction.Field.inv_mul_cancel _
        productNormPositive.ne').symm

open Purelib in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- Construct a dyadic loop tail from a residual in the retained small ball.

A zero residual returns infinity. A nonzero residual returns its exact reciprocal gamma-scaled affine tail with the
strict squared-norm bound for the supplied padding count. -/
def loopTailOfSmall {count : Nat} {ball :
  Approximation.Gaussian.Enclosure.Ball}
    (small : Approximation.Gaussian.Enclosure.Residual.SmallBall ball (paddingTarget
      count))
    (residual : Basic.Canonical) (inside : ball.Contains residual) :
    Chordal.DyadicTail.LoopTail count := by
  by_cases zero : residual = 0
  · exact .omega
  · exact .affine ((Basic.Canonical.gamma * residual)⁻¹)
      (inverseTail_large zero
        (Approximation.Gaussian.Enclosure.Residual.normSq_lt_of_contains small inside))

end Purelib.Data.CCL.Encoding.Padding.Residual

end
