module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Constructive finite variation bounds for powers and quotients

These core estimates use only displayed Gaussian rationals and finite induction on
the exponent.  They are the quantitative kernel for constant local models of
`x^k/y` on a prepared hyperelliptic continuation cell.
-/

namespace Purelib.Data.Gaussian.Power.Bounds.ApproximationQuotientVariation

open Purelib.Data.Rat in
/-- Compute the recursive squared-distance coefficient for a Gaussian natural power on a bounded disk.

Start at zero. At a successor exponent, double the sum of the preceding slope times the radius and the corresponding
radius power; the same recurrence controls squared displacement of natural powers. -/
def powerSlope (radiusSq : Fraction.Rational) :
  Nat -> Fraction.Rational
  | 0 => 0
  | exponent + 1 =>
      2 * (powerSlope radiusSq exponent * radiusSq +
        radiusSq ^ exponent)

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- A nonnegative disk norm bound makes every recursive power slope nonnegative. -/
theorem powerSlope_nonnegative {radiusSq :
  Fraction.Rational}
    (radiusNonnegative : 0 <= radiusSq) : forall exponent,
    0 <= powerSlope radiusSq exponent
  | 0 => le_rfl
  | exponent + 1 =>
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            (powerSlope_nonnegative radiusNonnegative
              exponent)
            radiusNonnegative)
          (Fraction.Order.Arithmetic.pow_nonneg_direct radiusNonnegative
            exponent))

/-- Endpoint squared norms bounded by a nonnegative radius give the retained power-slope bound on displacement of their
powers. -/
theorem normSq_pow_sub_pow_le {radiusSq :
  Fraction.Rational}
    (radiusNonnegative : 0 <= radiusSq) : forall (exponent : Nat)
    {left right : Basic.Canonical}, Data.Gaussian.Norm.Basic.normSq left <= radiusSq ->
    Data.Gaussian.Norm.Basic.normSq right <= radiusSq ->
    Data.Gaussian.Norm.Basic.normSq (left ^ exponent - right ^ exponent) <=
      powerSlope radiusSq exponent * Data.Gaussian.Norm.Basic.normSq (left -
        right)
  | 0, left, right, leftBound, rightBound => by
      rw [pow_zero, pow_zero, _root_.sub_self, Norm.Basic.normSq_zero]
      exact Fraction.Order.Arithmetic.mul_nonneg_direct
        (powerSlope_nonnegative radiusNonnegative 0)
        (Norm.Basic.normSq_nonneg (left - right))
  | exponent + 1, left, right, leftBound, rightBound => by
      have previous := normSq_pow_sub_pow_le
        radiusNonnegative exponent
        leftBound rightBound
      have rightPowerBound : Data.Gaussian.Norm.Basic.normSq (right ^ exponent) <=
          radiusSq ^ exponent := by
        rw [Power.normSq_pow]
        exact Fraction.Order.Arithmetic.pow_le_pow_direct
          (Norm.Basic.normSq_nonneg right) rightBound exponent
      have identity :
          left ^ (exponent + 1) - right ^ (exponent + 1) =
            (left ^ exponent - right ^ exponent) * left +
              right ^ exponent * (left - right) := by
        rw [pow_succ, pow_succ]
        apply Basic.ext <;>
          simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;>
          ring1
      rw [identity]
      calc
        Data.Gaussian.Norm.Basic.normSq ((left ^ exponent - right ^ exponent) * left +
            right ^ exponent * (left - right)) <=
            2 *
              (Data.Gaussian.Norm.Basic.normSq ((left ^ exponent - right ^ exponent) * left) +
                Data.Gaussian.Norm.Basic.normSq (right ^ exponent * (left - right))) :=
          Norm.Bounds.normSq_add_le_two _ _
        _ = 2 *
              (Data.Gaussian.Norm.Basic.normSq (left ^ exponent - right ^ exponent) * Data.Gaussian.Norm.Basic.normSq
                left +
                Data.Gaussian.Norm.Basic.normSq (right ^ exponent) * Data.Gaussian.Norm.Basic.normSq (left - right)) :=
                  by
          rw [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
        _ <= 2 *
              ((powerSlope radiusSq exponent *
                Data.Gaussian.Norm.Basic.normSq
                (left - right)) *
                  radiusSq +
                radiusSq ^ exponent * Data.Gaussian.Norm.Basic.normSq (left - right)) := by
          apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          · exact add_le_add
              (Fraction.Order.Arithmetic.mul_le_mul_direct previous leftBound
                (Norm.Basic.normSq_nonneg left)
                (Fraction.Order.Arithmetic.mul_nonneg_direct
                  (powerSlope_nonnegative radiusNonnegative exponent)
                  (Norm.Basic.normSq_nonneg (left - right))))
              (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
                rightPowerBound (Norm.Basic.normSq_nonneg (left - right)))
          · decide
        _ = powerSlope radiusSq (exponent + 1) *
          Data.Gaussian.Norm.Basic.normSq
          (left - right) := by
          simp only [powerSlope]
          ring1
end Purelib.Data.Gaussian.Power.Bounds.ApproximationQuotientVariation

end

@[expose] public section

/-!
# Riemann compatibility facade for finite quotient variation

The constructive Gaussian-rational estimates now live in the arithmetic core,
where progressive division can use them without importing the Riemann layer.
These declarations preserve the established Riemann names for downstream
modules without duplicating their proof bodies.
-/

namespace Purelib.Data.Gaussian.Power.Bounds.IntegrationQuotientVariation

open Purelib.Data.Rat in
/-- Compute the recursive squared-distance coefficient for a Gaussian natural power on a bounded disk.

Start at zero. At a successor exponent, double the sum of the preceding slope times the radius and the corresponding
radius power; the same recurrence controls squared displacement of natural powers. -/
abbrev powerSlope (radiusSq : Fraction.Rational)
  (exponent : Nat) : Fraction.Rational :=
  Purelib.Data.Gaussian.Power.Bounds.ApproximationQuotientVariation.powerSlope radiusSq exponent

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- A nonnegative disk norm bound makes every recursive power slope nonnegative. -/
theorem powerSlope_nonnegative {radiusSq :
  Fraction.Rational}
    (radiusNonnegative : 0 <= radiusSq) (exponent : Nat) :
    0 <= powerSlope radiusSq exponent :=
  Power.Bounds.ApproximationQuotientVariation.powerSlope_nonnegative
    radiusNonnegative exponent

/-- Endpoint squared norms bounded by a nonnegative radius give the retained power-slope bound on displacement of their
powers. -/
theorem normSq_pow_sub_pow_le {radiusSq :
  Fraction.Rational}
    (radiusNonnegative : 0 <= radiusSq) (exponent : Nat)
    {left right : Basic.Canonical} (leftBound : Data.Gaussian.Norm.Basic.normSq left <= radiusSq)
    (rightBound : Data.Gaussian.Norm.Basic.normSq right <= radiusSq) :
    Data.Gaussian.Norm.Basic.normSq (left ^ exponent - right ^ exponent) <=
      powerSlope radiusSq exponent * Data.Gaussian.Norm.Basic.normSq (left -
        right)
        :=
  Power.Bounds.ApproximationQuotientVariation.normSq_pow_sub_pow_le
    radiusNonnegative exponent leftBound rightBound
end Purelib.Data.Gaussian.Power.Bounds.IntegrationQuotientVariation

end
