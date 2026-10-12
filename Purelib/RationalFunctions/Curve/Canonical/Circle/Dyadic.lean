module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RationalFunctions.Curve.Canonical.Circle.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

section
@[expose] public section

/-!
# Canonical rational line and circle parameterizations

The CCL branch boundaries originate as coordinate lines or centered norm
circles before finite homographic pullback.  These explicit parameterizations
retain that provenance, including a proof that their parameter denominator
never vanishes.  Homographic transformation can subsequently move them into
the original polynomial coordinate.
-/

namespace Purelib.RationalFunctions.Curve.Canonical.Circle

section
open Purelib.Data
open Purelib.RationalFunctions
/-- Construct the centered circle with base given by the indicated power of one plus i.

The primary stereographic chart is used, and the resulting squared radius is two raised to the natural exponent. -/
def dyadicCircle (exponent : Nat) : Curve.RationalCurve :=
  Curve.Canonical.Circle.circle (Gaussian.Power.natPow Canonical.gamma exponent)

/-- Every point of the dyadic circle has quadrance two raised to its exponent. -/
theorem normSq_dyadicCircle_point (exponent : Nat) (parameter :
  Rational) :
    Gaussian.Norm.Basic.normSq ((dyadicCircle exponent).point parameter) =
      (2 : Rational) ^ exponent := by
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  rw [dyadicCircle, Curve.Canonical.Circle.normSq_circle_point, ←
    Gaussian.Norm.Basic.normSq_eq_canonical, Gaussian.Power.normSq_natPow, Gaussian.Constants.normSq_gamma]

/-- Construct the centered circle based at the inverse of the indicated power of one plus i.

The primary stereographic chart has squared radius equal to the inverse of two raised to the natural exponent. -/
def inverseDyadicCircle (exponent : Nat) : Curve.RationalCurve
  :=
  Curve.Canonical.Circle.circle ((Gaussian.Power.natPow Canonical.gamma exponent)⁻¹)

/-- Every inverse-dyadic circle point has quadrance equal to the inverse of two raised to its exponent. -/
theorem normSq_inverseDyadicCircle_point
    (exponent : Nat) (parameter : Rational) :
    Gaussian.Norm.Basic.normSq ((inverseDyadicCircle exponent).point parameter) =
      ((2 : Rational) ^ exponent)⁻¹ := by
  have powerNonzero : Gaussian.Power.natPow Canonical.gamma exponent ≠ 0 :=
    Gaussian.Power.natPow_ne_zero_direct Canonical.gamma (by
      intro gammaZero
      have realZero := congrArg Gaussian.Basic.re gammaZero
      exact Rat.Fraction.Field.zero_ne_one realZero.symm) exponent
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  rw [inverseDyadicCircle, Curve.Canonical.Circle.normSq_circle_point]
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical, Gaussian.Field.inv_eq, Gaussian.Field.normSq_inv _ powerNonzero,
    Gaussian.Power.normSq_natPow, Gaussian.Constants.normSq_gamma]

end

open Purelib.RationalFunctions in
/-- Choose the centered circle whose quadrance times two to the given exponent equals two.

Exponent zero uses the circle of quadrance two. A successor exponent uses the inverse-dyadic circle at its predecessor.
-/
def lowUpperCircle : Nat → Curve.RationalCurve
  | 0 => dyadicCircle 1
  | exponent + 1 => inverseDyadicCircle exponent

open Purelib.Data in
open Purelib.RationalFunctions in
/-- Multiplying a low-upper-circle point's quadrance by two to the given exponent yields two. -/
theorem scaled_normSq_lowUpperCircle_point
    (exponent : Nat) (parameter : Rational) :
    (2 : Rational) ^ exponent *
        Gaussian.Norm.Basic.normSq ((lowUpperCircle exponent).point parameter) = 2 := by
  cases exponent with
  | zero =>
      simp only [lowUpperCircle, pow_zero,
        normSq_dyadicCircle_point, pow_one]
      exact _root_.one_mul 2
  | succ exponent =>
      rw [lowUpperCircle, normSq_inverseDyadicCircle_point, pow_succ]
      have powerNonzero : (2 : Rational) ^ exponent ≠ 0 := by
        intro powerZero
        have powerPositive :=
          Rat.Fraction.Order.Arithmetic.pow_pos_direct
            (show (0 : Rational) < 2 by decide) exponent
        rw [powerZero] at powerPositive
        exact (lt_irrefl 0 powerPositive).elim
      calc
        ((2 : Rational) ^ exponent * 2) *
            ((2 : Rational) ^ exponent)⁻¹ =
          2 * ((2 : Rational) ^ exponent *
            ((2 : Rational) ^ exponent)⁻¹) := by
              calc
                ((2 : Rational) ^ exponent * 2) *
                    ((2 : Rational) ^ exponent)⁻¹ =
                  (2 * (2 : Rational) ^ exponent) *
                    ((2 : Rational) ^ exponent)⁻¹ := by
                      rw [Rat.Fraction.Field.mul_comm
                        ((2 : Rational) ^ exponent) 2]
                _ = 2 * ((2 : Rational) ^ exponent *
                    ((2 : Rational) ^ exponent)⁻¹) :=
                  Rat.Fraction.Field.mul_assoc _ _ _
        _ = 2 * 1 := by
          rw [Rat.Fraction.Field.mul_inv_cancel _ powerNonzero]
        _ = 2 := Rat.Fraction.Field.mul_one_direct _

end Purelib.RationalFunctions.Curve.Canonical.Circle

end
