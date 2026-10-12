module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
public import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Legendre

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

namespace Purelib.Curves.Legendre.PicardFuchs.Clearance

/-! ## Exact parameter clearance -/

set_option genInjectivity false in
/-- Rational lower bounds keeping one displayed parameter away from both singular Legendre values. -/
structure ParameterClearance (parameter :
  Data.Gaussian.Basic.Canonical) where
  /-- The retained rational lower bound for squared distance from parameter zero. -/ zeroBound : Fraction.Rational
  /-- The retained zero clearance is strictly positive. -/ zeroPositive : 0 < zeroBound
  /-- The zero clearance is bounded by the squared norm of the exact parameter. -/ zeroLower : zeroBound <=
    Data.Gaussian.Norm.Basic.normSq parameter
  /-- The retained rational lower bound for squared distance from parameter one. -/ oneBound : Fraction.Rational
  /-- The retained one clearance is strictly positive. -/ onePositive : 0 < oneBound
  /-- The one clearance is bounded by the squared norm of the parameter minus one. -/ oneLower : oneBound <=
    Data.Gaussian.Norm.Basic.normSq (parameter - 1)

constructive_injectivity Purelib.Curves.Legendre.PicardFuchs.Clearance.ParameterClearance

namespace ParameterClearance

/-- Every point of an already certified Legendre segment carries the exact parameter denominator clearance needed by the
connection. -/
def ofSegmentPoint {start finish :
  Data.Gaussian.Basic.Canonical}
    {left : Paths.Frame start} {right : Paths.Frame finish}
    (segment : Paths.Segment left right) (fraction : Fraction.Rational) :
    Curves.Legendre.PicardFuchs.Clearance.ParameterClearance (segment.geometry.pointAt fraction) where
  zeroBound := segment.safe.avoidsZero.bound
  zeroPositive := segment.safe.avoidsZero.positive
  zeroLower := by
    simpa only [Data.Gaussian.Basic.sub_zero] using
      segment.safe.avoidsZero.normSq_lower fraction
  oneBound := segment.safe.avoidsOne.bound
  onePositive := segment.safe.avoidsOne.positive
  oneLower := segment.safe.avoidsOne.normSq_lower fraction

/-- Positive retained clearance excludes the singular parameter zero. -/
theorem parameter_ne_zero {parameter :
  Data.Gaussian.Basic.Canonical}
    (clearance : Curves.Legendre.PicardFuchs.Clearance.ParameterClearance parameter) : parameter ≠ 0 := by
  intro parameterZero
  have normZero : Data.Gaussian.Norm.Basic.normSq parameter = 0 := by
    rw [parameterZero]
    rfl
  have lower : clearance.zeroBound <= 0 :=
    clearance.zeroLower.trans_eq normZero
  exact (not_le_of_gt clearance.zeroPositive) lower

/-- Positive retained clearance excludes the singular parameter one. -/
theorem parameter_sub_one_ne_zero {parameter :
  Data.Gaussian.Basic.Canonical}
    (clearance : Curves.Legendre.PicardFuchs.Clearance.ParameterClearance parameter) : parameter - 1 ≠ 0 := by
  intro differenceZero
  have normZero :
      Data.Gaussian.Norm.Basic.normSq (parameter - 1) = 0 := by
    rw [differenceZero]
    rfl
  have lower : clearance.oneBound <= 0 :=
    clearance.oneLower.trans_eq normZero
  exact (not_le_of_gt clearance.onePositive) lower

/-- The reversed parameter-one difference is nonzero under the retained clearance. -/
theorem one_sub_parameter_ne_zero {parameter :
  Data.Gaussian.Basic.Canonical}
    (clearance : Curves.Legendre.PicardFuchs.Clearance.ParameterClearance parameter) : 1 - parameter ≠ 0 := by
  intro differenceZero
  apply clearance.parameter_sub_one_ne_zero
  have oneEqual : (1 : Data.Gaussian.Basic.Canonical) = parameter :=
    Data.Gaussian.Basic.gaussian_eq_of_sub_eq_zero differenceZero
  cases oneEqual
  rfl

/-- The common fraction-free connection denominator. -/
def connectionDenominator (parameter :
  Data.Gaussian.Basic.Canonical) : Data.Gaussian.Basic.Canonical :=
  2 * parameter * (1 - parameter)

/-- Both parameter clearances make the exact connection denominator nonzero. -/
theorem connectionDenominator_ne_zero {parameter
  : Data.Gaussian.Basic.Canonical}
    (clearance : Curves.Legendre.PicardFuchs.Clearance.ParameterClearance parameter) :
    connectionDenominator parameter ≠ 0 :=
  Data.Gaussian.Field.mul_ne_zero_direct
    (Data.Gaussian.Field.mul_ne_zero_direct
      (by decide) clearance.parameter_ne_zero)
    clearance.one_sub_parameter_ne_zero

/-- A positive rational lower bound for the squared norm of the common connection denominator. -/
def connectionLowerSq {parameter :
  Data.Gaussian.Basic.Canonical}
    (clearance : Curves.Legendre.PicardFuchs.Clearance.ParameterClearance parameter) : Fraction.Rational :=
  4 * clearance.zeroBound * clearance.oneBound

/-- The product of the two positive clearances gives a strictly positive squared denominator bound. -/
theorem connectionLowerSq_positive {parameter :
  Data.Gaussian.Basic.Canonical}
    (clearance : Curves.Legendre.PicardFuchs.Clearance.ParameterClearance parameter) :
    0 < clearance.connectionLowerSq := by
  unfold PicardFuchs.Clearance.ParameterClearance.connectionLowerSq
  exact Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      clearance.zeroPositive) clearance.onePositive

/-- The retained connection bound does not exceed the squared norm of the exact connection denominator. -/
theorem connectionLowerSq_le_normSq {parameter :
  Data.Gaussian.Basic.Canonical}
    (clearance : Curves.Legendre.PicardFuchs.Clearance.ParameterClearance parameter) :
    clearance.connectionLowerSq <=
      Data.Gaussian.Norm.Basic.normSq
        (connectionDenominator parameter) := by
  have productLower : clearance.zeroBound * clearance.oneBound <=
      Data.Gaussian.Norm.Basic.normSq parameter *
        Data.Gaussian.Norm.Basic.normSq (parameter - 1) :=
    Fraction.Order.Arithmetic.mul_le_mul_direct clearance.zeroLower
      clearance.oneLower clearance.onePositive.le
      (Data.Gaussian.Norm.Basic.normSq_nonneg parameter)
  have scaled :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      productLower (by decide : (0 : Fraction.Rational) <= 4)
  calc
    clearance.connectionLowerSq =
        4 * (clearance.zeroBound * clearance.oneBound) := by
      unfold PicardFuchs.Clearance.ParameterClearance.connectionLowerSq
      ring1
    _ <= 4 *
        (Data.Gaussian.Norm.Basic.normSq parameter *
          Data.Gaussian.Norm.Basic.normSq (parameter - 1)) := scaled
    _ = Data.Gaussian.Norm.Basic.normSq
        (connectionDenominator parameter) := by
      unfold connectionDenominator
      rw [Data.Gaussian.Norm.Basic.normSq_mul,
        Data.Gaussian.Norm.Basic.normSq_mul]
      have opposite : (1 - parameter : Data.Gaussian.Basic.Canonical) = -(parameter - 1) := by
        ring1
      rw [opposite, Data.Gaussian.Norm.Basic.normSq_neg]
      change 4 *
          (Data.Gaussian.Norm.Basic.normSq parameter *
            Data.Gaussian.Norm.Basic.normSq (parameter - 1)) =
        (2 * 2 + 0 * 0) *
          Data.Gaussian.Norm.Basic.normSq parameter *
            Data.Gaussian.Norm.Basic.normSq (parameter - 1)
      ring1

end ParameterClearance

/-- Read the exact common denominator twice the parameter times one minus the parameter. -/
def connectionDenominator (parameter :
  Data.Gaussian.Basic.Canonical) : Data.Gaussian.Basic.Canonical :=
  Curves.Legendre.PicardFuchs.Clearance.ParameterClearance.connectionDenominator parameter
end Purelib.Curves.Legendre.PicardFuchs.Clearance

end
