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

/-!
# Exact Legendre parameter clearance

Positive squared-distance bounds exclude the two singular parameter values
and control the fraction-free connection denominator. Exact nonvanishing
or the original labelled root frame computes these bounds directly; certified
axis segments supply uniform bounds along their parametrizations.
-/

public section

namespace Purelib.Curves.Legendre.PicardFuchs.Clearance

open Purelib
open Purelib.Curves.Legendre
open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-! ## Exact parameter clearance -/

set_option genInjectivity false in
/-- Rational lower bounds keeping one displayed parameter away from both singular Legendre values. -/
structure ParameterClearance (parameter :
  Basic.Canonical) where
  /-- The retained rational lower bound for squared distance from parameter zero. -/ zeroBound : Fraction.Rational
  /-- The retained zero clearance is strictly positive. -/ zeroPositive : 0 < zeroBound
  /-- The zero clearance is bounded by the squared norm of the exact parameter. -/ zeroLower : zeroBound <=
    Norm.Basic.normSq parameter
  /-- The retained rational lower bound for squared distance from parameter one. -/ oneBound : Fraction.Rational
  /-- The retained one clearance is strictly positive. -/ onePositive : 0 < oneBound
  /-- The one clearance is bounded by the squared norm of the parameter minus one. -/ oneLower : oneBound <=
    Norm.Basic.normSq (parameter - 1)

constructive_injectivity ParameterClearance

namespace ParameterClearance

/-- Compute exact squared-distance clearances from the two nonzero parameter differences.

The retained bounds are the squared norms of the original parameter and its
original difference from one. Their strict positivity follows constructively
from the two nonvanishing hypotheses. -/
@[expose] def ofParameter (parameter : Basic.Canonical)
    (nonzero : parameter ≠ 0) (differenceNonzero : parameter - 1 ≠ 0) :
    ParameterClearance parameter where
  zeroBound := Norm.Basic.normSq parameter
  zeroPositive := Norm.Basic.normSq_pos nonzero
  zeroLower := Fraction.Order.Basic.le_refl _
  oneBound := Norm.Basic.normSq (parameter - 1)
  onePositive := Norm.Basic.normSq_pos differenceNonzero
  oneLower := Fraction.Order.Basic.le_refl _

/-- Compute parameter clearance from the original labelled root frame.

The separated owners already exclude the two singular parameter values, so
no additional numerical bound or nonvanishing witness is an input. -/
@[expose] def ofFrame {parameter : Basic.Canonical}
    (frame : Paths.Frame parameter) : ParameterClearance parameter :=
  ofParameter parameter frame.parameter_ne_zero frame.parameter_sub_one_ne_zero

/-- Every unit-interval point of a safe original axis carries its two retained parameter clearances.

The same whole-axis zero and one bounds apply at every displayed point.
No root frame, projected crossing or additional clearance search is used.
-/
@[expose] def ofAxisSegmentPoint {start finish : Basic.Canonical}
    {segment : Paths.AxisSegment start finish} (safe : Paths.AxisSegment.Safe segment)
    (fraction : Fraction.Rational) (nonnegative : 0 ≤ fraction) (atMostOne : fraction ≤ 1) :
    ParameterClearance (segment.pointAt fraction) where
  zeroBound := safe.avoidsZero.bound
  zeroPositive := safe.avoidsZero.positive
  zeroLower := by
    simpa only [Basic.sub_zero] using safe.avoidsZero.normSq_lower fraction nonnegative atMostOne
  oneBound := safe.avoidsOne.bound
  onePositive := safe.avoidsOne.positive
  oneLower := safe.avoidsOne.normSq_lower fraction nonnegative atMostOne

/-- Every unit-interval point of a certified Legendre segment carries parameter denominator clearance. -/
@[expose] def ofSegmentPoint {start finish :
  Basic.Canonical}
    {left : Paths.Frame start} {right : Paths.Frame finish}
    (segment : Paths.Segment left right) (fraction : Fraction.Rational)
    (nonnegative : 0 ≤ fraction) (atMostOne : fraction ≤ 1) :
    ParameterClearance (segment.geometry.pointAt fraction) :=
  ofAxisSegmentPoint segment.safe fraction nonnegative atMostOne

/-- Positive retained clearance excludes the singular parameter zero. -/
theorem parameter_ne_zero {parameter :
  Basic.Canonical}
    (clearance : ParameterClearance parameter) : parameter ≠ 0 := by
  intro parameterZero
  have normZero : Norm.Basic.normSq parameter = 0 := by
    rw [parameterZero]
    rfl
  have lower : clearance.zeroBound <= 0 :=
    clearance.zeroLower.trans_eq normZero
  exact (not_le_of_gt clearance.zeroPositive) lower

/-- Positive retained clearance excludes the singular parameter one. -/
theorem parameter_sub_one_ne_zero {parameter :
  Basic.Canonical}
    (clearance : ParameterClearance parameter) : parameter - 1 ≠ 0 := by
  intro differenceZero
  have normZero :
      Norm.Basic.normSq (parameter - 1) = 0 := by
    rw [differenceZero]
    rfl
  have lower : clearance.oneBound <= 0 :=
    clearance.oneLower.trans_eq normZero
  exact (not_le_of_gt clearance.onePositive) lower

/-- The reversed parameter-one difference is nonzero under the retained clearance. -/
theorem one_sub_parameter_ne_zero {parameter :
  Basic.Canonical}
    (clearance : ParameterClearance parameter) : 1 - parameter ≠ 0 := by
  intro differenceZero
  apply clearance.parameter_sub_one_ne_zero
  have oneEqual : (1 : Basic.Canonical) = parameter :=
    Basic.gaussian_eq_of_sub_eq_zero differenceZero
  cases oneEqual
  rfl

/-- The common fraction-free connection denominator. -/
@[expose] def connectionDenominator (parameter :
  Basic.Canonical) : Basic.Canonical :=
  2 * parameter * (1 - parameter)

/-- Both parameter clearances make the exact connection denominator nonzero. -/
theorem connectionDenominator_ne_zero {parameter
  : Basic.Canonical}
    (clearance : ParameterClearance parameter) :
    connectionDenominator parameter ≠ 0 :=
  Field.mul_ne_zero_direct
    (Field.mul_ne_zero_direct
      (by decide) clearance.parameter_ne_zero)
    clearance.one_sub_parameter_ne_zero

/-- A positive rational lower bound for the squared norm of the common connection denominator. -/
@[expose] def connectionLowerSq {parameter :
  Basic.Canonical}
    (clearance : ParameterClearance parameter) : Fraction.Rational :=
  4 * clearance.zeroBound * clearance.oneBound

/-- The product of the two positive clearances gives a strictly positive squared denominator bound. -/
theorem connectionLowerSq_positive {parameter :
  Basic.Canonical}
    (clearance : ParameterClearance parameter) :
    0 < clearance.connectionLowerSq := by
  unfold connectionLowerSq
  exact Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      clearance.zeroPositive) clearance.onePositive

/-- The retained connection bound does not exceed the squared norm of the exact connection denominator. -/
theorem connectionLowerSq_le_normSq {parameter :
  Basic.Canonical}
    (clearance : ParameterClearance parameter) :
    clearance.connectionLowerSq <=
      Norm.Basic.normSq
        (connectionDenominator parameter) := by
  have productLower : clearance.zeroBound * clearance.oneBound <=
      Norm.Basic.normSq parameter *
        Norm.Basic.normSq (parameter - 1) :=
    Fraction.Order.Arithmetic.mul_le_mul_direct clearance.zeroLower
      clearance.oneLower clearance.onePositive.le
      (Norm.Basic.normSq_nonneg parameter)
  have scaled :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      productLower (by decide : (0 : Fraction.Rational) <= 4)
  calc
    clearance.connectionLowerSq =
        4 * (clearance.zeroBound * clearance.oneBound) := by
      unfold connectionLowerSq
      ring1
    _ <= 4 *
        (Norm.Basic.normSq parameter *
          Norm.Basic.normSq (parameter - 1)) := scaled
    _ = Norm.Basic.normSq
        (connectionDenominator parameter) := by
      unfold connectionDenominator
      rw [Norm.Basic.normSq_mul,
        Norm.Basic.normSq_mul]
      have opposite : (1 - parameter : Basic.Canonical) = -(parameter - 1) := by
        ring1
      rw [opposite, Norm.Basic.normSq_neg]
      change 4 *
          (Norm.Basic.normSq parameter *
            Norm.Basic.normSq (parameter - 1)) =
        (2 * 2 + 0 * 0) *
          Norm.Basic.normSq parameter *
            Norm.Basic.normSq (parameter - 1)
      ring1

end ParameterClearance

/-- Read the exact common denominator twice the parameter times one minus the parameter. -/
@[expose] def connectionDenominator (parameter :
  Basic.Canonical) : Basic.Canonical :=
  ParameterClearance.connectionDenominator parameter
end Purelib.Curves.Legendre.PicardFuchs.Clearance
