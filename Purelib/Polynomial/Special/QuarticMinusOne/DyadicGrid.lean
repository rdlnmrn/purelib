module
import Purelib.Polynomial.Power.Gaussian
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Riemann.Periods.PeriodCurves
import Purelib.Data.Rat.Fraction.Order.NatCast
public import Purelib.Data.Gaussian.Components.Basic
public import Purelib.Data.Rat.Dyadic.Grid
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data

open Purelib

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Exact local certificates for the prepared cyclic quartic

The first outer cell of the canonical connector from `-1` to `1` runs along
the horizontal line `im z = -1/2`, from `-5/4` to `-1`.  This file records
the nine endpoints of its depth-three dyadic subdivision and caches the exact
values of `z^4 - 1` there as reduced constructive rationals.

Storing the reduced representatives, including their explicit Bezout
certificates, is important for the later prepared-sheet checks: direct box
clearance can inspect these small values instead of repeatedly normalizing the
large rational expression obtained by polynomial evaluation.
-/

namespace Purelib.Polynomial.Special.QuarticMinusOne.DyadicGrid

/-- The quartic grid's real component has its explicit rational numerator.

The formula uses denominator 1048576 for every rational grid parameter. -/
private theorem quarticGridReal (n : Fraction.Rational) :
    ((n / 32) ^ 2 - 1 / 4) ^ 2 - (n / 32) ^ 2 - 1 =
      (n ^ 4 - 1536 * n ^ 2 - 983040) / 1048576 := by
  have thirtyTwoNe := (Fraction.Order.NatCast.natCast_pos_direct 32 (by omega)).ne'
  have oneThousandTwentyFourNe := (Fraction.Order.NatCast.natCast_pos_direct 1024 (by omega)).ne'
  have oneMillionNe := (Fraction.Order.NatCast.natCast_pos_direct 1048576 (by omega)).ne'
  have uSquare : (n / 32) ^ 2 = n ^ 2 / 1024 := by
    rw [pow_two, Fraction.Field.div_mul_div_direct]
    apply Fraction.Field.div_eq_div_of_cross_mul
      (Fraction.Field.mul_ne_zero_direct thirtyTwoNe thirtyTwoNe)
      oneThousandTwentyFourNe
    ring1
  have quarterCommon : (1 / 4 : Fraction.Rational) = 256 / 1024 := by
    apply Fraction.Field.div_eq_div_of_cross_mul
      (Fraction.Order.NatCast.natCast_pos_direct 4 (by omega)).ne' oneThousandTwentyFourNe
    ring1
  have difference : (n / 32) ^ 2 - 1 / 4 =
      (n ^ 2 - 256) / 1024 := by
    rw [uSquare, quarterCommon,
      Fraction.Compatibility.subSameDenominator (n ^ 2) 256 1024 oneThousandTwentyFourNe]
  have differenceSquare : ((n ^ 2 - 256) / 1024) ^ 2 =
      (n ^ 2 - 256) ^ 2 / 1048576 := by
    rw [pow_two, Fraction.Field.div_mul_div_direct]
    apply Fraction.Field.div_eq_div_of_cross_mul
      (Fraction.Field.mul_ne_zero_direct
        oneThousandTwentyFourNe oneThousandTwentyFourNe)
      oneMillionNe
    ring1
  have uSquareCommon : n ^ 2 / 1024 =
      (1024 * n ^ 2) / 1048576 := by
    apply Fraction.Field.div_eq_div_of_cross_mul
      oneThousandTwentyFourNe oneMillionNe
    ring1
  have oneCommon : (1 : Fraction.Rational) = 1048576 / 1048576 := by
    apply Fraction.Field.mul_right_cancel_of_ne oneMillionNe
    rw [_root_.one_mul]
    exact (Fraction.Field.div_mul_cancel_of_ne _ _
      oneMillionNe).symm
  rw [difference, differenceSquare, uSquare, uSquareCommon, oneCommon]
  rw [Fraction.Compatibility.subSameDenominator ((n ^ 2 - 256) ^ 2) (1024 * n ^ 2)
    1048576 oneMillionNe]
  rw [Fraction.Compatibility.subSameDenominator
    ((n ^ 2 - 256) ^ 2 - 1024 * n ^ 2) 1048576
      1048576 oneMillionNe]
  congr 1
  ring1

/-- The quartic grid's imaginary component has its explicit rational numerator.

The formula uses denominator 16384 for every rational grid parameter. -/
private theorem quarticGridImaginary (n :
  Fraction.Rational) :
    2 * (n / 32) * ((n / 32) ^ 2 - 1 / 4) =
      (n ^ 3 - 256 * n) / 16384 := by
  have thirtyTwoNe := (Fraction.Order.NatCast.natCast_pos_direct 32 (by omega)).ne'
  have oneThousandTwentyFourNe := (Fraction.Order.NatCast.natCast_pos_direct 1024 (by omega)).ne'
  have sixteenThousandNe := (Fraction.Order.NatCast.natCast_pos_direct 16384 (by omega)).ne'
  have thirtyTwoThousandNe := (Fraction.Order.NatCast.natCast_pos_direct 32768 (by omega)).ne'
  have uSquare : (n / 32) ^ 2 = n ^ 2 / 1024 := by
    rw [pow_two, Fraction.Field.div_mul_div_direct]
    apply Fraction.Field.div_eq_div_of_cross_mul
      (Fraction.Field.mul_ne_zero_direct thirtyTwoNe thirtyTwoNe)
      oneThousandTwentyFourNe
    ring1
  have quarterCommon : (1 / 4 : Fraction.Rational) = 256 / 1024 := by
    apply Fraction.Field.div_eq_div_of_cross_mul
      (Fraction.Order.NatCast.natCast_pos_direct 4 (by omega)).ne' oneThousandTwentyFourNe
    ring1
  have difference : (n / 32) ^ 2 - 1 / 4 =
      (n ^ 2 - 256) / 1024 := by
    rw [uSquare, quarterCommon,
      Fraction.Compatibility.subSameDenominator (n ^ 2) 256 1024 oneThousandTwentyFourNe]
  rw [difference]
  have product : (n / 32) * ((n ^ 2 - 256) / 1024) =
      (n * (n ^ 2 - 256)) / 32768 := by
    rw [Fraction.Field.div_mul_div_direct]
    apply Fraction.Field.div_eq_div_of_cross_mul
      (Fraction.Field.mul_ne_zero_direct thirtyTwoNe
        oneThousandTwentyFourNe) thirtyTwoThousandNe
    ring1
  rw [show (2 : Fraction.Rational) * (n / 32) * ((n ^ 2 - 256) / 1024) =
    2 * ((n / 32) * ((n ^ 2 - 256) / 1024)) by ring1, product]
  change 2 * ((n * (n ^ 2 - 256)) / 32768) = _
  have asFraction : 2 * ((n * (n ^ 2 - 256)) / 32768) =
      (2 * (n * (n ^ 2 - 256))) / 32768 := by
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    ring1
  rw [asFraction]
  apply Fraction.Field.div_eq_div_of_cross_mul
    thirtyTwoThousandNe sixteenThousandNe
  ring1

open Purelib.Polynomial
/-- Exact symbolic value of `z^4 - 1` on the dyadic horizontal grid used by
the first prepared connector cell. -/
theorem quarticGridEvaluation (n : Fraction.Rational) :
    Riemann.Periods.PeriodCurves.quarticPolynomial.eval
        (Gaussian.Components.Basic.point (-(n / 32)) (-1 / 2)) =
      Gaussian.Components.Basic.point ((n ^ 4 - 1536 * n ^ 2 - 983040) / 1048576)
        ((n ^ 3 - 256 * n) / 16384) := open Purelib.Polynomial in by
  unfold Riemann.Periods.PeriodCurves.quarticPolynomial
  rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval]
  unfold Riemann.Periods.PeriodCurves.degreeFour
  have halfSquare : (-1 / 2 : Fraction.Rational) ^ 2 = 1 / 4 := by
    with_unfolding_all decide
  have negHalfPlusNegHalf : (-1 / 2 : Fraction.Rational) + (-1 / 2) = -1 := by
    with_unfolding_all decide
  have firstSquare : Gaussian.Components.Basic.point (-(n / 32)) (-1 / 2) ^ 2 =
      Gaussian.Components.Basic.point ((n / 32) ^ 2 - 1 / 4) (n / 32) := by
    rw [pow_two]
    apply Gaussian.Basic.ext
    · simp only [Gaussian.Basic.mul_re,
        Gaussian.Components.Basic.point]
      calc
        (-(n / 32)) * (-(n / 32)) - (-1 / 2) * (-1 / 2) =
            (n / 32) ^ 2 - (-1 / 2) ^ 2 := by ring1
        _ = (n / 32) ^ 2 - 1 / 4 := by rw [halfSquare]
    · simp only [Gaussian.Basic.mul_im,
        Gaussian.Components.Basic.point]
      calc
        (-(n / 32)) * (-1 / 2) + (-1 / 2) * (-(n / 32)) =
            (-(n / 32)) * ((-1 / 2) + (-1 / 2)) := by ring1
        _ = (-(n / 32)) * (-1) := by rw [negHalfPlusNegHalf]
        _ = n / 32 := by ring1
  rw [show Gaussian.Components.Basic.point (-(n / 32)) (-1 / 2) ^ 4 =
    (Gaussian.Components.Basic.point (-(n / 32)) (-1 / 2) ^ 2) ^ 2 by ring1, firstSquare, pow_two]
  apply Gaussian.Basic.ext
  · simp only [Gaussian.Basic.mul_re,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.one_re,
      Gaussian.Components.Basic.point]
    simpa only [pow_two] using quarticGridReal n
  · simp only [Gaussian.Basic.mul_im,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.one_im,
      Gaussian.Components.Basic.point]
    calc
      ((n / 32) ^ 2 - 1 / 4) * (n / 32) +
          (n / 32) * ((n / 32) ^ 2 - 1 / 4) - 0 =
        2 * (n / 32) * ((n / 32) ^ 2 - 1 / 4) := by ring1
      _ = (n ^ 3 - 256 * n) / 16384 := quarticGridImaginary n
/-- The quartic grid evaluation expressed in the common fine dyadic unit.

This form keeps grid parameters scaled uniformly for exact cell certificates. -/
theorem quarticGridEvaluation_scaled (n :
  Fraction.Rational) :
    Riemann.Periods.PeriodCurves.quarticPolynomial.eval
        (Gaussian.Components.Basic.point (-(n / 32)) (-1 / 2)) =
      Gaussian.Components.Basic.point ((n ^ 4 - 1536 * n ^ 2 - 983040) * Data.Rat.Dyadic.Grid.fineUnit)
        (64 * (n ^ 3 - 256 * n) * Data.Rat.Dyadic.Grid.fineUnit) := by
  rw [quarticGridEvaluation]
  apply Gaussian.Basic.ext
  · simp only [Gaussian.Components.Basic.point]
    exact Data.Rat.Dyadic.Grid.scaledFine _ _ 1048576 (by omega) (by ring1)
  · simp only [Gaussian.Components.Basic.point]
    exact Data.Rat.Dyadic.Grid.scaledFine _ _ 16384 (by omega) (by ring1)

end Purelib.Polynomial.Special.QuarticMinusOne.DyadicGrid

end
