module
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Norm.Small
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.GaussianInt.Embedding
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section
public section

/-!
# Two-parameter finite critical cylinders

After one critical Pell basis transition, the normalized error coordinate
and normalized denominator coordinate generally carry different rational
parameters.  This module proves the cylinder exterior estimate uniformly
when both supplied parameters lie in the finite critical chamber.  The proof
uses a uniform rational coefficient bound followed by the same finite
unit/diagonal case split as the one-parameter critical cylinder.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.TwoParameter

/-- The exact rational constant one half. -/
@[expose] def half : Fraction.Rational := 1 / 2

/-- The square of the retained half is one quarter. -/
private theorem half_sq : Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 = (1 / 4 : Fraction.Rational) := by
  unfold Dirichlet.Critical.Cylinder.TwoParameter.half
  decide

/-- Normalized upper error with its independently supplied parameter. -/
@[expose] def errorRatio (value : Fraction.Rational) : Gaussian.Basic.Canonical :=
  ⟨Dirichlet.Critical.Cylinder.TwoParameter.half, Dirichlet.Critical.Cylinder.TwoParameter.half * value⟩

/-- Normalized lower denominator with its independently supplied parameter. -/
@[expose] def denominatorRatio (value : Fraction.Rational) : Gaussian.Basic.Canonical :=
  ⟨Dirichlet.Critical.Cylinder.TwoParameter.half * value, -Dirichlet.Critical.Cylinder.TwoParameter.half⟩

/-- The real error-ratio coordinate is one half. -/
@[simp] theorem errorRatio_re (value : Fraction.Rational) :
    (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio value).re = (1 / 2 : Fraction.Rational) := by
  rfl

/-- The imaginary error-ratio coordinate is half its parameter. -/
@[simp] theorem errorRatio_im (value : Fraction.Rational) :
    (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio value).im = (1 / 2 : Fraction.Rational) * value := by
  rfl

/-- The real denominator-ratio coordinate is half its parameter. -/
@[simp] theorem denominatorRatio_re (value : Fraction.Rational) :
    (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio value).re = (1 / 2 : Fraction.Rational) * value := by
  rfl

/-- The imaginary denominator-ratio coordinate is minus one half. -/
@[simp] theorem denominatorRatio_im (value : Fraction.Rational) :
    (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio value).im = -(1 / 2 : Fraction.Rational) := by
  rfl

/-- The normalized error of a Gaussian integer coefficient pair.

The left coefficient contributes directly and the right coefficient is multiplied by the independently supplied error
ratio. -/
@[expose] def normalizedError
    (errorParameter : Fraction.Rational) (left right : GaussianInt) : Gaussian.Basic.Canonical :=
  GaussianInt.toGaussian left + GaussianInt.toGaussian right * Dirichlet.Critical.Cylinder.TwoParameter.errorRatio
    errorParameter

/-- The normalized denominator of a Gaussian integer coefficient pair.

The left coefficient is multiplied by the independently supplied denominator ratio and the right coefficient contributes
directly. -/
@[expose] def normalizedDenominator
    (denominatorParameter : Fraction.Rational)
    (left right : GaussianInt) : Gaussian.Basic.Canonical :=
  GaussianInt.toGaussian left * Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter +
    GaussianInt.toGaussian right

/-- The determinant factor `1 - denominatorRatio * errorRatio` of the two-parameter basis. -/
@[expose] def gapVector
    (errorParameter denominatorParameter : Fraction.Rational) : Gaussian.Basic.Canonical :=
  1 - Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter *
    Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter

/-- The quadrance of the two-parameter determinant factor. -/
@[expose] def gap (errorParameter denominatorParameter : Fraction.Rational) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq
    (Dirichlet.Critical.Cylinder.TwoParameter.gapVector errorParameter denominatorParameter)

/-- On the diagonal, the two-parameter gap is the original critical gap. -/
theorem diagonalGap_eq_criticalGap (value : Fraction.Rational) :
    Dirichlet.Critical.Cylinder.TwoParameter.gap value value = Dirichlet.Critical.Cylinder.Basic.criticalGap value := by
  rfl

/-- The error-ratio quadrance is one quarter plus the square of half its parameter. -/
theorem normSq_errorRatio (value : Fraction.Rational) :
    Data.Gaussian.Norm.Basic.normSq (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio value) =
      Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 + (Dirichlet.Critical.Cylinder.TwoParameter.half * value) ^ 2 :=
        by
  rfl

/-- The denominator-ratio quadrance is one quarter plus the square of half its parameter. -/
theorem normSq_denominatorRatio (value : Fraction.Rational) :
    Data.Gaussian.Norm.Basic.normSq (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio value) =
      Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 + (Dirichlet.Critical.Cylinder.TwoParameter.half * value) ^ 2 :=
        by
  unfold Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio Data.Gaussian.Norm.Basic.normSq
  ring1

/-- A parameter in the finite critical chamber is nonnegative. -/
private theorem parameter_nonnegative
    {value : Fraction.Rational}
    (certificate : Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter value) :
    0 ≤ value :=
  (show (0 : Fraction.Rational) ≤ 1 / 4 by decide).trans certificate.1

/-- A parameter in the finite critical chamber is at most one third. -/
private theorem parameter_le_oneThird
    {value : Fraction.Rational}
    (certificate : Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter value) :
    value ≤ 1 / 3 := certificate.2.1.le

/-- Twice one plus the error-ratio quadrance is at most `23/9`.

The critical-chamber bounds place the parameter between zero and one third, so its squared contribution is uniformly
bounded. -/
private theorem coordinateNorm_le_twentyThreeEighteenths
    {value : Fraction.Rational}
    (certificate : Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter value) :
    2 * (1 + Data.Gaussian.Norm.Basic.normSq
      (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio value)) ≤ 23 / 9 := by
  have scaledSquare : (Dirichlet.Critical.Cylinder.TwoParameter.half * value) ^ 2 ≤
      (Dirichlet.Critical.Cylinder.TwoParameter.half * (1 / 3 : Fraction.Rational)) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (show (0 : Fraction.Rational) ≤ Dirichlet.Critical.Cylinder.TwoParameter.half by
            unfold Dirichlet.Critical.Cylinder.TwoParameter.half;
            decide)
        (Dirichlet.Critical.Cylinder.TwoParameter.parameter_nonnegative certificate))
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Dirichlet.Critical.Cylinder.TwoParameter.parameter_le_oneThird certificate)
        (show (0 : Fraction.Rational) ≤ Dirichlet.Critical.Cylinder.TwoParameter.half by
            unfold Dirichlet.Critical.Cylinder.TwoParameter.half;
            decide)) 2
  rw [Dirichlet.Critical.Cylinder.TwoParameter.normSq_errorRatio]
  calc
    2 * (1 + (Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 + (Dirichlet.Critical.Cylinder.TwoParameter.half *
      value) ^ 2)) ≤
        2 * (1 + (Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 + (Dirichlet.Critical.Cylinder.TwoParameter.half *
          (1 / 3 : Fraction.Rational)) ^ 2)) := by
      apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      · exact Fraction.Order.Arithmetic.add_le_add_direct (le_refl 1)
          (Fraction.Order.Arithmetic.add_le_add_direct (le_refl (Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2))
            scaledSquare)
      · decide
    _ = 23 / 9 := by
      unfold Dirichlet.Critical.Cylinder.TwoParameter.half
      decide

/-- Twice one plus the denominator-ratio quadrance is at most `23/9` in the critical chamber. -/
private theorem coordinateNorm_denominator_le_twentyThreeEighteenths
    {value : Fraction.Rational}
    (certificate : Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter value) :
    2 * (1 + Data.Gaussian.Norm.Basic.normSq
      (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio value)) ≤ 23 / 9 := by
  rw [Dirichlet.Critical.Cylinder.TwoParameter.normSq_denominatorRatio]
  simpa only [Dirichlet.Critical.Cylinder.TwoParameter.normSq_errorRatio] using
    Dirichlet.Critical.Cylinder.TwoParameter.coordinateNorm_le_twentyThreeEighteenths certificate

/-- Every normalized error coordinate in the finite critical chamber lies
strictly inside the unit quadrance wall. -/
theorem normSq_errorRatio_lt_one
    {value : Fraction.Rational}
    (certificate : Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter value) :
    Data.Gaussian.Norm.Basic.normSq (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio value) < 1 := by
  have scaledSquare : (Dirichlet.Critical.Cylinder.TwoParameter.half * value) ^ 2 ≤
      (Dirichlet.Critical.Cylinder.TwoParameter.half * (1 / 3 : Fraction.Rational)) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (show (0 : Fraction.Rational) ≤ Dirichlet.Critical.Cylinder.TwoParameter.half by
            unfold Dirichlet.Critical.Cylinder.TwoParameter.half;
            decide)
        (Dirichlet.Critical.Cylinder.TwoParameter.parameter_nonnegative certificate))
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Dirichlet.Critical.Cylinder.TwoParameter.parameter_le_oneThird certificate)
        (show (0 : Fraction.Rational) ≤ Dirichlet.Critical.Cylinder.TwoParameter.half by
            unfold Dirichlet.Critical.Cylinder.TwoParameter.half;
            decide)) 2
  rw [Dirichlet.Critical.Cylinder.TwoParameter.normSq_errorRatio]
  calc
    Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 + (Dirichlet.Critical.Cylinder.TwoParameter.half * value) ^ 2 ≤
        Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 + (Dirichlet.Critical.Cylinder.TwoParameter.half * (1 / 3 :
          Fraction.Rational)) ^ 2 :=
      Fraction.Order.Arithmetic.add_le_add_direct (le_refl (Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2))
        scaledSquare
    _ < 1 := by
      unfold Dirichlet.Critical.Cylinder.TwoParameter.half
      decide

/-- The determinant gap is the sum of two explicit rational squares.

For parameters `s` and `t`, the squares are `(1 - (s+t)/4)^2` and `((1-s*t)/4)^2`. -/
theorem gap_eq
    (errorParameter denominatorParameter : Fraction.Rational) :
    Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter =
      (1 - Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (errorParameter + denominatorParameter)) ^ 2 +
        (Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (1 - errorParameter * denominatorParameter)) ^ 2 := by
  unfold Dirichlet.Critical.Cylinder.TwoParameter.gap Dirichlet.Critical.Cylinder.TwoParameter.gapVector
    Dirichlet.Critical.Cylinder.TwoParameter.errorRatio Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio
  simp only [Data.Gaussian.Norm.Basic.normSq,
    Gaussian.Basic.sub_re,
    Gaussian.Basic.sub_im,
    Gaussian.Basic.mul_re,
    Gaussian.Basic.mul_im,
    Gaussian.Basic.one_re,
    Gaussian.Basic.one_im]
  ring1

/-- Increasing either rational parameter within the finite critical chamber
can only decrease the exact two-parameter determinant gap. -/
theorem gap_antitone
    {errorLower errorUpper denominatorLower denominatorUpper : Fraction.Rational}
    (errorUpperCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorUpper)
    (denominatorLowerCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter denominatorLower)
    (denominatorUpperCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter denominatorUpper)
    (errorOrder : errorLower ≤ errorUpper)
    (denominatorOrder : denominatorLower ≤ denominatorUpper) :
    Dirichlet.Critical.Cylinder.TwoParameter.gap errorUpper denominatorUpper ≤
      Dirichlet.Critical.Cylinder.TwoParameter.gap errorLower denominatorLower := by
  have halfSquareNonnegative : (0 : Fraction.Rational) ≤ Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct Dirichlet.Critical.Cylinder.TwoParameter.half
  have upperSumBound :
      errorUpper + denominatorUpper ≤ (2 / 3 : Fraction.Rational) := by
    calc
      errorUpper + denominatorUpper ≤ 1 / 3 + 1 / 3 :=
        Fraction.Order.Arithmetic.add_le_add_direct
          (Dirichlet.Critical.Cylinder.TwoParameter.parameter_le_oneThird errorUpperCertificate)
          (Dirichlet.Critical.Cylinder.TwoParameter.parameter_le_oneThird denominatorUpperCertificate)
      _ = 2 / 3 := by decide
  have sumOrder :
      errorLower + denominatorLower ≤
        errorUpper + denominatorUpper :=
    Fraction.Order.Arithmetic.add_le_add_direct errorOrder denominatorOrder
  have scaledSumOrder :
      Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (errorLower + denominatorLower) ≤
        Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (errorUpper + denominatorUpper) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sumOrder
      halfSquareNonnegative
  have upperScaledSumLeOne :
      Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (errorUpper + denominatorUpper) ≤ 1 := by
    calc
      Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (errorUpper + denominatorUpper) ≤
          Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (2 / 3 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          upperSumBound halfSquareNonnegative
      _ ≤ 1 := by
        rw [Dirichlet.Critical.Cylinder.TwoParameter.half_sq]
        decide
  have firstCoordinateNonnegative :
      (0 : Fraction.Rational) ≤
        1 - Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (errorUpper + denominatorUpper) :=
    Fraction.Order.Arithmetic.sub_nonneg_direct upperScaledSumLeOne
  have firstCoordinateOrder :
      1 - Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (errorUpper + denominatorUpper) ≤
        1 - Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (errorLower + denominatorLower) :=
    Fraction.Order.Arithmetic.sub_le_sub_left_direct scaledSumOrder 1
  have firstSquareOrder :
      (1 - Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (errorUpper + denominatorUpper)) ^ 2 ≤
        (1 - Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (errorLower + denominatorLower)) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct firstCoordinateNonnegative
      firstCoordinateOrder 2
  have errorUpperNonnegative :=
    Dirichlet.Critical.Cylinder.TwoParameter.parameter_nonnegative errorUpperCertificate
  have denominatorLowerNonnegative :=
    Dirichlet.Critical.Cylinder.TwoParameter.parameter_nonnegative denominatorLowerCertificate
  have productOrder :
      errorLower * denominatorLower ≤
        errorUpper * denominatorUpper := by
    calc
      errorLower * denominatorLower ≤
          errorUpper * denominatorLower :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          errorOrder denominatorLowerNonnegative
      _ ≤ errorUpper * denominatorUpper :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          denominatorOrder errorUpperNonnegative
  have upperProductLeOne : errorUpper * denominatorUpper ≤ 1 := by
    calc
      errorUpper * denominatorUpper ≤
          (1 / 3 : Fraction.Rational) * denominatorUpper :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Dirichlet.Critical.Cylinder.TwoParameter.parameter_le_oneThird errorUpperCertificate)
          (Dirichlet.Critical.Cylinder.TwoParameter.parameter_nonnegative denominatorUpperCertificate)
      _ ≤ (1 / 3 : Fraction.Rational) * (1 / 3 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Dirichlet.Critical.Cylinder.TwoParameter.parameter_le_oneThird denominatorUpperCertificate) (by decide)
      _ ≤ 1 := by decide
  have upperComplementNonnegative :
      (0 : Fraction.Rational) ≤ 1 - errorUpper * denominatorUpper :=
    Fraction.Order.Arithmetic.sub_nonneg_direct upperProductLeOne
  have complementOrder :
      1 - errorUpper * denominatorUpper ≤
        1 - errorLower * denominatorLower :=
    Fraction.Order.Arithmetic.sub_le_sub_left_direct productOrder 1
  have secondCoordinateNonnegative :
      (0 : Fraction.Rational) ≤
        Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (1 - errorUpper * denominatorUpper) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct halfSquareNonnegative
      upperComplementNonnegative
  have secondCoordinateOrder :
      Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (1 - errorUpper * denominatorUpper) ≤
        Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (1 - errorLower * denominatorLower) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      complementOrder halfSquareNonnegative
  have secondSquareOrder :
      (Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (1 - errorUpper * denominatorUpper)) ^ 2 ≤
        (Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (1 - errorLower * denominatorLower)) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct secondCoordinateNonnegative
      secondCoordinateOrder 2
  rw [Dirichlet.Critical.Cylinder.TwoParameter.gap_eq, Dirichlet.Critical.Cylinder.TwoParameter.gap_eq]
  exact Fraction.Order.Arithmetic.add_le_add_direct firstSquareOrder
    secondSquareOrder

/-- Four times the determinant gap is at least `25/9` for two critical parameters. -/
private theorem twentyFiveNinths_le_four_mul_gap
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter) :
    25 / 9 ≤ 4 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter := by
  have sumBound :
      errorParameter + denominatorParameter ≤ (2 / 3 : Fraction.Rational) := by
    calc
      errorParameter + denominatorParameter ≤ 1 / 3 + 1 / 3 :=
        Fraction.Order.Arithmetic.add_le_add_direct
          (Dirichlet.Critical.Cylinder.TwoParameter.parameter_le_oneThird errorCertificate)
          (Dirichlet.Critical.Cylinder.TwoParameter.parameter_le_oneThird denominatorCertificate)
      _ = 2 / 3 := by decide
  have firstCoordinateBound :
      (5 / 6 : Fraction.Rational) ≤
        1 - Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (errorParameter + denominatorParameter) := by
    have scaledSum :
        Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (errorParameter + denominatorParameter) ≤
          Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (2 / 3 : Fraction.Rational) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound
        (Fraction.Order.Arithmetic.sq_nonneg_direct Dirichlet.Critical.Cylinder.TwoParameter.half)
    calc
      (5 / 6 : Fraction.Rational) = 1 - Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (2 / 3 : Fraction.Rational)
        := by
        rw [Dirichlet.Critical.Cylinder.TwoParameter.half_sq]
        decide
      _ ≤ 1 - Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 * (errorParameter + denominatorParameter) :=
        Fraction.Order.Arithmetic.sub_le_sub_left_direct scaledSum 1
  have squareBound :
      (5 / 6 : Fraction.Rational) ^ 2 ≤
        (1 - Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 *
          (errorParameter + denominatorParameter)) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct (by decide)
      firstCoordinateBound 2
  rw [Dirichlet.Critical.Cylinder.TwoParameter.gap_eq]
  calc
    (25 / 9 : Fraction.Rational) = 4 * (5 / 6 : Fraction.Rational) ^ 2 := by decide
    _ ≤ 4 *
        (1 - Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 *
          (errorParameter + denominatorParameter)) ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        squareBound (by decide)
    _ ≤ 4 *
        ((1 - Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 *
            (errorParameter + denominatorParameter)) ^ 2 +
          (Dirichlet.Critical.Cylinder.TwoParameter.half ^ 2 *
            (1 - errorParameter * denominatorParameter)) ^ 2) := by
      apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      · exact le_add_of_nonneg_right
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      · decide

/-- The error-ratio coefficient bound is strictly below four times the determinant gap.

Both parameters must lie in the finite critical chamber; the uniform `23/9` upper and `25/9` lower bounds give strict
slack. -/
theorem error_margin
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter) :
    2 * (1 + Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter)) <
      4 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter := by
  exact (Dirichlet.Critical.Cylinder.TwoParameter.coordinateNorm_le_twentyThreeEighteenths errorCertificate).trans_lt
    ((show (23 / 9 : Fraction.Rational) < 25 / 9 by decide).trans_le
      (Dirichlet.Critical.Cylinder.TwoParameter.twentyFiveNinths_le_four_mul_gap errorCertificate
        denominatorCertificate))

/-- The denominator-ratio coefficient bound is strictly below four times the determinant gap for critical parameters. -/
theorem denominator_margin
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter) :
    2 * (1 + Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter)) <
      4 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter := by
  exact
    (Dirichlet.Critical.Cylinder.TwoParameter.coordinateNorm_denominator_le_twentyThreeEighteenths
      denominatorCertificate).trans_lt
      ((show (23 / 9 : Fraction.Rational) < 25 / 9 by decide).trans_le
        (Dirichlet.Critical.Cylinder.TwoParameter.twentyFiveNinths_le_four_mul_gap errorCertificate
          denominatorCertificate))

/-- The two-parameter determinant gap is positive throughout the finite critical chamber. -/
theorem gap_pos
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter) :
    0 < Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter := by
  have onePlusPositive :
      (0 : Fraction.Rational) <
        1 + Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter) :=
    (show (0 : Fraction.Rational) < 1 by decide).trans_le
      (le_add_of_nonneg_right
        (Gaussian.Norm.Basic.normSq_nonneg _))
  have scaledPositive :
      0 < 4 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter :=
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      onePlusPositive).trans
        (Dirichlet.Critical.Cylinder.TwoParameter.error_margin errorCertificate denominatorCertificate)
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := 4)
  · calc
      (0 : Fraction.Rational) * 4 = 0 := by ring1
      _ < 4 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter := scaledPositive
      _ = Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter * 4 := by ring1
  · decide

/-- Eliminating the right coefficient recovers the left coefficient times the determinant factor. -/
private theorem left_gap_identity
    (errorParameter denominatorParameter : Fraction.Rational)
    (left right : GaussianInt) :
    GaussianInt.toGaussian left * Dirichlet.Critical.Cylinder.TwoParameter.gapVector errorParameter denominatorParameter
      =
      Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right -
        Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right *
          Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter := by
  apply Gaussian.Basic.ext <;>
    simp only [Dirichlet.Critical.Cylinder.TwoParameter.gapVector,
      Dirichlet.Critical.Cylinder.TwoParameter.normalizedError,
      Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.one_re,
      Gaussian.Basic.one_im] <;>
    ring1

/-- Eliminating the left coefficient recovers the right coefficient times the determinant factor. -/
private theorem right_gap_identity
    (errorParameter denominatorParameter : Fraction.Rational)
    (left right : GaussianInt) :
    GaussianInt.toGaussian right * Dirichlet.Critical.Cylinder.TwoParameter.gapVector errorParameter
      denominatorParameter =
      Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right -
        Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter *
          Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right := by
  apply Gaussian.Basic.ext <;>
    simp only [Dirichlet.Critical.Cylinder.TwoParameter.gapVector,
      Dirichlet.Critical.Cylinder.TwoParameter.normalizedError,
      Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.one_re,
      Gaussian.Basic.one_im] <;>
    ring1

/-- Unit bounds on both normalized quadrances force both coefficient quadrances below four.

For critical parameters, the elimination identities and strict determinant margins bound each Gaussian integer
coefficient separately. -/
private theorem coefficient_normNat_lt_four
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    (left right : GaussianInt)
    (errorBound :
      Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) ≤ 1)
    (denominatorBound :
      Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right) ≤ 1) :
    GaussianInt.normNat left < 4 ∧ GaussianInt.normNat right < 4 := by
  have errorNormNonnegative :
      (0 : Fraction.Rational) ≤
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter) :=
    Gaussian.Norm.Basic.normSq_nonneg _
  have denominatorNormNonnegative :
      (0 : Fraction.Rational) ≤
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter) :=
    Gaussian.Norm.Basic.normSq_nonneg _
  have denominatorScaledLe :
      Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right) *
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter) ≤
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter) := by
    calc
      _ ≤ (1 : Fraction.Rational) *
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          denominatorBound errorNormNonnegative
      _ = _ := by ring1
  have errorScaledLe :
      Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) *
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter) ≤
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter) := by
    calc
      _ ≤ (1 : Fraction.Rational) *
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          errorBound denominatorNormNonnegative
      _ = _ := by ring1
  have leftSumBound :
      Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) +
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right *
              Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter) ≤
        1 + Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter) := by
    rw [Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.add_le_add_direct
      errorBound denominatorScaledLe
  have rightSumBound :
      Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right) +
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter *
              Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) ≤
        1 + Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter) := by
    rw [Gaussian.Norm.Basic.normSq_mul]
    apply Fraction.Order.Arithmetic.add_le_add_direct denominatorBound
    calc
      Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter) *
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) =
        Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) *
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter) := by ring1
      _ ≤ Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter) := errorScaledLe
  have leftProductStrict :
      (GaussianInt.normNat left : Fraction.Rational) * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter
        denominatorParameter <
        4 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter := by
    calc
      (GaussianInt.normNat left : Fraction.Rational) *
          Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter =
        Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian left *
            Dirichlet.Critical.Cylinder.TwoParameter.gapVector errorParameter denominatorParameter) := by
        unfold Dirichlet.Critical.Cylinder.TwoParameter.gap
        rw [Gaussian.Norm.Basic.normSq_mul,
          GaussianInt.normSq_toGaussian]
      _ = Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right -
            Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right *
              Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter) := by
        rw [Dirichlet.Critical.Cylinder.TwoParameter.left_gap_identity]
      _ ≤ 2 *
          (Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) +
            Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right *
                Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter)) :=
        Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ ≤ 2 *
          (1 + Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          leftSumBound (by decide)
      _ < 4 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter :=
        Dirichlet.Critical.Cylinder.TwoParameter.error_margin errorCertificate denominatorCertificate
  have rightProductStrict :
      (GaussianInt.normNat right : Fraction.Rational) * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter
        denominatorParameter <
        4 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter := by
    calc
      (GaussianInt.normNat right : Fraction.Rational) *
          Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter =
        Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian right *
            Dirichlet.Critical.Cylinder.TwoParameter.gapVector errorParameter denominatorParameter) := by
        unfold Dirichlet.Critical.Cylinder.TwoParameter.gap
        rw [Gaussian.Norm.Basic.normSq_mul,
          GaussianInt.normSq_toGaussian]
      _ = Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right -
            Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter *
              Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) := by
        rw [Dirichlet.Critical.Cylinder.TwoParameter.right_gap_identity]
      _ ≤ 2 *
          (Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right) +
            Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter *
                Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right)) :=
        Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ ≤ 2 *
          (1 + Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          rightSumBound (by decide)
      _ < 4 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter :=
        Dirichlet.Critical.Cylinder.TwoParameter.denominator_margin errorCertificate denominatorCertificate
  refine ⟨?_, ?_⟩
  · apply (Fraction.Cast.Order.natCast_lt_iff_direct).1
    exact Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      leftProductStrict (Dirichlet.Critical.Cylinder.TwoParameter.gap_pos errorCertificate denominatorCertificate)
  · apply (Fraction.Cast.Order.natCast_lt_iff_direct).1
    exact Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      rightProductStrict (Dirichlet.Critical.Cylinder.TwoParameter.gap_pos errorCertificate denominatorCertificate)

/-- The denominator ratio lies strictly inside the unit quadrance wall for a critical parameter. -/
private theorem normSq_denominatorRatio_lt_one
    {value : Fraction.Rational}
    (certificate : Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter value) :
    Data.Gaussian.Norm.Basic.normSq (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio value) < 1 := by
  rw [Dirichlet.Critical.Cylinder.TwoParameter.normSq_denominatorRatio]
  simpa only [Dirichlet.Critical.Cylinder.TwoParameter.normSq_errorRatio] using
    Dirichlet.Critical.Cylinder.TwoParameter.normSq_errorRatio_lt_one certificate

/-- A coarse but finite robust cutoff: if the exact-source normalized error
quadrance is at most five and the normalized denominator remains inside its
unit wall, both Gaussian-integral coefficients lie in quadrance `< 32`. -/
theorem coefficient_normNat_lt_thirtyTwo
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    (left right : GaussianInt)
    (errorBound :
      Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) ≤ 5)
    (denominatorBound :
      Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right) ≤ 1) :
    GaussianInt.normNat left < 32 ∧ GaussianInt.normNat right < 32 := by
  have errorRatioBound :=
    (Dirichlet.Critical.Cylinder.TwoParameter.normSq_errorRatio_lt_one errorCertificate).le
  have denominatorRatioBound :=
    (Dirichlet.Critical.Cylinder.TwoParameter.normSq_denominatorRatio_lt_one denominatorCertificate).le
  have errorRatioNonnegative :=
    Gaussian.Norm.Basic.normSq_nonneg
      (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter)
  have denominatorRatioNonnegative :=
    Gaussian.Norm.Basic.normSq_nonneg
      (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter)
  have denominatorScaledLe :
      Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right) *
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter) ≤ 1 := by
    calc
      _ ≤ (1 : Fraction.Rational) *
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          denominatorBound errorRatioNonnegative
      _ = Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter) := by ring1
      _ ≤ 1 := errorRatioBound
  have errorScaledLe :
      Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) *
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter) ≤ 5 := by
    calc
      _ ≤ (5 : Fraction.Rational) *
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          errorBound denominatorRatioNonnegative
      _ ≤ 5 * (1 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          denominatorRatioBound (by decide)
      _ = 5 := by ring1
  have leftSumBound :
      Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) +
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right *
              Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter) ≤ 6 := by
    rw [Gaussian.Norm.Basic.normSq_mul]
    calc
      _ ≤ (5 : Fraction.Rational) + 1 :=
        Fraction.Order.Arithmetic.add_le_add_direct errorBound
          denominatorScaledLe
      _ = 6 := by ring1
  have rightSumBound :
      Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right) +
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter *
              Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) ≤ 6 := by
    rw [Gaussian.Norm.Basic.normSq_mul]
    calc
      Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right) +
          Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter) *
            Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) =
        Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right) +
          Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) *
            Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter) := by ring1
      _ ≤ (1 : Fraction.Rational) + 5 :=
        Fraction.Order.Arithmetic.add_le_add_direct denominatorBound
          errorScaledLe
      _ = 6 := by ring1
  have thirtyTwoGapLower :
      (16 : Fraction.Rational) ≤
        32 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter := by
    have twoLeFourGap :
        (2 : Fraction.Rational) ≤ 4 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter
          :=
      (show (2 : Fraction.Rational) ≤ 25 / 9 by decide).trans
        (Dirichlet.Critical.Cylinder.TwoParameter.twentyFiveNinths_le_four_mul_gap errorCertificate
          denominatorCertificate)
    calc
      (16 : Fraction.Rational) = 8 * 2 := by ring1
      _ ≤ 8 * (4 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          twoLeFourGap (by decide)
      _ = 32 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter := by ring1
  have leftProductStrict :
      (GaussianInt.normNat left : Fraction.Rational) *
          Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter <
        32 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter := by
    calc
      (GaussianInt.normNat left : Fraction.Rational) *
          Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter =
        Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian left *
            Dirichlet.Critical.Cylinder.TwoParameter.gapVector errorParameter denominatorParameter) := by
        unfold Dirichlet.Critical.Cylinder.TwoParameter.gap
        rw [Gaussian.Norm.Basic.normSq_mul,
          GaussianInt.normSq_toGaussian]
      _ = Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right -
            Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right *
              Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter) := by
        rw [Dirichlet.Critical.Cylinder.TwoParameter.left_gap_identity]
      _ ≤ 2 *
          (Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) +
            Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right *
                Dirichlet.Critical.Cylinder.TwoParameter.errorRatio errorParameter)) :=
        Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ ≤ 2 * (6 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          leftSumBound (by decide)
      _ = 12 := by ring1
      _ < 16 := by decide
      _ ≤ 32 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter := thirtyTwoGapLower
  have rightProductStrict :
      (GaussianInt.normNat right : Fraction.Rational) *
          Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter <
        32 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter := by
    calc
      (GaussianInt.normNat right : Fraction.Rational) *
          Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter =
        Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian right *
            Dirichlet.Critical.Cylinder.TwoParameter.gapVector errorParameter denominatorParameter) := by
        unfold Dirichlet.Critical.Cylinder.TwoParameter.gap
        rw [Gaussian.Norm.Basic.normSq_mul,
          GaussianInt.normSq_toGaussian]
      _ = Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right -
            Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter *
              Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) := by
        rw [Dirichlet.Critical.Cylinder.TwoParameter.right_gap_identity]
      _ ≤ 2 *
          (Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right) +
            Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio denominatorParameter *
                Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right)) :=
        Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ ≤ 2 * (6 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          rightSumBound (by decide)
      _ = 12 := by ring1
      _ < 16 := by decide
      _ ≤ 32 * Dirichlet.Critical.Cylinder.TwoParameter.gap errorParameter denominatorParameter := thirtyTwoGapLower
  refine ⟨?_, ?_⟩
  · apply (Fraction.Cast.Order.natCast_lt_iff_direct).1
    exact Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      leftProductStrict (Dirichlet.Critical.Cylinder.TwoParameter.gap_pos errorCertificate denominatorCertificate)
  · apply (Fraction.Cast.Order.natCast_lt_iff_direct).1
    exact Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      rightProductStrict (Dirichlet.Critical.Cylinder.TwoParameter.gap_pos errorCertificate denominatorCertificate)

/-- Swap the coefficient directions and rotate the original right coefficient by the imaginary unit.

This operation interchanges normalized error and denominator coordinates
when their two retained parameters are interchanged.
-/
@[expose] def dualCoefficients (left right : GaussianInt) : GaussianInt × GaussianInt :=
  ((⟨0, 1⟩ : GaussianInt) * right, left)

/-- The dual normalized error is the quarter-turn of the original normalized denominator. -/
theorem normalizedError_dualCoefficients (parameter : Fraction.Rational)
    (left right : GaussianInt) :
    normalizedError parameter (dualCoefficients left right).1 (dualCoefficients left right).2 =
      (⟨0, 1⟩ : Gaussian.Basic.Canonical) * normalizedDenominator parameter left right := by
  have imaginaryEmbedding : GaussianInt.toGaussian (⟨0, 1⟩ : GaussianInt) =
      (⟨0, 1⟩ : Gaussian.Basic.Canonical) := by decide
  unfold dualCoefficients normalizedError normalizedDenominator errorRatio denominatorRatio
  rewrite [GaussianInt.toGaussian_mul, imaginaryEmbedding]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- The dual normalized denominator is the original normalized error. -/
theorem normalizedDenominator_dualCoefficients (parameter : Fraction.Rational)
    (left right : GaussianInt) :
    normalizedDenominator parameter (dualCoefficients left right).1 (dualCoefficients left right).2 =
      normalizedError parameter left right := by
  have imaginaryEmbedding : GaussianInt.toGaussian (⟨0, 1⟩ : GaussianInt) =
      (⟨0, 1⟩ : Gaussian.Basic.Canonical) := by decide
  unfold dualCoefficients normalizedError normalizedDenominator errorRatio denominatorRatio
  rewrite [GaussianInt.toGaussian_mul, imaginaryEmbedding]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- The same finite coefficient cutoff holds with the two quadrance bounds interchanged.

The dual coefficient operation reuses the original cutoff with the original
parameters interchanged. Its quarter-turn preserves coefficient quadrance.
-/
theorem coefficient_normNat_lt_thirtyTwo_of_swapped_bounds
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate : Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate : Cylinder.Basic.IsCriticalParameter denominatorParameter)
    (left right : GaussianInt)
    (errorBound : Gaussian.Norm.Basic.normSq (normalizedError errorParameter left right) ≤ 1)
    (denominatorBound :
      Gaussian.Norm.Basic.normSq (normalizedDenominator denominatorParameter left right) ≤ 5) :
    GaussianInt.normNat left < 32 ∧ GaussianInt.normNat right < 32 := by
  have dualErrorBound : Gaussian.Norm.Basic.normSq
      (normalizedError denominatorParameter (dualCoefficients left right).1
        (dualCoefficients left right).2) ≤ 5 := by
    rewrite [normalizedError_dualCoefficients, Gaussian.Norm.Basic.normSq_mul]
    have imaginaryNorm : Gaussian.Norm.Basic.normSq (⟨0, 1⟩ : Gaussian.Basic.Canonical) = 1 := by decide
    rewrite [imaginaryNorm, Fraction.Field.one_mul]
    exact denominatorBound
  have dualDenominatorBound : Gaussian.Norm.Basic.normSq
      (normalizedDenominator errorParameter (dualCoefficients left right).1
        (dualCoefficients left right).2) ≤ 1 := by
    rewrite [normalizedDenominator_dualCoefficients]
    exact errorBound
  have bounded := coefficient_normNat_lt_thirtyTwo denominatorCertificate errorCertificate
    (dualCoefficients left right).1 (dualCoefficients left right).2 dualErrorBound dualDenominatorBound
  have rotatedNorm : GaussianInt.normNat (dualCoefficients left right).1 = GaussianInt.normNat right := by
    unfold dualCoefficients
    rewrite [GaussianInt.normNat_mul]
    change 1 * GaussianInt.normNat right = GaussianInt.normNat right
    exact Nat.one_mul _
  refine ⟨bounded.2, ?_⟩
  rewrite [rotatedNorm] at bounded
  exact bounded.1

/-- Twice the real normalized error, expressed as an affine rational polynomial in the parameter. -/
private def scaledErrorReal
    (left right : GaussianInt) (value : Fraction.Rational) : Fraction.Rational :=
  2 * (left.re : Fraction.Rational) + (right.re : Fraction.Rational) -
    (right.im : Fraction.Rational) * value

/-- Twice the imaginary normalized error, expressed as an affine rational polynomial in the parameter. -/
private def scaledErrorImaginary
    (left right : GaussianInt) (value : Fraction.Rational) : Fraction.Rational :=
  2 * (left.im : Fraction.Rational) + (right.im : Fraction.Rational) +
    (right.re : Fraction.Rational) * value

/-- Twice the real normalized denominator, expressed as an affine rational polynomial in the parameter. -/
private def scaledDenominatorReal
    (left right : GaussianInt) (value : Fraction.Rational) : Fraction.Rational :=
  (left.re : Fraction.Rational) * value + (left.im : Fraction.Rational) +
    2 * (right.re : Fraction.Rational)

/-- Twice the imaginary normalized denominator, expressed as an affine rational polynomial in the parameter. -/
private def scaledDenominatorImaginary
    (left right : GaussianInt) (value : Fraction.Rational) : Fraction.Rational :=
  -(left.re : Fraction.Rational) + (left.im : Fraction.Rational) * value +
    2 * (right.im : Fraction.Rational)

/-- Twice the retained rational half is one. -/
private theorem two_mul_half : (2 : Fraction.Rational) * Dirichlet.Critical.Cylinder.TwoParameter.half = 1 := by
  unfold Dirichlet.Critical.Cylinder.TwoParameter.half
  decide

/-- Doubling the real normalized error gives its scaled affine polynomial. -/
private theorem two_mul_error_real
    (left right : GaussianInt) (value : Fraction.Rational) :
    2 * (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError value left right).re =
      Dirichlet.Critical.Cylinder.TwoParameter.scaledErrorReal left right value := by
  simp only [Dirichlet.Critical.Cylinder.TwoParameter.normalizedError,
    Dirichlet.Critical.Cylinder.TwoParameter.errorRatio,
    Gaussian.Basic.add_re,
    Gaussian.Basic.mul_re, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
  calc
    2 * ((left.re : Fraction.Rational) +
        ((right.re : Fraction.Rational) * Dirichlet.Critical.Cylinder.TwoParameter.half -
          (right.im : Fraction.Rational) * (Dirichlet.Critical.Cylinder.TwoParameter.half * value))) =
      2 * (left.re : Fraction.Rational) +
        (2 * Dirichlet.Critical.Cylinder.TwoParameter.half) * (right.re : Fraction.Rational) -
          (2 * Dirichlet.Critical.Cylinder.TwoParameter.half) * (right.im : Fraction.Rational) * value := by ring1
    _ = Dirichlet.Critical.Cylinder.TwoParameter.scaledErrorReal left right value := by
      rw [Dirichlet.Critical.Cylinder.TwoParameter.two_mul_half]
      unfold Dirichlet.Critical.Cylinder.TwoParameter.scaledErrorReal
      ring1

/-- Doubling the imaginary normalized error gives its scaled affine polynomial. -/
private theorem two_mul_error_imaginary
    (left right : GaussianInt) (value : Fraction.Rational) :
    2 * (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError value left right).im =
      Dirichlet.Critical.Cylinder.TwoParameter.scaledErrorImaginary left right value := by
  simp only [Dirichlet.Critical.Cylinder.TwoParameter.normalizedError,
    Dirichlet.Critical.Cylinder.TwoParameter.errorRatio,
    Gaussian.Basic.add_im,
    Gaussian.Basic.mul_im, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
  calc
    2 * ((left.im : Fraction.Rational) +
        ((right.re : Fraction.Rational) * (Dirichlet.Critical.Cylinder.TwoParameter.half * value) +
          (right.im : Fraction.Rational) * Dirichlet.Critical.Cylinder.TwoParameter.half)) =
      2 * (left.im : Fraction.Rational) +
        (2 * Dirichlet.Critical.Cylinder.TwoParameter.half) * (right.im : Fraction.Rational) +
          (2 * Dirichlet.Critical.Cylinder.TwoParameter.half) * (right.re : Fraction.Rational) * value := by ring1
    _ = Dirichlet.Critical.Cylinder.TwoParameter.scaledErrorImaginary left right value := by
      rw [Dirichlet.Critical.Cylinder.TwoParameter.two_mul_half]
      unfold Dirichlet.Critical.Cylinder.TwoParameter.scaledErrorImaginary
      ring1

/-- Doubling the real normalized denominator gives its scaled affine polynomial. -/
private theorem two_mul_denominator_real
    (left right : GaussianInt) (value : Fraction.Rational) :
    2 * (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator value left right).re =
      Dirichlet.Critical.Cylinder.TwoParameter.scaledDenominatorReal left right value := by
  simp only [Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator,
    Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio,
    Gaussian.Basic.add_re,
    Gaussian.Basic.mul_re, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
  calc
    2 * (((left.re : Fraction.Rational) * (Dirichlet.Critical.Cylinder.TwoParameter.half * value) -
        (left.im : Fraction.Rational) * -Dirichlet.Critical.Cylinder.TwoParameter.half) + (right.re :
          Fraction.Rational)) =
      (2 * Dirichlet.Critical.Cylinder.TwoParameter.half) * (left.re : Fraction.Rational) * value +
        (2 * Dirichlet.Critical.Cylinder.TwoParameter.half) * (left.im : Fraction.Rational) +
          2 * (right.re : Fraction.Rational) := by ring1
    _ = Dirichlet.Critical.Cylinder.TwoParameter.scaledDenominatorReal left right value := by
      rw [Dirichlet.Critical.Cylinder.TwoParameter.two_mul_half]
      unfold Dirichlet.Critical.Cylinder.TwoParameter.scaledDenominatorReal
      ring1

/-- Doubling the imaginary normalized denominator gives its scaled affine polynomial. -/
private theorem two_mul_denominator_imaginary
    (left right : GaussianInt) (value : Fraction.Rational) :
    2 * (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator value left right).im =
      Dirichlet.Critical.Cylinder.TwoParameter.scaledDenominatorImaginary left right value := by
  simp only [Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator,
    Dirichlet.Critical.Cylinder.TwoParameter.denominatorRatio,
    Gaussian.Basic.add_im,
    Gaussian.Basic.mul_im, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
  calc
    2 * (((left.re : Fraction.Rational) * -Dirichlet.Critical.Cylinder.TwoParameter.half +
        (left.im : Fraction.Rational) * (Dirichlet.Critical.Cylinder.TwoParameter.half * value)) +
          (right.im : Fraction.Rational)) =
      -(2 * Dirichlet.Critical.Cylinder.TwoParameter.half) * (left.re : Fraction.Rational) +
        (2 * Dirichlet.Critical.Cylinder.TwoParameter.half) * (left.im : Fraction.Rational) * value +
          2 * (right.im : Fraction.Rational) := by ring1
    _ = Dirichlet.Critical.Cylinder.TwoParameter.scaledDenominatorImaginary left right value := by
      rw [Dirichlet.Critical.Cylinder.TwoParameter.two_mul_half]
      unfold Dirichlet.Critical.Cylinder.TwoParameter.scaledDenominatorImaginary
      ring1

/-- Four times the excess error quadrance equals the sum of scaled coordinate squares minus four. -/
private theorem error_difference_mul_four
    (left right : GaussianInt) (value : Fraction.Rational) :
    (Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError value left right) - 1) * 4 =
      Dirichlet.Critical.Cylinder.TwoParameter.scaledErrorReal left right value ^ 2 +
        Dirichlet.Critical.Cylinder.TwoParameter.scaledErrorImaginary left right value ^ 2 - 4 := by
  unfold Data.Gaussian.Norm.Basic.normSq
  calc
    (((Dirichlet.Critical.Cylinder.TwoParameter.normalizedError value left right).re ^ 2 +
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError value left right).im ^ 2) - 1) * 4 =
      (2 * (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError value left right).re) ^ 2 +
        (2 * (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError value left right).im) ^ 2 - 4 := by ring1
    _ = Dirichlet.Critical.Cylinder.TwoParameter.scaledErrorReal left right value ^ 2 +
        Dirichlet.Critical.Cylinder.TwoParameter.scaledErrorImaginary left right value ^ 2 - 4 := by
      rw [Dirichlet.Critical.Cylinder.TwoParameter.two_mul_error_real,
        Dirichlet.Critical.Cylinder.TwoParameter.two_mul_error_imaginary]

/-- Four times the excess denominator quadrance equals the sum of scaled coordinate squares minus four. -/
private theorem denominator_difference_mul_four
    (left right : GaussianInt) (value : Fraction.Rational) :
    (Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator value left right) - 1) * 4 =
      Dirichlet.Critical.Cylinder.TwoParameter.scaledDenominatorReal left right value ^ 2 +
        Dirichlet.Critical.Cylinder.TwoParameter.scaledDenominatorImaginary left right value ^ 2 - 4 := by
  unfold Data.Gaussian.Norm.Basic.normSq
  calc
    (((Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator value left right).re ^ 2 +
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator value left right).im ^ 2) - 1) * 4 =
      (2 * (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator value left right).re) ^ 2 +
        (2 * (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator value left right).im) ^ 2 - 4 := by
      ring1
    _ = Dirichlet.Critical.Cylinder.TwoParameter.scaledDenominatorReal left right value ^ 2 +
        Dirichlet.Critical.Cylinder.TwoParameter.scaledDenominatorImaginary left right value ^ 2 - 4 := by
      rw [Dirichlet.Critical.Cylinder.TwoParameter.two_mul_denominator_real,
        Dirichlet.Critical.Cylinder.TwoParameter.two_mul_denominator_imaginary]

/-- A rational value is positive if multiplying it by four is positive. -/
private theorem positive_of_mul_four_positive {value : Fraction.Rational}
    (scaledPositive : 0 < value * 4) : 0 < value := by
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := 4)
  · calc
      (0 : Fraction.Rational) * 4 = 0 := by ring1
      _ < value * 4 := scaledPositive
  · decide

/-- The polynomial `1 + 4*t + t^2` is positive for a critical parameter. -/
private theorem templatePlus_pos
    {value : Fraction.Rational}
    (certificate : Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter value) :
    0 < 1 + 4 * value + value ^ 2 := by
  have tailNonnegative : 0 ≤ 4 * value + value ^ 2 :=
    add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Dirichlet.Critical.Cylinder.TwoParameter.parameter_nonnegative certificate))
      (Fraction.Order.Arithmetic.sq_nonneg_direct value)
  exact (show (0 : Fraction.Rational) < 1 by decide).trans_le
    (by
      calc
        (1 : Fraction.Rational) ≤ 1 + (4 * value + value ^ 2) :=
          le_add_of_nonneg_right tailNonnegative
        _ = 1 + 4 * value + value ^ 2 := by ring1)

/-- The polynomial `5 + t^2` is positive for every rational parameter. -/
private theorem templateFive_pos {value : Fraction.Rational} :
    0 < 5 + value ^ 2 :=
  (show (0 : Fraction.Rational) < 5 by decide).trans_le
    (le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.sq_nonneg_direct value))

/-- The polynomial `6 + 4*t + 2*t^2` is positive for a critical parameter. -/
private theorem templateSixPlusFour_pos
    {value : Fraction.Rational}
    (certificate : Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter value) :
    0 < 6 + 4 * value + 2 * value ^ 2 := by
  have tailNonnegative : 0 ≤ 4 * value + 2 * value ^ 2 :=
    add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Dirichlet.Critical.Cylinder.TwoParameter.parameter_nonnegative certificate))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.sq_nonneg_direct value))
  exact (show (0 : Fraction.Rational) < 6 by decide).trans_le
    (by
      calc
        (6 : Fraction.Rational) ≤ 6 + (4 * value + 2 * value ^ 2) :=
          le_add_of_nonneg_right tailNonnegative
        _ = 6 + 4 * value + 2 * value ^ 2 := by ring1)

/-- The polynomial `9 - 4*t + t^2` is positive for a critical parameter. -/
private theorem templateNineMinusFour_pos
    {value : Fraction.Rational}
    (certificate : Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter value) :
    0 < 9 - 4 * value + value ^ 2 := by
  calc
    (0 : Fraction.Rational) <
        8 + Dirichlet.Critical.Cylinder.Basic.parameterPolynomial value :=
      (show (0 : Fraction.Rational) < 8 by decide).trans_le
        (le_add_of_nonneg_right certificate.2.2.le)
    _ = 9 - 4 * value + value ^ 2 := by
      unfold Dirichlet.Critical.Cylinder.Basic.parameterPolynomial
      ring1

/-- The polynomial `14 + 2*t^2` is positive for every rational parameter. -/
private theorem templateFourteen_pos {value : Fraction.Rational} :
    0 < 14 + 2 * value ^ 2 :=
  (show (0 : Fraction.Rational) < 14 by decide).trans_le
    (le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.sq_nonneg_direct value)))

/-- The polynomial `6 - 8*t + 2*t^2` is positive for a critical parameter. -/
private theorem templateSixMinusEight_pos
    {value : Fraction.Rational}
    (certificate : Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter value) :
    0 < 6 - 8 * value + 2 * value ^ 2 := by
  have doubledNonnegative :
      0 ≤ 2 * Dirichlet.Critical.Cylinder.Basic.parameterPolynomial value :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      certificate.2.2.le
  calc
    (0 : Fraction.Rational) <
        4 + 2 * Dirichlet.Critical.Cylinder.Basic.parameterPolynomial value :=
      (show (0 : Fraction.Rational) < 4 by decide).trans_le
        (le_add_of_nonneg_right doubledNonnegative)
    _ = 6 - 8 * value + 2 * value ^ 2 := by
      unfold Dirichlet.Critical.Cylinder.Basic.parameterPolynomial
      ring1

/-- The polynomial `6 + 8*t + 2*t^2` is positive for a critical parameter. -/
private theorem templateSixPlusEight_pos
    {value : Fraction.Rational}
    (certificate : Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter value) :
    0 < 6 + 8 * value + 2 * value ^ 2 := by
  have tailNonnegative : 0 ≤ 8 * value + 2 * value ^ 2 :=
    add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Dirichlet.Critical.Cylinder.TwoParameter.parameter_nonnegative certificate))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.sq_nonneg_direct value))
  exact (show (0 : Fraction.Rational) < 6 by decide).trans_le
    (by
      calc
        (6 : Fraction.Rational) ≤ 6 + (8 * value + 2 * value ^ 2) :=
          le_add_of_nonneg_right tailNonnegative
        _ = 6 + 8 * value + 2 * value ^ 2 := by ring1)

/-- The polynomial `1 - 4*t + t^2` is positive for a critical parameter. -/
private theorem templateMinus_pos
    {value : Fraction.Rational}
    (certificate : Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter value) :
    0 < 1 - 4 * value + value ^ 2 := by
  calc
    (0 : Fraction.Rational) <
        Dirichlet.Critical.Cylinder.Basic.parameterPolynomial value :=
      certificate.2.2
    _ = 1 - 4 * value + value ^ 2 := by
      unfold Dirichlet.Critical.Cylinder.Basic.parameterPolynomial
      ring1

/-- Expand the scaled coordinate polynomials and normalize their scalar ring identities. -/
macro "scaled_ring" : tactic =>
  `(tactic| (simp only [-eq_self, -iff_self,
      Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.TwoParameter.scaledErrorReal,
      Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.TwoParameter.scaledErrorImaginary,
      Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.TwoParameter.scaledDenominatorReal,
      Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.TwoParameter.scaledDenominatorImaginary,
      Purelib.Data.GaussianInt.toGaussian, Purelib.Data.GaussianInt.Norm.Small.imaginaryUnit,
      Purelib.Data.GaussianInt.neg_re, Purelib.Data.GaussianInt.neg_im,
      Purelib.Data.GaussianInt.one_re, Purelib.Data.GaussianInt.one_im,
      Purelib.Algebra.Ring.IntCast.cast_zero, Purelib.Algebra.Ring.IntCast.neg,
      Int.cast_one, Int.cast_ofNat, ← Rat.Fraction.Cast.intCast_eq_fromInt] <;> ring1))

/-- Prove a critical-cylinder exterior from its selected positive polynomial.

The generated finite cases select this schema directly; exact ring checking verifies the coordinate identity.
-/
macro "two_parameter_error" positive:term : tactic =>
  `(tactic| first
    | left
      apply Purelib.Data.Rat.Fraction.Order.Arithmetic.lt_of_sub_pos_direct
      apply Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.TwoParameter.positive_of_mul_four_positive
      rw [Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.TwoParameter.error_difference_mul_four]
      convert ($positive) using 1 <;> scaled_ring)

/-- Prove a critical-cylinder exterior from its selected positive polynomial.

The generated finite cases select this schema directly; exact ring checking verifies the coordinate identity.
-/
macro "two_parameter_denominator" positive:term : tactic =>
  `(tactic| first
    | right
      apply Purelib.Data.Rat.Fraction.Order.Arithmetic.lt_of_sub_pos_direct
      apply Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.TwoParameter.positive_of_mul_four_positive
      rw [Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.TwoParameter.denominator_difference_mul_four]
      convert ($positive) using 1 <;> scaled_ring)

/-- The displayed left coefficient and each retained right coefficient give a strict cylinder exterior.

Both rational parameters satisfy their own critical-chamber certificate. The
four right coefficients reduce to the retained positive scalar polynomials. -/
private theorem unit_unit_strictly_exterior_row0
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {right : GaussianInt}
    (rightUnit : Purelib.Data.GaussianInt.Norm.Small.IsGaussianUnit right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter (1 : GaussianInt) right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter (1 : GaussianInt) right) :=
          by
  rcases rightUnit with rfl | rfl | rfl | rfl
  · two_parameter_denominator (templatePlus_pos denominatorCertificate)
  · two_parameter_denominator (templateMinus_pos denominatorCertificate)
  · two_parameter_error (templateMinus_pos errorCertificate)
  · two_parameter_error (templatePlus_pos errorCertificate)

/-- The displayed left coefficient and each retained right coefficient give a strict cylinder exterior.

Both rational parameters satisfy their own critical-chamber certificate. The
four right coefficients reduce to the retained positive scalar polynomials. -/
private theorem unit_unit_strictly_exterior_row1
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {right : GaussianInt}
    (rightUnit : Purelib.Data.GaussianInt.Norm.Small.IsGaussianUnit right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter (-1 : GaussianInt) right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter (-1 : GaussianInt) right)
          := by
  rcases rightUnit with rfl | rfl | rfl | rfl
  · two_parameter_denominator (templateMinus_pos denominatorCertificate)
  · two_parameter_denominator (templatePlus_pos denominatorCertificate)
  · two_parameter_error (templatePlus_pos errorCertificate)
  · two_parameter_error (templateMinus_pos errorCertificate)

/-- The displayed left coefficient and each retained right coefficient give a strict cylinder exterior.

Both rational parameters satisfy their own critical-chamber certificate. The
four right coefficients reduce to the retained positive scalar polynomials. -/
private theorem unit_unit_strictly_exterior_row2
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {right : GaussianInt}
    (rightUnit : Purelib.Data.GaussianInt.Norm.Small.IsGaussianUnit right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter
            (Purelib.Data.GaussianInt.Norm.Small.imaginaryUnit : GaussianInt) right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter
          (Purelib.Data.GaussianInt.Norm.Small.imaginaryUnit : GaussianInt) right) := by
  rcases rightUnit with rfl | rfl | rfl | rfl
  · two_parameter_error (templatePlus_pos errorCertificate)
  · two_parameter_error (templateMinus_pos errorCertificate)
  · two_parameter_denominator (templatePlus_pos denominatorCertificate)
  · two_parameter_denominator (templateMinus_pos denominatorCertificate)

/-- The displayed left coefficient and each retained right coefficient give a strict cylinder exterior.

Both rational parameters satisfy their own critical-chamber certificate. The
four right coefficients reduce to the retained positive scalar polynomials. -/
private theorem unit_unit_strictly_exterior_row3
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {right : GaussianInt}
    (rightUnit : Purelib.Data.GaussianInt.Norm.Small.IsGaussianUnit right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter
            (-Purelib.Data.GaussianInt.Norm.Small.imaginaryUnit : GaussianInt) right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter
          (-Purelib.Data.GaussianInt.Norm.Small.imaginaryUnit : GaussianInt) right) := by
  rcases rightUnit with rfl | rfl | rfl | rfl
  · two_parameter_error (templateMinus_pos errorCertificate)
  · two_parameter_error (templatePlus_pos errorCertificate)
  · two_parameter_denominator (templateMinus_pos denominatorCertificate)
  · two_parameter_denominator (templatePlus_pos denominatorCertificate)

/-- Two Gaussian unit coefficients force the normalized error or denominator quadrance strictly above one.

The independently supplied parameters lie in the critical chamber; the sixteen unit pairs reduce to positive scalar
polynomial templates. -/
private theorem unit_unit_strictly_exterior
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {left right : GaussianInt}
    (leftUnit : Purelib.Data.GaussianInt.Norm.Small.IsGaussianUnit left)
    (rightUnit : Purelib.Data.GaussianInt.Norm.Small.IsGaussianUnit right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right) := by
  rcases leftUnit with rfl | rfl | rfl | rfl
  · exact Dirichlet.Critical.Cylinder.TwoParameter.unit_unit_strictly_exterior_row0 errorCertificate
      denominatorCertificate rightUnit
  · exact Dirichlet.Critical.Cylinder.TwoParameter.unit_unit_strictly_exterior_row1 errorCertificate
      denominatorCertificate rightUnit
  · exact Dirichlet.Critical.Cylinder.TwoParameter.unit_unit_strictly_exterior_row2 errorCertificate
      denominatorCertificate rightUnit
  · exact Dirichlet.Critical.Cylinder.TwoParameter.unit_unit_strictly_exterior_row3 errorCertificate
      denominatorCertificate rightUnit

/-- The displayed left coefficient and each retained right coefficient give a strict cylinder exterior.

Both rational parameters satisfy their own critical-chamber certificate. The
four right coefficients reduce to the retained positive scalar polynomials. -/
private theorem unit_diagonal_strictly_exterior_row0
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {right : GaussianInt}
    (rightDiagonal : Purelib.Data.GaussianInt.Norm.Small.IsDiagonal right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter (1 : GaussianInt) right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter (1 : GaussianInt) right) :=
          by
  rcases rightDiagonal with rfl | rfl | rfl | rfl
  · two_parameter_denominator (templatePlus_pos denominatorCertificate)
  · two_parameter_error (templateSixPlusFour_pos errorCertificate)
  · two_parameter_denominator (templateMinus_pos denominatorCertificate)
  · two_parameter_denominator (templateNineMinusFour_pos denominatorCertificate)

/-- The displayed left coefficient and each retained right coefficient give a strict cylinder exterior.

Both rational parameters satisfy their own critical-chamber certificate. The
four right coefficients reduce to the retained positive scalar polynomials. -/
private theorem unit_diagonal_strictly_exterior_row1
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {right : GaussianInt}
    (rightDiagonal : Purelib.Data.GaussianInt.Norm.Small.IsDiagonal right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter (-1 : GaussianInt) right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter (-1 : GaussianInt) right)
          := by
  rcases rightDiagonal with rfl | rfl | rfl | rfl
  · two_parameter_denominator (templateNineMinusFour_pos denominatorCertificate)
  · two_parameter_denominator (templateMinus_pos denominatorCertificate)
  · two_parameter_error (templateSixPlusFour_pos errorCertificate)
  · two_parameter_denominator (templatePlus_pos denominatorCertificate)

/-- The displayed left coefficient and each retained right coefficient give a strict cylinder exterior.

Both rational parameters satisfy their own critical-chamber certificate. The
four right coefficients reduce to the retained positive scalar polynomials. -/
private theorem unit_diagonal_strictly_exterior_row2
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {right : GaussianInt}
    (rightDiagonal : Purelib.Data.GaussianInt.Norm.Small.IsDiagonal right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter
            (Purelib.Data.GaussianInt.Norm.Small.imaginaryUnit : GaussianInt) right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter
          (Purelib.Data.GaussianInt.Norm.Small.imaginaryUnit : GaussianInt) right) := by
  rcases rightDiagonal with rfl | rfl | rfl | rfl
  · two_parameter_error (templateSixPlusFour_pos errorCertificate)
  · two_parameter_denominator (templateNineMinusFour_pos denominatorCertificate)
  · two_parameter_denominator (templatePlus_pos denominatorCertificate)
  · two_parameter_denominator (templateMinus_pos denominatorCertificate)

/-- The displayed left coefficient and each retained right coefficient give a strict cylinder exterior.

Both rational parameters satisfy their own critical-chamber certificate. The
four right coefficients reduce to the retained positive scalar polynomials. -/
private theorem unit_diagonal_strictly_exterior_row3
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {right : GaussianInt}
    (rightDiagonal : Purelib.Data.GaussianInt.Norm.Small.IsDiagonal right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter
            (-Purelib.Data.GaussianInt.Norm.Small.imaginaryUnit : GaussianInt) right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter
          (-Purelib.Data.GaussianInt.Norm.Small.imaginaryUnit : GaussianInt) right) := by
  rcases rightDiagonal with rfl | rfl | rfl | rfl
  · two_parameter_denominator (templateMinus_pos denominatorCertificate)
  · two_parameter_denominator (templatePlus_pos denominatorCertificate)
  · two_parameter_denominator (templateNineMinusFour_pos denominatorCertificate)
  · two_parameter_error (templateSixPlusFour_pos errorCertificate)

/-- A unit left coefficient and diagonal right coefficient force a strict cylinder exterior for critical parameters. -/
private theorem unit_diagonal_strictly_exterior
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {left right : GaussianInt}
    (leftUnit : Purelib.Data.GaussianInt.Norm.Small.IsGaussianUnit left)
    (rightDiagonal : Purelib.Data.GaussianInt.Norm.Small.IsDiagonal right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right) := by
  rcases leftUnit with rfl | rfl | rfl | rfl
  · exact Dirichlet.Critical.Cylinder.TwoParameter.unit_diagonal_strictly_exterior_row0 errorCertificate
      denominatorCertificate rightDiagonal
  · exact Dirichlet.Critical.Cylinder.TwoParameter.unit_diagonal_strictly_exterior_row1 errorCertificate
      denominatorCertificate rightDiagonal
  · exact Dirichlet.Critical.Cylinder.TwoParameter.unit_diagonal_strictly_exterior_row2 errorCertificate
      denominatorCertificate rightDiagonal
  · exact Dirichlet.Critical.Cylinder.TwoParameter.unit_diagonal_strictly_exterior_row3 errorCertificate
      denominatorCertificate rightDiagonal

/-- The displayed left coefficient and each retained right coefficient give a strict cylinder exterior.

Both rational parameters satisfy their own critical-chamber certificate. The
four right coefficients reduce to the retained positive scalar polynomials. -/
private theorem diagonal_unit_strictly_exterior_row0
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {right : GaussianInt}
    (rightUnit : Purelib.Data.GaussianInt.Norm.Small.IsGaussianUnit right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter (⟨1, 1⟩ : GaussianInt) right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter (⟨1, 1⟩ : GaussianInt)
          right) := by
  rcases rightUnit with rfl | rfl | rfl | rfl
  · two_parameter_denominator (templateSixPlusFour_pos denominatorCertificate)
  · two_parameter_error (templateMinus_pos errorCertificate)
  · two_parameter_error (templateNineMinusFour_pos errorCertificate)
  · two_parameter_error (templatePlus_pos errorCertificate)

/-- The displayed left coefficient and each retained right coefficient give a strict cylinder exterior.

Both rational parameters satisfy their own critical-chamber certificate. The
four right coefficients reduce to the retained positive scalar polynomials. -/
private theorem diagonal_unit_strictly_exterior_row1
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {right : GaussianInt}
    (rightUnit : Purelib.Data.GaussianInt.Norm.Small.IsGaussianUnit right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter (⟨1, -1⟩ : GaussianInt) right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter (⟨1, -1⟩ : GaussianInt)
          right) := by
  rcases rightUnit with rfl | rfl | rfl | rfl
  · two_parameter_error (templateNineMinusFour_pos errorCertificate)
  · two_parameter_error (templatePlus_pos errorCertificate)
  · two_parameter_error (templateMinus_pos errorCertificate)
  · two_parameter_denominator (templateSixPlusFour_pos denominatorCertificate)

/-- The displayed left coefficient and each retained right coefficient give a strict cylinder exterior.

Both rational parameters satisfy their own critical-chamber certificate. The
four right coefficients reduce to the retained positive scalar polynomials. -/
private theorem diagonal_unit_strictly_exterior_row2
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {right : GaussianInt}
    (rightUnit : Purelib.Data.GaussianInt.Norm.Small.IsGaussianUnit right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter (⟨-1, 1⟩ : GaussianInt) right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter (⟨-1, 1⟩ : GaussianInt)
          right) := by
  rcases rightUnit with rfl | rfl | rfl | rfl
  · two_parameter_error (templatePlus_pos errorCertificate)
  · two_parameter_error (templateNineMinusFour_pos errorCertificate)
  · two_parameter_denominator (templateSixPlusFour_pos denominatorCertificate)
  · two_parameter_error (templateMinus_pos errorCertificate)

/-- The displayed left coefficient and each retained right coefficient give a strict cylinder exterior.

Both rational parameters satisfy their own critical-chamber certificate. The
four right coefficients reduce to the retained positive scalar polynomials. -/
private theorem diagonal_unit_strictly_exterior_row3
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {right : GaussianInt}
    (rightUnit : Purelib.Data.GaussianInt.Norm.Small.IsGaussianUnit right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter (⟨-1, -1⟩ : GaussianInt) right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter (⟨-1, -1⟩ : GaussianInt)
          right) := by
  rcases rightUnit with rfl | rfl | rfl | rfl
  · two_parameter_error (templateMinus_pos errorCertificate)
  · two_parameter_denominator (templateSixPlusFour_pos denominatorCertificate)
  · two_parameter_error (templatePlus_pos errorCertificate)
  · two_parameter_error (templateNineMinusFour_pos errorCertificate)

/-- A diagonal left coefficient and unit right coefficient force a strict cylinder exterior for critical parameters. -/
private theorem diagonal_unit_strictly_exterior
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {left right : GaussianInt}
    (leftDiagonal : Purelib.Data.GaussianInt.Norm.Small.IsDiagonal left)
    (rightUnit : Purelib.Data.GaussianInt.Norm.Small.IsGaussianUnit right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right) := by
  rcases leftDiagonal with rfl | rfl | rfl | rfl
  · exact Dirichlet.Critical.Cylinder.TwoParameter.diagonal_unit_strictly_exterior_row0 errorCertificate
      denominatorCertificate rightUnit
  · exact Dirichlet.Critical.Cylinder.TwoParameter.diagonal_unit_strictly_exterior_row1 errorCertificate
      denominatorCertificate rightUnit
  · exact Dirichlet.Critical.Cylinder.TwoParameter.diagonal_unit_strictly_exterior_row2 errorCertificate
      denominatorCertificate rightUnit
  · exact Dirichlet.Critical.Cylinder.TwoParameter.diagonal_unit_strictly_exterior_row3 errorCertificate
      denominatorCertificate rightUnit

/-- The left coefficient `(1,1)` and any diagonal right coefficient force a strict cylinder exterior for critical
parameters. -/
private theorem diagonal_diagonal_strictly_exterior_row0
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {right : GaussianInt}
    (rightDiagonal : Purelib.Data.GaussianInt.Norm.Small.IsDiagonal right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter (⟨1, 1⟩ : GaussianInt) right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter (⟨1, 1⟩ : GaussianInt)
          right) := by
  rcases rightDiagonal with rfl | rfl | rfl | rfl
  · two_parameter_error (templateFourteen_pos (value := errorParameter))
  · two_parameter_denominator (templateFourteen_pos (value := denominatorParameter))
  · two_parameter_error (templateSixMinusEight_pos errorCertificate)
  · two_parameter_denominator (templateSixMinusEight_pos denominatorCertificate)

/-- The left coefficient `(1,-1)` and any diagonal right coefficient force a strict cylinder exterior for critical
parameters. -/
private theorem diagonal_diagonal_strictly_exterior_row1
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {right : GaussianInt}
    (rightDiagonal : Purelib.Data.GaussianInt.Norm.Small.IsDiagonal right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter (⟨1, -1⟩ : GaussianInt) right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter (⟨1, -1⟩ : GaussianInt)
          right) := by
  rcases rightDiagonal with rfl | rfl | rfl | rfl
  · two_parameter_error (templateSixMinusEight_pos errorCertificate)
  · two_parameter_error (templateFourteen_pos (value := errorParameter))
  · two_parameter_denominator (templateSixMinusEight_pos denominatorCertificate)
  · two_parameter_denominator (templateFourteen_pos (value := denominatorParameter))

/-- The left coefficient `(-1,1)` and any diagonal right coefficient force a strict cylinder exterior for critical
parameters. -/
private theorem diagonal_diagonal_strictly_exterior_row2
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {right : GaussianInt}
    (rightDiagonal : Purelib.Data.GaussianInt.Norm.Small.IsDiagonal right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter (⟨-1, 1⟩ : GaussianInt) right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter (⟨-1, 1⟩ : GaussianInt)
          right) := by
  rcases rightDiagonal with rfl | rfl | rfl | rfl
  · two_parameter_denominator (templateFourteen_pos (value := denominatorParameter))
  · two_parameter_denominator (templateSixMinusEight_pos denominatorCertificate)
  · two_parameter_error (templateFourteen_pos (value := errorParameter))
  · two_parameter_error (templateSixMinusEight_pos errorCertificate)

/-- The left coefficient `(-1,-1)` and any diagonal right coefficient force a strict cylinder exterior for critical
parameters. -/
private theorem diagonal_diagonal_strictly_exterior_row3
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {right : GaussianInt}
    (rightDiagonal : Purelib.Data.GaussianInt.Norm.Small.IsDiagonal right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter (⟨-1, -1⟩ : GaussianInt) right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter (⟨-1, -1⟩ : GaussianInt)
          right) := by
  rcases rightDiagonal with rfl | rfl | rfl | rfl
  · two_parameter_denominator (templateSixMinusEight_pos denominatorCertificate)
  · two_parameter_error (templateSixMinusEight_pos errorCertificate)
  · two_parameter_denominator (templateFourteen_pos (value := denominatorParameter))
  · two_parameter_error (templateFourteen_pos (value := errorParameter))

/-- Two diagonal Gaussian coefficients force a strict cylinder exterior for critical parameters. -/
private theorem diagonal_diagonal_strictly_exterior
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    {left right : GaussianInt}
    (leftDiagonal : Purelib.Data.GaussianInt.Norm.Small.IsDiagonal left)
    (rightDiagonal : Purelib.Data.GaussianInt.Norm.Small.IsDiagonal right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right) := by
  rcases leftDiagonal with rfl | rfl | rfl | rfl
  · exact Dirichlet.Critical.Cylinder.TwoParameter.diagonal_diagonal_strictly_exterior_row0 errorCertificate
      denominatorCertificate rightDiagonal
  · exact Dirichlet.Critical.Cylinder.TwoParameter.diagonal_diagonal_strictly_exterior_row1 errorCertificate
      denominatorCertificate rightDiagonal
  · exact Dirichlet.Critical.Cylinder.TwoParameter.diagonal_diagonal_strictly_exterior_row2 errorCertificate
      denominatorCertificate rightDiagonal
  · exact Dirichlet.Critical.Cylinder.TwoParameter.diagonal_diagonal_strictly_exterior_row3 errorCertificate
      denominatorCertificate rightDiagonal

/-- Two nonzero coefficients of quadrance below four force a strict cylinder exterior.

Each coefficient is a Gaussian unit or diagonal; their finite combinations are excluded by the exact positive polynomial
templates for the two critical parameters. -/
private theorem small_nonzero_strictly_exterior
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    (left right : GaussianInt) (leftNonzero : left ≠ 0)
    (rightNonzero : right ≠ 0) (leftSmall : GaussianInt.normNat left < 4)
    (rightSmall : GaussianInt.normNat right < 4) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right) := by
  have leftShape :
      GaussianInt.Norm.Small.IsGaussianUnit left ∨
        GaussianInt.Norm.Small.IsDiagonal left := by
    rcases GaussianInt.Norm.Small.normNat_eq_zero_or_one_or_two_of_lt_four
        left leftSmall with zeroNorm | unitNorm | diagonalNorm
    · exact (leftNonzero
        (GaussianInt.Norm.Basic.eq_zero_of_normNat_eq_zero zeroNorm)).elim
    · exact Or.inl
        (GaussianInt.Norm.Small.isGaussianUnit_of_normNat_eq_one unitNorm)
    · exact Or.inr
        (GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two diagonalNorm)
  have rightShape :
      GaussianInt.Norm.Small.IsGaussianUnit right ∨
        GaussianInt.Norm.Small.IsDiagonal right := by
    rcases GaussianInt.Norm.Small.normNat_eq_zero_or_one_or_two_of_lt_four
        right rightSmall with zeroNorm | unitNorm | diagonalNorm
    · exact (rightNonzero
        (GaussianInt.Norm.Basic.eq_zero_of_normNat_eq_zero zeroNorm)).elim
    · exact Or.inl
        (GaussianInt.Norm.Small.isGaussianUnit_of_normNat_eq_one unitNorm)
    · exact Or.inr
        (GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two diagonalNorm)
  rcases leftShape with leftUnit | leftDiagonal
  · rcases rightShape with rightUnit | rightDiagonal
    · exact Dirichlet.Critical.Cylinder.TwoParameter.unit_unit_strictly_exterior errorCertificate
        denominatorCertificate leftUnit rightUnit
    · exact Dirichlet.Critical.Cylinder.TwoParameter.unit_diagonal_strictly_exterior errorCertificate
        denominatorCertificate leftUnit rightDiagonal
  · rcases rightShape with rightUnit | rightDiagonal
    · exact Dirichlet.Critical.Cylinder.TwoParameter.diagonal_unit_strictly_exterior errorCertificate
        denominatorCertificate leftDiagonal rightUnit
    · exact Dirichlet.Critical.Cylinder.TwoParameter.diagonal_diagonal_strictly_exterior errorCertificate
        denominatorCertificate leftDiagonal rightDiagonal

/-- Uniform two-parameter exterior theorem for every pair of rational
parameters in the finite critical chamber. -/
theorem strictExterior
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate :
      Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter
        denominatorParameter)
    (left right : GaussianInt) (leftNonzero : left ≠ 0)
    (rightNonzero : right ≠ 0) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right) ∨
      1 < Data.Gaussian.Norm.Basic.normSq
        (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right) := by
  by_cases errorExterior :
      (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          (Dirichlet.Critical.Cylinder.TwoParameter.normalizedError errorParameter left right)
  · exact Or.inl errorExterior
  · by_cases denominatorExterior :
        (1 : Fraction.Rational) <
          Data.Gaussian.Norm.Basic.normSq
            (Dirichlet.Critical.Cylinder.TwoParameter.normalizedDenominator denominatorParameter left right)
    · exact Or.inr denominatorExterior
    · have small := Dirichlet.Critical.Cylinder.TwoParameter.coefficient_normNat_lt_four errorCertificate
        denominatorCertificate left right (le_of_not_gt errorExterior)
        (le_of_not_gt denominatorExterior)
      exact Dirichlet.Critical.Cylinder.TwoParameter.small_nonzero_strictly_exterior errorCertificate
        denominatorCertificate left right leftNonzero rightNonzero
        small.1 small.2

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.TwoParameter

end
