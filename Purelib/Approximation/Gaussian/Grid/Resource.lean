module
import Purelib.Data.Nat.Order

public import Purelib.Approximation.Gaussian.Grid.Basic
import Purelib.Approximation.Rational.Grid.Basic
import Purelib.Approximation.Rational.Grid.Bounds
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Fraction.NaturalDenominator.Norm
public import Purelib.Data.Gaussian.Fraction.NaturalDenominator.Resource
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Resource
import Purelib.Data.Nat.BitWidth
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Resource.Clauses
public import Purelib.Data.Rat.Fraction.Resource.Width
import Purelib.Data.Rat.Rounding.Floor
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Gaussian grid arithmetic budgets

The original grid construction retains its natural bit-width and clause budgets,
coordinate products and common-denominator fraction. The quantitative claims bound these
exact retained operations.
-/

public section

namespace Purelib.Approximation.Gaussian.Grid.Resource

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Fraction
open Purelib.Data.Gaussian.Fraction.NaturalDenominator
open Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Data.Rat.Rounding
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt
open Purelib.Data

/-- A source-only natural envelope for the quadrance of the two integral coordinates in the
grid numerator. -/
@[expose] def gridNumeratorNormBudget (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) : Nat :=
  let denominator := Grid.Basic.gridDenominator radius
  Floor.ceilNat
    ((denominator : Fraction.Rational) ^ 2 *
      (2 * (Data.Gaussian.Norm.Basic.normSq center +
        2 * ((1 / 2 : Fraction.Rational) / denominator) ^ 2)))

/-- Maximum bit-width budget for the three normalized scalar results used by the grid
construction.

The source records have their directly computed `rationalRecordWidth` values. -/
@[expose] def gridArithmeticBitBudget (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) : Nat :=
  let denominator : Fraction.Rational :=
    Grid.Basic.gridDenominator radius
  max (Fraction.Resource.Width.normalizedDivBitBudget (1 / 2 : Fraction.Rational) radius)
    (max (Fraction.Resource.Width.normalizedMulBitBudget denominator center.re)
      (Fraction.Resource.Width.normalizedMulBitBudget denominator center.im))

/-- Source-only clause budget for construction of the displayed grid record. -/
@[expose] def gridArithmeticStepBudget (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) : Nat :=
  let denominator := Grid.Basic.gridDenominator radius
  Fraction.Resource.Clauses.normalizedDivStepBudget (1 / 2 : Fraction.Rational) radius +
    Fraction.Resource.Clauses.normalizedMulStepBudget (denominator : Fraction.Rational) center.re +
    Fraction.Resource.Clauses.normalizedMulStepBudget (denominator : Fraction.Rational) center.im + 5

/-- Exact accounted arithmetic clauses in the three normalized rational operations used to
construct a grid record, plus the fixed floor, rounding, cast, and assembly work. -/
@[expose] def gridArithmeticSteps (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) : Nat :=
  let denominator := Grid.Basic.gridDenominator radius
  Fraction.Resource.Clauses.divSteps
      (Fraction.Basic.ofRational (1 / 2 : Fraction.Rational))
      (Fraction.Basic.ofRational radius) +
    Fraction.Resource.Clauses.mulSteps
      (Fraction.Basic.ofRational (denominator : Fraction.Rational))
      (Fraction.Basic.ofRational center.re) +
    Fraction.Resource.Clauses.mulSteps
      (Fraction.Basic.ofRational (denominator : Fraction.Rational))
      (Fraction.Basic.ofRational center.im) + 5

/-- The exact counted grid-construction arithmetic clauses fit the budget computed from the
original inputs. -/
theorem gridArithmeticSteps_le_budget (center : Data.Gaussian.Basic.Canonical)
    (radius : Fraction.Rational) :
    gridArithmeticSteps center radius ≤
      gridArithmeticStepBudget center radius := by
  unfold gridArithmeticSteps gridArithmeticStepBudget
  exact Nat.add_le_add_right
    (Nat.add_le_add
      (Nat.add_le_add
        (Fraction.Resource.Clauses.normalizedDiv_steps_le_budget (1 / 2 : Fraction.Rational) radius)
        (Fraction.Resource.Clauses.normalizedMul_steps_le_budget
          (Grid.Basic.gridDenominator radius : Fraction.Rational)
          center.re))
      (Fraction.Resource.Clauses.normalizedMul_steps_le_budget
        (Grid.Basic.gridDenominator radius : Fraction.Rational)
        center.im)) 5

/-- The normalized half-over-radius division fits the original grid arithmetic bit-width
budget. -/
theorem gridDivision_width_le_budget (center : Data.Gaussian.Basic.Canonical)
    (radius : Fraction.Rational) :
    Fraction.Resource.Width.rationalRecordWidth (Fraction.Arithmetic.normalizedDiv
        (1 / 2 : Fraction.Rational) radius) ≤
      gridArithmeticBitBudget center radius :=
  (Fraction.Resource.Width.normalizedDiv_width_le_budget (1 / 2 : Fraction.Rational) radius).trans
    (Nat.Order.le_max_left _ _)

/-- The nearest square-grid point has an explicit squared displacement bound. -/
theorem gridFraction_offset_normSq_le (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) :
    Data.Gaussian.Norm.Basic.normSq
        ((Gaussian.Grid.Basic.gridFraction center radius).value - center) ≤
      2 * ((1 / 2 : Fraction.Rational) /
        Grid.Basic.gridDenominator radius) ^ 2 := by
  have realBound := Grid.Bounds.gridCoordinate_offset_sq_le center.re
    (Grid.Basic.gridDenominator_pos radius)
  have imaginaryBound := Grid.Bounds.gridCoordinate_offset_sq_le center.im
    (Grid.Basic.gridDenominator_pos radius)
  simp only [Data.Gaussian.Norm.Basic.normSq,
    Basic.sub_re,
    Basic.sub_im,
    Gaussian.Grid.Basic.gridFraction_value_re,
    Gaussian.Grid.Basic.gridFraction_value_im]
  calc
    _ ≤
        ((1 / 2 : Fraction.Rational) /
            Grid.Basic.gridDenominator radius) ^ 2 +
          ((1 / 2 : Fraction.Rational) /
            Grid.Basic.gridDenominator radius) ^ 2 :=
      add_le_add realBound imaginaryBound
    _ = 2 * ((1 / 2 : Fraction.Rational) /
        Grid.Basic.gridDenominator radius) ^ 2 := by ring1

/-- The rounded grid value has an explicit squared-norm bound from its original centre and
denominator displacement. -/
theorem gridFraction_value_normSq_le (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) :
    Data.Gaussian.Norm.Basic.normSq (Gaussian.Grid.Basic.gridFraction center radius).value ≤
      2 * (Data.Gaussian.Norm.Basic.normSq center +
        2 * ((1 / 2 : Fraction.Rational) /
          Grid.Basic.gridDenominator radius) ^ 2) :=
  Norm.Bounds.value_normSq_le_of_offset (gridFraction_offset_normSq_le center radius)

/-- The original grid fraction's Gaussian-integer numerator norm fits its computed natural
budget. -/
theorem gridFraction_numerator_norm_le_budget
    (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) :
    normNat (Gaussian.Grid.Basic.gridFraction center radius).numerator ≤
      gridNumeratorNormBudget center radius := by
  let denominator := Grid.Basic.gridDenominator radius
  let bound : Fraction.Rational :=
    (denominator : Fraction.Rational) ^ 2 *
      (2 * (Data.Gaussian.Norm.Basic.normSq center +
        2 * ((1 / 2 : Fraction.Rational) / denominator) ^ 2))
  have denominatorNonnegative : (0 : Fraction.Rational) ≤
      (denominator : Fraction.Rational) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  have boundNonnegative : (0 : Fraction.Rational) ≤ bound := by
    exact Fraction.Order.Arithmetic.mul_nonneg_direct denominatorNonnegative
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg (Norm.Basic.normSq_nonneg _)
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (Fraction.Order.Arithmetic.sq_nonneg_direct _))))
  apply (Fraction.Cast.Order.natCast_le_iff_direct).1
  rw [NaturalDenominator.Norm.commonFraction_numerator_norm_identity]
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (gridFraction_value_normSq_le center radius) denominatorNonnegative
  calc
    (Gaussian.Grid.Basic.gridFraction center radius).denominator ^ 2 *
          Data.Gaussian.Norm.Basic.normSq (Gaussian.Grid.Basic.gridFraction center radius).value =
        (denominator : Fraction.Rational) ^ 2 *
          Data.Gaussian.Norm.Basic.normSq (Gaussian.Grid.Basic.gridFraction center radius).value := by
      rfl
    _ ≤ bound := scaled
    _ ≤ (gridNumeratorNormBudget center radius : Fraction.Rational) := by
      dsimp only [gridNumeratorNormBudget, denominator] at boundNonnegative ⊢
      exact Floor.le_natCast_ceilNat_of_nonneg
        boundNonnegative

/-- The normalized denominator times imaginary-coordinate product fits the original grid
arithmetic bit-width budget. -/
theorem gridImaginaryProduct_width_le_budget (center : Data.Gaussian.Basic.Canonical)
    (radius : Fraction.Rational) :
    Fraction.Resource.Width.rationalRecordWidth (Fraction.Arithmetic.normalizedMul
        (Grid.Basic.gridDenominator radius : Fraction.Rational)
        center.im) ≤ gridArithmeticBitBudget center radius :=
  (Fraction.Resource.Width.normalizedMul_width_le_budget _ center.im).trans
    ((Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _ _))

/-- The normalized denominator times real-coordinate product fits the original grid
arithmetic bit-width budget. -/
theorem gridRealProduct_width_le_budget (center : Data.Gaussian.Basic.Canonical)
    (radius : Fraction.Rational) :
    Fraction.Resource.Width.rationalRecordWidth (Fraction.Arithmetic.normalizedMul
        (Grid.Basic.gridDenominator radius : Fraction.Rational)
        center.re) ≤ gridArithmeticBitBudget center radius :=
  (Fraction.Resource.Width.normalizedMul_width_le_budget _ center.re).trans
    ((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _ _))

/-- Maximum component width of the returned grid numerator and denominator. -/
@[expose] def gridRecordBitBudget (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) : Nat :=
  max (BitWidth.natWidth (gridNumeratorNormBudget center radius))
    (BitWidth.natWidth (Grid.Basic.gridDenominator radius))

/-- The original grid fraction's numerator and denominator component widths fit the computed
record bit-width budget. -/
theorem gridFraction_width_le_budget (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) :
    Resource.commonFractionWidth (Gaussian.Grid.Basic.gridFraction center radius) ≤
      gridRecordBitBudget center radius := by
  apply Nat.Order.max_le
  · exact (Resource.gaussianIntWidth_le_budget
      (gridFraction_numerator_norm_le_budget center radius)).trans
      (Nat.Order.le_max_left _ _)
  · exact Nat.Order.le_max_right _ _

end Purelib.Approximation.Gaussian.Grid.Resource
