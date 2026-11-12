module

meta import Lean.Elab.Tactic.RCases
public import Purelib.Curves.Legendre.Periods.Jets.Connection
public import Purelib.Curves.Legendre.PicardFuchs.Clearance.Increment
public import Purelib.LinearAlgebra.Gaussian.Norm
public import Purelib.Data.Gaussian.Field
import Purelib.Curves.Legendre.PicardFuchs.Connection
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Fin.Two
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Reciprocal
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # The original two-row Legendre connection coefficient matrix

The entries come from the original symbolic reductions in the ordered
basis `dx/y`, `x dx/y`, divided by the same exact connection denominator.
The original parameter clearance supplies one rational coefficient bound
throughout its admitted increment ball. No period output defines an entry.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Connection

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ)
open Purelib.Algebra.FiniteSum.Fin.Rational (sumFin_two_constant)
open Purelib.Algebra.FiniteSum.Rational.Order.IndexedBudget (sumFin_le)
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Bounds
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order.Arithmetic
open Purelib.LinearAlgebra renaming Matrix → Mat
open Purelib.LinearAlgebra.Gaussian
open Purelib.LinearAlgebra.Matrix (matrixOfFn matrixOfFn_apply)
open Purelib.LinearAlgebra.Matrix.Multiplication (matrixVector matrixVector_apply)

/-- Materialize the original connection reductions in their two differential coordinates.

Row zero is the derivative of `dx/y`; row one is the derivative of
`x dx/y`. Columns retain that same basis order. Each numerator is an
actual coefficient of the original row reduction, with denominator
`2 * parameter * (1 - parameter)` in all four entries.
-/
def matrix (parameter : Canonical) : Mat Canonical 2 :=
  matrixOfFn fun row column =>
    (if column = 0 then (connectionReduction parameter row).basisConstant
      else (connectionReduction parameter row).basisLinear) /
        ParameterClearance.connectionDenominator parameter

/-- Read one actual matrix entry through its original retained connection reduction. -/
theorem matrix_apply (parameter : Canonical) (row column : Fin 2) :
    matrix parameter row column =
      (if column = 0 then (connectionReduction parameter row).basisConstant
        else (connectionReduction parameter row).basisLinear) /
          ParameterClearance.connectionDenominator parameter := by
  unfold matrix
  exact matrixOfFn_apply _ row column

/-- Multiplication by the original nonzero denominator recovers the original basis action.

The two coefficients are the original row's stored constant and linear
coefficients. This identity keeps the actual structural input vector and
matrix-vector multiplication, rather than defining an action from period
samples or a desired transport result.
-/
theorem matrixVector_cleared {parameter : Canonical}
    (clearance : ParameterClearance parameter) (values : Data.Vector Canonical 2) (row : Fin 2) :
    ParameterClearance.connectionDenominator parameter * matrixVector (matrix parameter) values row =
      (connectionReduction parameter row).basisConstant * values 0 +
        (connectionReduction parameter row).basisLinear * values 1 := by
  rewrite [matrixVector_apply, sumFin_succ, sumFin_succ]
  change ParameterClearance.connectionDenominator parameter *
    (matrix parameter row 0 * values 0 + (matrix parameter row 1 * values 1 + 0)) = _
  rewrite [matrix_apply, matrix_apply, if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  have first := Algebra.Field.ExplicitField.div_mul_cancel
    (connectionReduction parameter row).basisConstant clearance.connectionDenominator_ne_zero
  have last := Algebra.Field.ExplicitField.div_mul_cancel
    (connectionReduction parameter row).basisLinear clearance.connectionDenominator_ne_zero
  calc
    _ = ((connectionReduction parameter row).basisConstant /
          ParameterClearance.connectionDenominator parameter *
            ParameterClearance.connectionDenominator parameter) * values 0 +
        ((connectionReduction parameter row).basisLinear /
          ParameterClearance.connectionDenominator parameter *
            ParameterClearance.connectionDenominator parameter) * values 1 := by ring1
    _ = _ := by rewrite [first, last]; rfl

/-- Compute one positive common squared-denominator floor on the original admitted increment ball.

Both original singular-value floors are quartered by the existing shifted
clearance construction. Their original connection product is retained
literally; equivalently this is the original connection floor divided by
sixteen.
-/
def denominatorFloor {parameter : Canonical} (clearance : ParameterClearance parameter) : Rational :=
  4 * (clearance.zeroBound / 4) * (clearance.oneBound / 4)

/-- The common denominator floor is positive from the two original parameter floors. -/
theorem denominatorFloor_positive {parameter : Canonical} (clearance : ParameterClearance parameter) :
    0 < denominatorFloor clearance :=
  mul_pos_direct (mul_pos_direct (by decide) (Quarter.quarter_pos clearance.zeroPositive))
    (Quarter.quarter_pos clearance.onePositive)

/-- Every admitted increment has the same positive denominator floor, derived from its actual shifted clearance. -/
theorem denominatorFloor_le {parameter : Canonical} (clearance : ParameterClearance parameter)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ clearance.incrementBound) :
    denominatorFloor clearance ≤
      Norm.Basic.normSq (ParameterClearance.connectionDenominator (parameter + increment)) := by
  have retained := (clearance.shifted increment admitted).connectionLowerSq_le_normSq
  have same : (clearance.shifted increment admitted).connectionLowerSq = denominatorFloor clearance := by
    unfold ParameterClearance.connectionLowerSq denominatorFloor
    rewrite [clearance.shifted_zeroBound increment admitted, clearance.shifted_oneBound increment admitted]
    rfl
  exact same.symm.trans_le retained

/-- Compute a fixed upper bound for parameter quadrance on the original admitted increment ball. -/
def parameterCeiling {parameter : Canonical} (clearance : ParameterClearance parameter) : Rational :=
  2 * (Norm.Basic.normSq parameter + clearance.incrementBound)

/-- The parameter quadrance ceiling is nonnegative without a lower bound on the actual increment. -/
theorem parameterCeiling_nonnegative {parameter : Canonical} (clearance : ParameterClearance parameter) :
    0 ≤ parameterCeiling clearance :=
  mul_nonneg_direct (by decide)
    (add_pos_of_nonneg_of_pos_direct (Norm.Basic.normSq_nonneg parameter)
      clearance.incrementBound_positive).le

/-- Every admitted actual parameter quadrance is bounded by the same fixed ceiling. -/
theorem parameter_normSq_le {parameter : Canonical} (clearance : ParameterClearance parameter)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ clearance.incrementBound) :
    Norm.Basic.normSq (parameter + increment) ≤ parameterCeiling clearance :=
  (Norm.Bounds.normSq_add_le_two parameter increment).trans
    (mul_le_mul_of_nonneg_left_direct
      (add_le_add_direct (Fraction.Order.Basic.le_refl _) admitted) (by decide))

/-- Compute a fixed rational squared-norm ceiling for all four actual connection coefficients.

The same original parameter ceiling bounds both constant coefficients and
the parameter-dependent linear coefficient; adding one also pays the
remaining linear coefficient. The four entries share the same original
positive denominator floor. No query stage or increment is an input.
-/
def matrixCeiling {parameter : Canonical} (clearance : ParameterClearance parameter) : Rational :=
  4 * ((parameterCeiling clearance + 1) * (denominatorFloor clearance)⁻¹)

/-- The fixed matrix coefficient ceiling is nonnegative. -/
theorem matrixCeiling_nonnegative {parameter : Canonical} (clearance : ParameterClearance parameter) :
    0 ≤ matrixCeiling clearance :=
  mul_nonneg_direct (by decide)
    (mul_nonneg_direct
      (add_pos_of_nonneg_of_pos_direct (parameterCeiling_nonnegative clearance)
        (by decide : (0 : Rational) < 1)).le
      (Fraction.Order.Field.inv_pos_direct (denominatorFloor_positive clearance)).le)

/-- Each original row numerator is paid by an upper bound on its actual parameter quadrance. -/
private theorem numerator_normSq_le_of_bound (parameter : Canonical) (ceiling : Rational)
    (bounded : Norm.Basic.normSq parameter ≤ ceiling) (row column : Fin 2) :
    Norm.Basic.normSq
      (if column = 0 then (connectionReduction parameter row).basisConstant
        else (connectionReduction parameter row).basisLinear) ≤ ceiling + 1 := by
  have parameterBound : Norm.Basic.normSq parameter ≤ ceiling + 1 :=
    bounded.trans (by
      calc
        ceiling = ceiling + 0 := by ring1
        _ ≤ ceiling + 1 :=
          add_le_add_direct (Fraction.Order.Basic.le_refl _) (by decide))
  have oneBound : (1 : Rational) ≤ ceiling + 1 := by
    calc
      (1 : Rational) = 0 + 1 := by ring1
      _ ≤ ceiling + 1 :=
        add_le_add_direct ((Norm.Basic.normSq_nonneg parameter).trans bounded) (Fraction.Order.Basic.le_refl _)
  rcases Data.Fin.Two.finTwo_cases column with equal | equal
  · subst column
    rewrite [if_pos rfl]
    rcases Data.Fin.Two.finTwo_cases row with equal | equal
    · subst row
      rewrite [connectionReduction_zero]
      exact parameterBound
    · subst row
      rewrite [connectionReduction_one]
      exact parameterBound
  · subst column
    rewrite [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    rcases Data.Fin.Two.finTwo_cases row with equal | equal
    · subst row
      rewrite [connectionReduction_zero]
      change Norm.Basic.normSq (-1 : Canonical) ≤ _
      rewrite [Norm.Basic.normSq_neg, Norm.Basic.normSq_one]
      exact oneBound
    · subst row
      rewrite [connectionReduction_one]
      change Norm.Basic.normSq (-parameter) ≤ _
      rewrite [Norm.Basic.normSq_neg]
      exact parameterBound

/-- Each original row numerator is paid by the same fixed parameter ceiling plus one. -/
private theorem numerator_normSq_le {parameter : Canonical} (clearance : ParameterClearance parameter)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ clearance.incrementBound)
    (row column : Fin 2) :
    Norm.Basic.normSq
      (if column = 0 then (connectionReduction (parameter + increment) row).basisConstant
        else (connectionReduction (parameter + increment) row).basisLinear) ≤
      parameterCeiling clearance + 1 :=
  numerator_normSq_le_of_bound (parameter + increment) (parameterCeiling clearance)
    (parameter_normSq_le clearance increment admitted) row column

/-- Actual parameter clearance and a quadrance ceiling bound each original connection entry.

The positive denominator floor is the retained product of the two actual
singular-value clearances. Both bounds concern this same parameter; no
increment-ball or connection-sample comparison is required.
-/
theorem matrix_entry_le_of_clearance {parameter : Canonical} (clearance : ParameterClearance parameter)
    (ceiling : Rational) (bounded : Norm.Basic.normSq parameter ≤ ceiling) (row column : Fin 2) :
    Norm.Basic.normSq (matrix parameter row column) ≤
      (ceiling + 1) * clearance.connectionLowerSq⁻¹ := by
  have numerator := numerator_normSq_le_of_bound parameter ceiling bounded row column
  have reciprocal := Norm.Reciprocal.normSq_le
    (source := ParameterClearance.connectionDenominator parameter)
    clearance.connectionLowerSq_positive clearance.connectionLowerSq_le_normSq
  rewrite [Field.inv_eq, Field.normSq_inv _ clearance.connectionDenominator_ne_zero] at reciprocal
  rewrite [matrix_apply, Field.normSq_div _ _ clearance.connectionDenominator_ne_zero]
  exact mul_le_mul_direct numerator reciprocal
    (Fraction.Order.Field.inv_pos_direct
      (clearance.connectionLowerSq_positive.trans_le clearance.connectionLowerSq_le_normSq)).le
    ((Norm.Basic.normSq_nonneg _).trans numerator)

/-- The same retained point clearances and parameter ceiling bound the complete original connection matrix. -/
theorem matrix_le_of_clearance {parameter : Canonical} (clearance : ParameterClearance parameter)
    (ceiling : Rational) (bounded : Norm.Basic.normSq parameter ≤ ceiling) :
    Norm.matrix (matrix parameter) ≤ 4 * ((ceiling + 1) * clearance.connectionLowerSq⁻¹) := by
  let entryBound := (ceiling + 1) * clearance.connectionLowerSq⁻¹
  have rows (row : Fin 2) : Norm.vector (matrix parameter row) ≤ 2 * entryBound :=
    (sumFin_le (fun column => matrix_entry_le_of_clearance clearance ceiling bounded row column)).trans_eq
      (sumFin_two_constant entryBound)
  have total := (sumFin_le rows).trans_eq (sumFin_two_constant (2 * entryBound))
  exact total.trans_eq (by dsimp only [entryBound]; ring1)

/-- Every actual matrix entry obeys the same coefficient budget throughout the original admitted ball. -/
theorem matrix_entry_le {parameter : Canonical} (clearance : ParameterClearance parameter)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ clearance.incrementBound)
    (row column : Fin 2) :
    Norm.Basic.normSq (matrix (parameter + increment) row column) ≤
      (parameterCeiling clearance + 1) * (denominatorFloor clearance)⁻¹ := by
  have numerator := numerator_normSq_le clearance increment admitted row column
  have reciprocal := Norm.Reciprocal.normSq_le
    (source := ParameterClearance.connectionDenominator (parameter + increment))
    (denominatorFloor_positive clearance) (denominatorFloor_le clearance increment admitted)
  rewrite [Field.inv_eq, Field.normSq_inv _
    (clearance.shifted increment admitted).connectionDenominator_ne_zero] at reciprocal
  rewrite [matrix_apply, Field.normSq_div _ _
    (clearance.shifted increment admitted).connectionDenominator_ne_zero]
  exact mul_le_mul_direct numerator reciprocal
    (Fraction.Order.Field.inv_pos_direct
      ((denominatorFloor_positive clearance).trans_le (denominatorFloor_le clearance increment admitted))).le
    ((Norm.Basic.normSq_nonneg _).trans numerator)

/-- The whole actual matrix has the fixed original-clearance squared-norm ceiling at every admitted increment. -/
theorem matrix_le {parameter : Canonical} (clearance : ParameterClearance parameter)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ clearance.incrementBound) :
    Norm.matrix (matrix (parameter + increment)) ≤ matrixCeiling clearance := by
  let entryBound := (parameterCeiling clearance + 1) * (denominatorFloor clearance)⁻¹
  have rows (row : Fin 2) : Norm.vector (matrix (parameter + increment) row) ≤ 2 * entryBound :=
    (sumFin_le (fun column => matrix_entry_le clearance increment admitted row column)).trans_eq
      (sumFin_two_constant entryBound)
  have total := (sumFin_le rows).trans_eq (sumFin_two_constant (2 * entryBound))
  exact total.trans_eq (by unfold matrixCeiling; dsimp only [entryBound]; ring1)

/-- The original matrix-vector action is uniformly bounded on the same original increment ball. -/
theorem matrixVector_le {parameter : Canonical} (clearance : ParameterClearance parameter)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ clearance.incrementBound)
    (values : Data.Vector Canonical 2) :
    Norm.vector (matrixVector (matrix (parameter + increment)) values) ≤
      2 * matrixCeiling clearance * Norm.vector values := by
  have coefficients := mul_le_mul_of_nonneg_left_direct (matrix_le clearance increment admitted)
    (by decide : (0 : Rational) ≤ 2)
  exact (Norm.matrixVector_le (matrix (parameter + increment)) values).trans
    (mul_le_mul_of_nonneg_right_direct coefficients (Norm.vector_nonnegative values))

end Purelib.Curves.Legendre.Periods.Jets.Connection

end
