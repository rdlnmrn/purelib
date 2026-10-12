module
import Purelib.Algebra.Semiring.Normalization
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Geometry.Rational.Box.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Bounds.Square

public section

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

namespace Purelib.Geometry.Rational.Box

/-- The squared real-coordinate difference of two box members is bounded by the squared diagonal. -/
theorem real_sub_sq_le_diagonalSq
    {current : Rational.Box} {left right : Data.Gaussian.Basic.Canonical}
    (leftInside : current.Contains left)
    (rightInside : current.Contains right) :
    (left.re - right.re) ^ 2 ≤ current.diagonalSq := by
  have distance := current.normSq_sub_le_diagonalSq leftInside rightInside
  have imaginaryNonnegative :
      0 ≤ (left.im - right.im) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  calc
    (left.re - right.re) ^ 2 =
        (left.re - right.re) ^ 2 + 0 := by ring1
    _ ≤ (left.re - right.re) ^ 2 +
        (left.im - right.im) ^ 2 :=
      add_le_add le_rfl imaginaryNonnegative
    _ = Data.Gaussian.Norm.Basic.normSq (left - right) := by
      simp only [Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
        -eq_self, -iff_self]
      rfl
    _ ≤ current.diagonalSq := distance

/-- The squared imaginary-coordinate difference of two box members is bounded by the squared diagonal. -/
theorem imag_sub_sq_le_diagonalSq
    {current : Rational.Box} {left right : Data.Gaussian.Basic.Canonical}
    (leftInside : current.Contains left)
    (rightInside : current.Contains right) :
    (left.im - right.im) ^ 2 ≤ current.diagonalSq := by
  have distance := current.normSq_sub_le_diagonalSq leftInside rightInside
  have realNonnegative :
      0 ≤ (left.re - right.re) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  calc
    (left.im - right.im) ^ 2 =
        0 + (left.im - right.im) ^ 2 := by ring1
    _ ≤ (left.re - right.re) ^ 2 +
        (left.im - right.im) ^ 2 :=
      add_le_add realNonnegative le_rfl
    _ = Data.Gaussian.Norm.Basic.normSq (left - right) := by
      simp only [Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
        -eq_self, -iff_self]
      rfl
    _ ≤ current.diagonalSq := distance

/-- The squared sum of two real coordinates is at most four times the enclosing endpoint-square bound. -/
private theorem real_add_sq_le_coordinateSqBound
    {bounding current : Rational.Box} {left right : Data.Gaussian.Basic.Canonical}
    (refines : current.Refines bounding)
    (leftInside : current.Contains left)
    (rightInside : current.Contains right) :
    (left.re + right.re) ^ 2 ≤ 4 * bounding.coordinateSqBound := by
  have leftBounding := refines.contains leftInside
  have rightBounding := refines.contains rightInside
  have leftSquare : left.re ^ 2 ≤ bounding.coordinateSqBound :=
    (Rational.Box.sq_le_endpoint_max
      leftBounding.1 leftBounding.2.1).trans
      (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _ _)
  have rightSquare : right.re ^ 2 ≤ bounding.coordinateSqBound :=
    (Rational.Box.sq_le_endpoint_max
      rightBounding.1 rightBounding.2.1).trans
      (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _ _)
  have sumSquares :
      left.re ^ 2 + right.re ^ 2 ≤
        bounding.coordinateSqBound + bounding.coordinateSqBound :=
    add_le_add leftSquare rightSquare
  have twoNonnegative : (0 : Fraction.Rational) ≤ 2 := by decide
  calc
    (left.re + right.re) ^ 2 ≤
        2 * (left.re ^ 2 + right.re ^ 2) :=
      Purelib.Data.Rat.Bounds.Square.add_sq_le_two _ _
    _ ≤ 2 * (bounding.coordinateSqBound +
        bounding.coordinateSqBound) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        sumSquares twoNonnegative
    _ = 4 * bounding.coordinateSqBound := by ring1

/-- The squared sum of two imaginary coordinates is at most four times the enclosing endpoint-square bound. -/
private theorem imag_add_sq_le_coordinateSqBound
    {bounding current : Rational.Box} {left right : Data.Gaussian.Basic.Canonical}
    (refines : current.Refines bounding)
    (leftInside : current.Contains left)
    (rightInside : current.Contains right) :
    (left.im + right.im) ^ 2 ≤ 4 * bounding.coordinateSqBound := by
  have leftBounding := refines.contains leftInside
  have rightBounding := refines.contains rightInside
  have leftSquare : left.im ^ 2 ≤ bounding.coordinateSqBound :=
    (Rational.Box.sq_le_endpoint_max
      leftBounding.2.2.1 leftBounding.2.2.2).trans
      (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _)
  have rightSquare : right.im ^ 2 ≤ bounding.coordinateSqBound :=
    (Rational.Box.sq_le_endpoint_max
      rightBounding.2.2.1 rightBounding.2.2.2).trans
      (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _)
  have sumSquares :
      left.im ^ 2 + right.im ^ 2 ≤
        bounding.coordinateSqBound + bounding.coordinateSqBound :=
    add_le_add leftSquare rightSquare
  have twoNonnegative : (0 : Fraction.Rational) ≤ 2 := by decide
  calc
    (left.im + right.im) ^ 2 ≤
        2 * (left.im ^ 2 + right.im ^ 2) :=
      Purelib.Data.Rat.Bounds.Square.add_sq_le_two _ _
    _ ≤ 2 * (bounding.coordinateSqBound +
        bounding.coordinateSqBound) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        sumSquares twoNonnegative
    _ = 4 * bounding.coordinateSqBound := by ring1

/-- Squared variation of Gaussian quadrance is bounded by sixteen times the enclosing coordinate bound and the current
squared diagonal.

Both points belong to the same current box, which retains its coordinatewise refinement of the bounding box. -/
theorem normSq_sub_sq_le
    {bounding current : Rational.Box} {left right : Data.Gaussian.Basic.Canonical}
    (refines : current.Refines bounding)
    (leftInside : current.Contains left)
    (rightInside : current.Contains right) :
    (Data.Gaussian.Norm.Basic.normSq left - Data.Gaussian.Norm.Basic.normSq right) ^ 2 ≤
      16 * bounding.coordinateSqBound * current.diagonalSq := by
  have realDifference := real_sub_sq_le_diagonalSq leftInside rightInside
  have imaginaryDifference := imag_sub_sq_le_diagonalSq leftInside rightInside
  have realSum := real_add_sq_le_coordinateSqBound refines
    leftInside rightInside
  have imaginarySum := imag_add_sq_le_coordinateSqBound refines
    leftInside rightInside
  have realProduct :
      ((left.re - right.re) * (left.re + right.re)) ^ 2 ≤
        current.diagonalSq * (4 * bounding.coordinateSqBound) := by
    rw [Purelib.Algebra.Semiring.Normalization.product_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct
      realDifference realSum
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      current.diagonalSq_nonneg
  have imaginaryProduct :
      ((left.im - right.im) * (left.im + right.im)) ^ 2 ≤
        current.diagonalSq * (4 * bounding.coordinateSqBound) := by
    rw [Purelib.Algebra.Semiring.Normalization.product_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct
      imaginaryDifference imaginarySum
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      current.diagonalSq_nonneg
  have productSum :
      ((left.re - right.re) * (left.re + right.re)) ^ 2 +
          ((left.im - right.im) * (left.im + right.im)) ^ 2 ≤
        current.diagonalSq * (4 * bounding.coordinateSqBound) +
          current.diagonalSq * (4 * bounding.coordinateSqBound) :=
    add_le_add realProduct imaginaryProduct
  have twoNonnegative : (0 : Fraction.Rational) ≤ 2 := by decide
  calc
    (Data.Gaussian.Norm.Basic.normSq left - Data.Gaussian.Norm.Basic.normSq right) ^ 2 =
        ((left.re - right.re) * (left.re + right.re) +
          (left.im - right.im) * (left.im + right.im)) ^ 2 := by
      simp only [Data.Gaussian.Norm.Basic.normSq, -eq_self, -iff_self]
      ring1
    _ ≤ 2 *
        (((left.re - right.re) * (left.re + right.re)) ^ 2 +
          ((left.im - right.im) * (left.im + right.im)) ^ 2) :=
      Purelib.Data.Rat.Bounds.Square.add_sq_le_two _ _
    _ ≤ 2 *
        (current.diagonalSq * (4 * bounding.coordinateSqBound) +
          current.diagonalSq * (4 * bounding.coordinateSqBound)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        productSum twoNonnegative
    _ = 16 * bounding.coordinateSqBound * current.diagonalSq := by
      ring1

end Purelib.Geometry.Rational.Box

end
