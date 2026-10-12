module
import Purelib.Algebra.Semiring.Normalization
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Variation
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.Ring

public section

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

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

namespace Purelib.Geometry.Projective.Hermitian.Box

/-- The fixed coefficient multiplying the current squared diagonal in the Hermitian variation estimate. -/
@[expose] def variationCoefficient (form : Hermitian.HermitianForm)
  (bounding : Rational.Box) : Fraction.Rational :=
  3 * (16 * form.radial ^ 2 * bounding.coordinateSqBound +
    form.realLinear ^ 2 + form.imagLinear ^ 2)

/-- Squared variation margin for a current box inside `bounding`. -/
@[expose] def variationSqBound
    (form : Hermitian.HermitianForm) (bounding current : Rational.Box) : Fraction.Rational :=
  variationCoefficient form bounding * current.diagonalSq

/-- The Hermitian variation coefficient on a rational bounding box is nonnegative. -/
theorem variationCoefficient_nonneg (form : Hermitian.HermitianForm)
  (bounding : Rational.Box) :
    0 ≤ variationCoefficient form bounding := by
  have sixteenNonnegative : (0 : Fraction.Rational) ≤ 16 := by decide
  have threeNonnegative : (0 : Fraction.Rational) ≤ 3 := by decide
  have radialSquare :=
    Fraction.Order.Arithmetic.sq_nonneg_direct form.radial
  have radialCoordinateNonnegative :
      0 ≤ 16 * form.radial ^ 2 * bounding.coordinateSqBound :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct sixteenNonnegative
        radialSquare)
      bounding.coordinateSqBound_nonneg
  exact Fraction.Order.Arithmetic.mul_nonneg_direct threeNonnegative
    (add_nonneg
      (add_nonneg radialCoordinateNonnegative
        (Fraction.Order.Arithmetic.sq_nonneg_direct form.realLinear))
      (Fraction.Order.Arithmetic.sq_nonneg_direct form.imagLinear))

/-- The computed squared variation bound is nonnegative. -/
theorem variationSqBound_nonneg
    (form : Hermitian.HermitianForm) (bounding current : Rational.Box) :
    0 ≤ variationSqBound form bounding current :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (variationCoefficient_nonneg form bounding) current.diagonalSq_nonneg

/-- The squared change in a Hermitian form between any two points of the current box is bounded by a displayed rational
multiple of its squared diagonal. -/
theorem eval_sub_sq_le
    (form : Hermitian.HermitianForm) {bounding current : Rational.Box} {left right :
      Data.Gaussian.Basic.Canonical}
    (refines : current.Refines bounding)
    (leftInside : current.Contains left)
    (rightInside : current.Contains right) :
    (form.eval left - form.eval right) ^ 2 ≤
      variationSqBound form bounding current := by
  have normDifference := Rational.Box.normSq_sub_sq_le refines leftInside rightInside
  have realDifference := Rational.Box.real_sub_sq_le_diagonalSq leftInside rightInside
  have imaginaryDifference := Rational.Box.imag_sub_sq_le_diagonalSq leftInside rightInside
  have radialSquare := Fraction.Order.Arithmetic.sq_nonneg_direct form.radial
  have realSquare :=
    Fraction.Order.Arithmetic.sq_nonneg_direct form.realLinear
  have imaginarySquare :=
    Fraction.Order.Arithmetic.sq_nonneg_direct form.imagLinear
  have radialTerm :
      (form.radial * (Data.Gaussian.Norm.Basic.normSq left - Data.Gaussian.Norm.Basic.normSq right)) ^
        2 ≤
        form.radial ^ 2 *
          (16 * bounding.coordinateSqBound * current.diagonalSq) := by
    rw [Purelib.Algebra.Semiring.Normalization.product_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      normDifference radialSquare
  have realTerm :
      (form.realLinear * (left.re - right.re)) ^ 2 ≤
        form.realLinear ^ 2 * current.diagonalSq := by
    rw [Purelib.Algebra.Semiring.Normalization.product_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      realDifference realSquare
  have imaginaryTerm :
      (form.imagLinear * (left.im - right.im)) ^ 2 ≤
        form.imagLinear ^ 2 * current.diagonalSq := by
    rw [Purelib.Algebra.Semiring.Normalization.product_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      imaginaryDifference imaginarySquare
  have termSum :
      (form.radial * (Data.Gaussian.Norm.Basic.normSq left - Data.Gaussian.Norm.Basic.normSq right)) ^
        2 +
          (form.realLinear * (left.re - right.re)) ^ 2 +
          (form.imagLinear * (left.im - right.im)) ^ 2 ≤
        form.radial ^ 2 *
            (16 * bounding.coordinateSqBound * current.diagonalSq) +
          form.realLinear ^ 2 * current.diagonalSq +
          form.imagLinear ^ 2 * current.diagonalSq :=
    add_le_add (add_le_add radialTerm realTerm) imaginaryTerm
  have threeNonnegative : (0 : Fraction.Rational) ≤ 3 := by decide
  calc
    (form.eval left - form.eval right) ^ 2 =
        (form.radial * (Data.Gaussian.Norm.Basic.normSq left - Data.Gaussian.Norm.Basic.normSq right)
          +
          form.realLinear * (left.re - right.re) +
          form.imagLinear * (left.im - right.im)) ^ 2 := by
      simp only [HermitianForm.eval, -eq_self, -iff_self]
      ring1
    _ ≤ 3 *
        ((form.radial * (Data.Gaussian.Norm.Basic.normSq left - Data.Gaussian.Norm.Basic.normSq
          right)) ^ 2 +
          (form.realLinear * (left.re - right.re)) ^ 2 +
          (form.imagLinear * (left.im - right.im)) ^ 2) :=
      Bounds.Square.Boundary.add_sq_le_three _ _ _
    _ ≤ 3 *
        (form.radial ^ 2 *
            (16 * bounding.coordinateSqBound * current.diagonalSq) +
          form.realLinear ^ 2 * current.diagonalSq +
          form.imagLinear ^ 2 * current.diagonalSq) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        termSum threeNonnegative
    _ = variationSqBound form bounding current := by
      simp only [variationSqBound,
        variationCoefficient, -eq_self, -iff_self]
      ring1
end Purelib.Geometry.Projective.Hermitian.Box

end
