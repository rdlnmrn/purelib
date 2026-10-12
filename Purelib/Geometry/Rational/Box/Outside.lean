module
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Rational.Box.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational.Box

section
@[expose] public section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

namespace Purelib.Geometry.Rational.Box

/-- One explicit coordinate side by which a rational point is outside a rational box. -/
inductive OutsideSide (box : Rational.Box) (point :
  Data.Gaussian.Basic.Canonical) where
  /-- The point lies strictly to the left of the box. -/ | left (less : point.re < box.xLower)
  /-- The point lies strictly to the right of the box. -/ | right (less : box.xUpper < point.re)
  /-- The point lies strictly below the box. -/ | bottom (less : point.im < box.yLower)
  /-- The point lies strictly above the box. -/ | top (less : box.yUpper < point.im)

/-- A failed finite membership test computes a strict outside side. -/
def outsideSide {box : Rational.Box} {point :
  Data.Gaussian.Basic.Canonical}
    (outside : ¬box.Contains point) : OutsideSide box point := by
  by_cases left : point.re < box.xLower
  · exact .left left
  by_cases right : box.xUpper < point.re
  · exact .right right
  by_cases bottom : point.im < box.yLower
  · exact .bottom bottom
  by_cases top : box.yUpper < point.im
  · exact .top top
  exact (outside ⟨le_of_not_gt left, le_of_not_gt right,
    le_of_not_gt bottom, le_of_not_gt top⟩).elim

namespace OutsideSide

/-- Squared coordinate distance certified by an outside side. -/
def margin {box : Rational.Box} {point :
  Data.Gaussian.Basic.Canonical} :
    OutsideSide box point → Fraction.Rational
  | .left _ => (box.xLower - point.re) ^ 2
  | .right _ => (point.re - box.xUpper) ^ 2
  | .bottom _ => (box.yLower - point.im) ^ 2
  | .top _ => (point.im - box.yUpper) ^ 2

/-- Every certified strict outside side has positive squared coordinate margin. -/
theorem margin_pos {box : Rational.Box} {point :
  Data.Gaussian.Basic.Canonical}
    (side : OutsideSide box point) : 0 < side.margin := by
  cases side with
  | left less =>
      rw [margin, pow_two]
      exact Fraction.Order.Arithmetic.mul_pos_direct
        (Fraction.Order.Arithmetic.sub_pos_direct less)
        (Fraction.Order.Arithmetic.sub_pos_direct less)
  | right less =>
      rw [margin, pow_two]
      exact Fraction.Order.Arithmetic.mul_pos_direct
        (Fraction.Order.Arithmetic.sub_pos_direct less)
        (Fraction.Order.Arithmetic.sub_pos_direct less)
  | bottom less =>
      rw [margin, pow_two]
      exact Fraction.Order.Arithmetic.mul_pos_direct
        (Fraction.Order.Arithmetic.sub_pos_direct less)
        (Fraction.Order.Arithmetic.sub_pos_direct less)
  | top less =>
      rw [margin, pow_two]
      exact Fraction.Order.Arithmetic.mul_pos_direct
        (Fraction.Order.Arithmetic.sub_pos_direct less)
        (Fraction.Order.Arithmetic.sub_pos_direct less)

/-- Every point of the box stays at least the displayed squared coordinate distance from the excluded point.

The retained side witness selects the original coordinate gap, whose square is bounded by the corresponding coordinate
difference and then by the full quadrance. -/
theorem margin_le_normSq_sub
    {box : Rational.Box} {point value : Data.Gaussian.Basic.Canonical}
    (side : OutsideSide box point) (inside : box.Contains value) :
    side.margin ≤ Data.Gaussian.Norm.Basic.normSq (value - point) := by
  cases side with
  | left less =>
      have gapNonnegative : 0 ≤ box.xLower - point.re :=
        Fraction.Order.Arithmetic.sub_nonneg_direct less.le
      have coordinateNonnegative : 0 ≤ value.re - point.re :=
        Fraction.Order.Arithmetic.sub_nonneg_direct (less.le.trans inside.1)
      have gapOrder : box.xLower - point.re ≤ value.re - point.re :=
        Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.1 point.re
      calc
        (OutsideSide.left less).margin =
            (box.xLower - point.re) ^ 2 := rfl
        _ ≤ (value.re - point.re) ^ 2 :=
          Purelib.Data.Rat.Bounds.Square.sq_le_sq_of_nonneg gapOrder gapNonnegative coordinateNonnegative
        _ ≤ (value.re - point.re) ^ 2 +
            (value.im - point.im) ^ 2 :=
          le_add_of_nonneg_right
            (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        _ = Data.Gaussian.Norm.Basic.normSq (value - point) := by
          simp only [Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
            -eq_self, -iff_self]
          rfl
  | right less =>
      have gapNonnegative : 0 ≤ point.re - box.xUpper :=
        Fraction.Order.Arithmetic.sub_nonneg_direct less.le
      have coordinateNonnegative : 0 ≤ point.re - value.re :=
        Fraction.Order.Arithmetic.sub_nonneg_direct
          (inside.2.1.trans less.le)
      have gapOrder : point.re - box.xUpper ≤ point.re - value.re :=
        Fraction.Order.Arithmetic.sub_le_sub_left_direct inside.2.1 point.re
      calc
        (OutsideSide.right less).margin =
            (point.re - box.xUpper) ^ 2 := rfl
        _ ≤ (point.re - value.re) ^ 2 :=
          Purelib.Data.Rat.Bounds.Square.sq_le_sq_of_nonneg gapOrder gapNonnegative coordinateNonnegative
        _ = (value.re - point.re) ^ 2 := by ring1
        _ ≤ (value.re - point.re) ^ 2 +
            (value.im - point.im) ^ 2 :=
          le_add_of_nonneg_right
            (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        _ = Data.Gaussian.Norm.Basic.normSq (value - point) := by
          simp only [Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
            -eq_self, -iff_self]
          rfl
  | bottom less =>
      have gapNonnegative : 0 ≤ box.yLower - point.im :=
        Fraction.Order.Arithmetic.sub_nonneg_direct less.le
      have coordinateNonnegative : 0 ≤ value.im - point.im :=
        Fraction.Order.Arithmetic.sub_nonneg_direct
          (less.le.trans inside.2.2.1)
      have gapOrder : box.yLower - point.im ≤ value.im - point.im :=
        Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2.2.1 point.im
      calc
        (OutsideSide.bottom less).margin =
            (box.yLower - point.im) ^ 2 := rfl
        _ ≤ (value.im - point.im) ^ 2 :=
          Purelib.Data.Rat.Bounds.Square.sq_le_sq_of_nonneg gapOrder gapNonnegative coordinateNonnegative
        _ ≤ (value.re - point.re) ^ 2 +
            (value.im - point.im) ^ 2 :=
          le_add_of_nonneg_left
            (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        _ = Data.Gaussian.Norm.Basic.normSq (value - point) := by
          simp only [Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
            -eq_self, -iff_self]
          rfl
  | top less =>
      have gapNonnegative : 0 ≤ point.im - box.yUpper :=
        Fraction.Order.Arithmetic.sub_nonneg_direct less.le
      have coordinateNonnegative : 0 ≤ point.im - value.im :=
        Fraction.Order.Arithmetic.sub_nonneg_direct
          (inside.2.2.2.trans less.le)
      have gapOrder : point.im - box.yUpper ≤ point.im - value.im :=
        Fraction.Order.Arithmetic.sub_le_sub_left_direct inside.2.2.2 point.im
      calc
        (OutsideSide.top less).margin =
            (point.im - box.yUpper) ^ 2 := rfl
        _ ≤ (point.im - value.im) ^ 2 :=
          Purelib.Data.Rat.Bounds.Square.sq_le_sq_of_nonneg gapOrder gapNonnegative coordinateNonnegative
        _ = (value.im - point.im) ^ 2 := by ring1
        _ ≤ (value.re - point.re) ^ 2 +
            (value.im - point.im) ^ 2 :=
          le_add_of_nonneg_left
            (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        _ = Data.Gaussian.Norm.Basic.normSq (value - point) := by
          simp only [Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
            -eq_self, -iff_self]
          rfl

end OutsideSide
end Purelib.Geometry.Rational.Box

end
