module
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Bounds
public import Purelib.Geometry.Rational.Box.Band.Basic
public import Purelib.Geometry.Rational.Box.Boundary
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.Ring

/-!
# Quadrance and containment bounds for rational bands

The original band retains eight side comparisons around its centre.
Those endpoint bounds control properness, outer-square refinement and
the original diagonal and radial quadrance measurements.
-/

open Purelib
open Purelib.Data.Rat
open Fraction.Order
open Purelib.Geometry
open Purelib.Geometry.Rational.Box
open Purelib.Geometry.Rational.Box.Square.Centered

namespace Purelib.Geometry.Rational.Box.Band.Basic.BandBox

open Purelib.Data.Rat.Bounds

/-- A positive band radius places the center strictly between all four rectangle sides.

The original band endpoints lie at least one positive radius from
the retained centre in each coordinate. Direct scalar displacements
place that same centre strictly between both pairs of sides. -/
public theorem center_strictly_inside
    {center : Data.Gaussian.Basic.Canonical} {r : Fraction.Rational} (band : Band.Basic.BandBox center r)
    (positive : 0 < r) :
    band.box.xLower < center.re ∧ center.re < band.box.xUpper ∧
      band.box.yLower < center.im ∧ center.im < band.box.yUpper := by
  have realLower : center.re - r < center.re := by
    calc
      center.re - r < center.re - 0 :=
        Arithmetic.sub_lt_sub_left_direct positive center.re
      _ = center.re := by ring1
  have realUpper : center.re < center.re + r := by
    calc
      center.re = center.re + 0 := by ring1
      _ < center.re + r := Arithmetic.add_lt_add_left_direct positive center.re
  have imaginaryLower : center.im - r < center.im := by
    calc
      center.im - r < center.im - 0 :=
        Arithmetic.sub_lt_sub_left_direct positive center.im
      _ = center.im := by ring1
  have imaginaryUpper : center.im < center.im + r := by
    calc
      center.im = center.im + 0 := by ring1
      _ < center.im + r := Arithmetic.add_lt_add_left_direct positive center.im
  exact ⟨band.left_upper.trans_lt realLower,
    realUpper.trans_le band.right_lower,
    band.bottom_upper.trans_lt imaginaryLower,
    imaginaryUpper.trans_le band.top_lower⟩

/-- A band with positive radius has strictly positive width and height.

The original positive radius places the retained centre strictly
between both real sides and both imaginary sides. Composing those
strict comparisons proves the original rectangle has positive side lengths. -/
public theorem proper
    {center : Data.Gaussian.Basic.Canonical} {r : Fraction.Rational} (band : Band.Basic.BandBox center r)
    (positive : 0 < r) : band.box.Proper := by
  have inside := band.center_strictly_inside positive
  exact ⟨inside.1.trans inside.2.1, inside.2.2.1.trans inside.2.2.2⟩

/-- A band rectangle refines the concentric square with twice its nonnegative radius.

The eight original side constraints place all band endpoints
within the square of twice the same nonnegative radius. These retained
comparisons give refinement of that concentric outer square. -/
public theorem refines_outerSquare
    {center : Data.Gaussian.Basic.Canonical} {r : Fraction.Rational} (band : Band.Basic.BandBox center r)
    (nonnegative : 0 ≤ r) :
    band.box.Refines
      (Affine.centeredSquare center (2 * r)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          nonnegative)) :=
  ⟨band.left_lower, band.right_upper,
    band.bottom_lower, band.top_upper⟩

/-- The squared band diagonal is at most thirty-two times the squared positive radius.

The original side constraints bound each nonnegative side length
by four times the same positive radius. Their two square comparisons
bound the retained squared diagonal by thirty-two radius squares. -/
public theorem diagonalSq_le
    {center : Data.Gaussian.Basic.Canonical} {r : Fraction.Rational} (band : Band.Basic.BandBox center r)
    (positive : 0 < r) : band.box.diagonalSq ≤ 32 * r ^ 2 := by
  have widthXBound : band.box.widthX ≤ 4 * r := by
    have shifted := Fraction.Order.Arithmetic.sub_le_sub_direct band.right_upper band.left_lower
    calc
      band.box.widthX = band.box.xUpper - band.box.xLower := rfl
      _ ≤ (center.re + 2 * r) - (center.re - 2 * r) := shifted
      _ = 4 * r := by ring1
  have widthYBound : band.box.widthY ≤ 4 * r := by
    have shifted := Fraction.Order.Arithmetic.sub_le_sub_direct band.top_upper band.bottom_lower
    calc
      band.box.widthY = band.box.yUpper - band.box.yLower := rfl
      _ ≤ (center.im + 2 * r) - (center.im - 2 * r) := shifted
      _ = 4 * r := by ring1
  have fourRadiusNonnegative : 0 ≤ 4 * r :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) positive.le
  have widthXSquared := Fraction.Order.Arithmetic.pow_le_pow_direct
    band.box.widthX_nonneg widthXBound 2
  have widthYSquared := Fraction.Order.Arithmetic.pow_le_pow_direct
    band.box.widthY_nonneg widthYBound 2
  calc
    band.box.diagonalSq = band.box.widthX ^ 2 + band.box.widthY ^ 2 := rfl
    _ ≤ (4 * r) ^ 2 + (4 * r) ^ 2 :=
      add_le_add widthXSquared widthYSquared
    _ = 32 * r ^ 2 := by ring1

end Purelib.Geometry.Rational.Box.Band.Basic.BandBox

namespace Purelib.Geometry.Rational.Box.Band.Bounds

open Purelib.Data.Rat.Bounds

/-- The widest admissible band attains the coefficient thirty-two in the squared-diagonal bound.

The original widest band is the concentric square of twice the
same positive radius. Substitution into its exact squared-diagonal
formula yields the displayed coefficient thirty-two. -/
public theorem widestBand_diagonalSq
    (center : Data.Gaussian.Basic.Canonical) (r : Fraction.Rational) (positive : 0 < r) :
    (Band.Basic.widestBand center r positive).box.diagonalSq = 32 * r ^ 2 := by
  change
    (Affine.centeredSquare center (2 * r)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        positive.le)).diagonalSq = 32 * r ^ 2
  rw [Affine.centeredSquare_diagonalSq]
  ring1

/-- The widest band diagonal square equals half the square of eight times its radius.

The retained widest band has squared diagonal thirty-two radius
squares. The same quantity equals half the square of eight times
the original positive radius. -/
public theorem widestBand_diagonalSq_eq_half_request
    (center : Data.Gaussian.Basic.Canonical) (r : Fraction.Rational) (positive : 0 < r) :
    (Band.Basic.widestBand center r positive).box.diagonalSq =
      (1 / 2 : Fraction.Rational) * (8 * r) ^ 2 := by
  rw [Geometry.Rational.Box.Band.Bounds.widestBand_diagonalSq]
  have coefficientIdentity : (1 / 2 : Fraction.Rational) * 8 ^ 2 = 32 := by decide
  calc
    32 * r ^ 2 = ((1 / 2 : Fraction.Rational) * 8 ^ 2) * r ^ 2 := by
      rw [coefficientIdentity]
    _ = (1 / 2 : Fraction.Rational) * (8 * r) ^ 2 := by ring1

end Purelib.Geometry.Rational.Box.Band.Bounds

namespace Purelib.Geometry.Rational.Box.Band.Basic.BandBox

open Purelib.Data.Rat.Bounds

/-- Every point of the selected band is within squared distance `8r²` of its center.

The retained containment witness and band endpoint constraints
bound both coordinate displacements by twice the original radius.
Their square bounds add to at most eight radius squares. -/
public theorem radial_upper
    {center : Data.Gaussian.Basic.Canonical} {r : Fraction.Rational} (band : Band.Basic.BandBox center r)
    {z : Data.Gaussian.Basic.Canonical} (inside : band.box.Contains z) :
    Data.Gaussian.Norm.Basic.normSq (z - center) ≤ 8 * r ^ 2 := by
  have realLower : -(2 * r) ≤ z.re - center.re := by
    calc
      -(2 * r) = center.re - 2 * r - center.re := by ring1
      _ ≤ z.re - center.re := Fraction.Order.Arithmetic.sub_le_sub_right_direct
        (band.left_lower.trans inside.1) center.re
  have realUpper : z.re - center.re ≤ 2 * r := by
    calc
      z.re - center.re ≤ center.re + 2 * r - center.re :=
        Fraction.Order.Arithmetic.sub_le_sub_right_direct (inside.2.1.trans band.right_upper) center.re
      _ = 2 * r := by ring1
  have imaginaryLower : -(2 * r) ≤ z.im - center.im := by
    calc
      -(2 * r) = center.im - 2 * r - center.im := by ring1
      _ ≤ z.im - center.im := Fraction.Order.Arithmetic.sub_le_sub_right_direct
        (band.bottom_lower.trans inside.2.2.1) center.im
  have imaginaryUpper : z.im - center.im ≤ 2 * r := by
    calc
      z.im - center.im ≤ center.im + 2 * r - center.im :=
        Fraction.Order.Arithmetic.sub_le_sub_right_direct (inside.2.2.2.trans band.top_upper) center.im
      _ = 2 * r := by ring1
  have realSquare := Rational.Box.sq_le_endpoint_max
    realLower realUpper
  have imaginarySquare := Rational.Box.sq_le_endpoint_max
    imaginaryLower imaginaryUpper
  have endpointSquare : (-(2 * r)) ^ 2 = (2 * r) ^ 2 := by ring1
  rw [endpointSquare, Fraction.Order.Basic.max_self] at realSquare imaginarySquare
  calc
    Data.Gaussian.Norm.Basic.normSq (z - center) =
        (z.re - center.re) ^ 2 + (z.im - center.im) ^ 2 := rfl
    _ ≤ (2 * r) ^ 2 + (2 * r) ^ 2 :=
      add_le_add realSquare imaginarySquare
    _ = 8 * r ^ 2 := by ring1

/-- Every boundary point is at squared distance at least `r²` from the center.

A retained boundary point lies on one original band side. That
side is at least the same nonnegative radius from the centre in
one coordinate, whose square bounds the total displacement quadrance. -/
public theorem radial_lower
    {center : Data.Gaussian.Basic.Canonical} {r : Fraction.Rational} (band : Band.Basic.BandBox center r)
    (nonnegative : 0 ≤ r) {z : Data.Gaussian.Basic.Canonical}
    (boundary : Boundary.OnBoxBoundary band.box z) :
    r ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq (z - center) := by
  rcases boundary.2 with onLeft | onRight | onBottom | onTop
  · have distance : r ≤ center.re - z.re := by
      calc
        r = center.re - (center.re - r) := by ring1
        _ ≤ center.re - band.box.xLower :=
          Fraction.Order.Arithmetic.sub_le_sub_left_direct band.left_upper center.re
        _ = center.re - z.re := by rw [onLeft]
    have square := Fraction.Order.Arithmetic.pow_le_pow_direct
      nonnegative distance 2
    calc
      r ^ 2 ≤ (center.re - z.re) ^ 2 := square
      _ = (z.re - center.re) ^ 2 := by ring1
      _ ≤ (z.re - center.re) ^ 2 + (z.im - center.im) ^ 2 :=
        le_add_of_nonneg_right
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  · have distance : r ≤ z.re - center.re := by
      calc
        r = center.re + r - center.re := by ring1
        _ ≤ band.box.xUpper - center.re :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct band.right_lower center.re
        _ = z.re - center.re := by rw [onRight]
    have square := Fraction.Order.Arithmetic.pow_le_pow_direct
      nonnegative distance 2
    exact square.trans (le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  · have distance : r ≤ center.im - z.im := by
      calc
        r = center.im - (center.im - r) := by ring1
        _ ≤ center.im - band.box.yLower :=
          Fraction.Order.Arithmetic.sub_le_sub_left_direct band.bottom_upper center.im
        _ = center.im - z.im := by rw [onBottom]
    have square := Fraction.Order.Arithmetic.pow_le_pow_direct
      nonnegative distance 2
    calc
      r ^ 2 ≤ (center.im - z.im) ^ 2 := square
      _ = (z.im - center.im) ^ 2 := by ring1
      _ ≤ (z.re - center.re) ^ 2 + (z.im - center.im) ^ 2 :=
        le_add_of_nonneg_left
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  · have distance : r ≤ z.im - center.im := by
      calc
        r = center.im + r - center.im := by ring1
        _ ≤ band.box.yUpper - center.im :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct band.top_lower center.im
        _ = z.im - center.im := by rw [onTop]
    have square := Fraction.Order.Arithmetic.pow_le_pow_direct
      nonnegative distance 2
    exact square.trans (le_add_of_nonneg_left
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))

end Purelib.Geometry.Rational.Box.Band.Basic.BandBox
