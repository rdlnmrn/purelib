module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Nat.Order
import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Bounds

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Geometry.Rational (Box)

/-!
# Rational squares around a retained centre

The original Gaussian centres and rational half-widths determine explicit
closed boxes. Scalar certificates compare their retained endpoints and
control containment, strict interior and squared distance.
-/

open scoped Purelib.Data.Nat

open Purelib
open Purelib.Data.Rat
open Fraction.Order
open Purelib.Geometry

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

namespace Purelib.Geometry.Rational.Box.Square.Centered.BoxTransport

/-- The closed rational square of half-width `radius` about `center`.

The original centre coordinates and nonnegative half-width determine
the four rational endpoints. Their retained ordering proofs compare
those same endpoints; no coordinate or radius observation is replaced. -/
@[expose] public def centeredBox (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational)
    (radiusNonnegative : 0 ≤ radius) : Rational.Box where
  xLower := center.re - radius
  xUpper := center.re + radius
  yLower := center.im - radius
  yUpper := center.im + radius
  x_valid := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ 2 * radius :=
        Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) radiusNonnegative
      _ = (center.re + radius) - (center.re - radius) := by ring1
  y_valid := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ 2 * radius :=
        Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) radiusNonnegative
      _ = (center.im + radius) - (center.im - radius) := by ring1

end Purelib.Geometry.Rational.Box.Square.Centered.BoxTransport

namespace Purelib.Geometry.Rational.Box.Square.Centered

/-- A squared Euclidean error bounded by the half-width squared places the value in the explicit centred rational box.

The original Gaussian squared displacement is at most the supplied
radius square. Its two coordinate square bounds give the signed
displacements from the same centre and hence closed box containment. -/
public theorem centeredBox_contains_of_normSq_sub_le
    {center value : Data.Gaussian.Basic.Canonical} {radius : Fraction.Rational}
    (radiusNonnegative : 0 ≤ radius)
    (distanceBound : Data.Gaussian.Norm.Basic.normSq (value - center) ≤ radius ^ 2) :
    (Box.Square.Centered.BoxTransport.centeredBox center radius radiusNonnegative).Contains value :=
      by
  have realSquare : (value.re - center.re) ^ 2 ≤ radius ^ 2 :=
    calc
      (value.re - center.re) ^ 2 ≤
          (value.re - center.re) ^ 2 + (value.im - center.im) ^ 2 :=
        le_add_of_nonneg_right
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ = Data.Gaussian.Norm.Basic.normSq (value - center) := rfl
      _ ≤ radius ^ 2 := distanceBound
  have imaginarySquare : (value.im - center.im) ^ 2 ≤ radius ^ 2 :=
    calc
      (value.im - center.im) ^ 2 ≤
          (value.re - center.re) ^ 2 + (value.im - center.im) ^ 2 :=
        le_add_of_nonneg_left
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ = Data.Gaussian.Norm.Basic.normSq (value - center) := rfl
      _ ≤ radius ^ 2 := distanceBound
  have realBounds := Bounds.Square.signed_bounds_of_sq_le_sq radiusNonnegative realSquare
  have imaginaryBounds :=
    Bounds.Square.signed_bounds_of_sq_le_sq radiusNonnegative imaginarySquare
  exact
    ⟨by
      calc
        center.re - radius = -radius + center.re := by ring1
        _ ≤ (value.re - center.re) + center.re :=
          add_le_add_left realBounds.1 center.re
        _ = value.re := by ring1,
      by
        calc
          value.re = (value.re - center.re) + center.re := by ring1
          _ ≤ radius + center.re := add_le_add_left realBounds.2 center.re
          _ = center.re + radius := by ring1,
      by
        calc
          center.im - radius = -radius + center.im := by ring1
          _ ≤ (value.im - center.im) + center.im :=
            add_le_add_left imaginaryBounds.1 center.im
          _ = value.im := by ring1,
      by
        calc
          value.im = (value.im - center.im) + center.im := by ring1
          _ ≤ radius + center.im :=
            add_le_add_left imaginaryBounds.2 center.im
          _ = center.im + radius := by ring1⟩

end Purelib.Geometry.Rational.Box.Square.Centered

namespace Purelib.Geometry.Rational.Box.Square.Centered.BoxTransport

/-- A centered box of half-width radius has squared diagonal eight times the squared radius.

Both original side lengths are twice the nonnegative half-width.
The sum of their squares therefore equals eight times that same
radius square. -/
public theorem centeredBox_diagonalSq
    (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational)
    (radiusNonnegative : 0 ≤ radius) :
    (centeredBox center radius radiusNonnegative).diagonalSq =
      8 * radius ^ 2 := by
  simp only [Rational.Box.diagonalSq, centeredBox]
  ring1

end Purelib.Geometry.Rational.Box.Square.Centered.BoxTransport

namespace Purelib.Geometry.Rational.Box.Square.Centered

/-- The rational square of half-width epsilon divided by four around the displayed centre.

The original positive rational accuracy parameter determines the
half-width epsilon divided by four. The same centre and positive
quotient construct the retained centred box. -/
@[expose] public def epsilonBox (center : Data.Gaussian.Basic.Canonical) (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon) : Rational.Box :=
  Box.Square.Centered.BoxTransport.centeredBox center (epsilon / 4)
    (Fraction.Order.Field.div_nonneg_direct epsilonPositive.le (by decide))

/-- The square of half-width epsilon divided by four has squared diagonal epsilon squared divided by two.

The retained box has half-width epsilon divided by four. Substituting
that same quotient into the exact diagonal formula gives epsilon
squared divided by two. -/
public theorem epsilonBox_diagonalSq
    (center : Data.Gaussian.Basic.Canonical) (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon) :
    (epsilonBox center epsilon epsilonPositive).diagonalSq = epsilon ^ 2 / 2 := by
  unfold epsilonBox
  rw [Box.Square.Centered.BoxTransport.centeredBox_diagonalSq]
  rw [pow_two]
  have squareQuotient :
      (epsilon / 4) * (epsilon / 4) =
        (epsilon * epsilon) / ((4 : Fraction.Rational) * 4) :=
    Fraction.Field.div_mul_div_direct epsilon 4 epsilon 4
  rw [squareQuotient]
  have fourTimesFour : (4 : Fraction.Rational) * 4 = 16 := by decide
  have eightSixteenths : (8 : Fraction.Rational) / 16 = 1 / 2 := by decide
  rw [fourTimesFour]
  calc
    8 * (epsilon * epsilon / 16) =
        (epsilon * epsilon) * (8 / 16) := by
      simp only [ExplicitField.div_eq_mul_inv]
      calc
        8 * ((epsilon * epsilon) * (16 : Fraction.Rational)⁻¹) =
            (8 * (epsilon * epsilon)) * (16 : Fraction.Rational)⁻¹ :=
          (Fraction.Field.mul_assoc _ _ _).symm
        _ = ((epsilon * epsilon) * 8) * (16 : Fraction.Rational)⁻¹ := by
          rw [Fraction.Field.mul_comm 8 (epsilon * epsilon)]
        _ = (epsilon * epsilon) * (8 * (16 : Fraction.Rational)⁻¹) :=
          Fraction.Field.mul_assoc _ _ _
    _ = (epsilon * epsilon) * (1 / 2) := by rw [eightSixteenths]
    _ = epsilon ^ 2 / 2 := by
      rw [pow_two, ExplicitField.div_eq_mul_inv,
        ExplicitField.div_eq_mul_inv,
        _root_.one_mul]

/-- The epsilon box satisfies the requested squared-diagonal bound.

The original positive accuracy parameter fixes the same retained
centred box. Its exact diagonal square is half the nonnegative
epsilon square, hence at most that requested square. -/
public theorem epsilonBox_diagonalSq_le
    (center : Data.Gaussian.Basic.Canonical) (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon) :
    (epsilonBox center epsilon epsilonPositive).diagonalSq ≤ epsilon ^ 2 := by
  rw [epsilonBox_diagonalSq]
  apply (Fraction.Order.Field.div_le_iff_pos
    (show (0 : Fraction.Rational) < 2 by decide)).2
  calc
    epsilon ^ 2 = epsilon ^ 2 * 1 := by ring1
    _ ≤ epsilon ^ 2 * 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (by decide) (Fraction.Order.Arithmetic.sq_nonneg_direct epsilon)

/-- The rational square of half-width one sixteenth around the displayed Gaussian centre.

The original Gaussian centre determines all four displayed endpoints
using the same fixed half-width one sixteenth. Direct rational order
certificates retain those original endpoints as their indices. -/
@[expose] public def connectorFixedBox (root : Data.Gaussian.Basic.Canonical) : Rational.Box where
  xLower := root.re - 1 / 16
  xUpper := root.re + 1 / 16
  yLower := root.im - 1 / 16
  yUpper := root.im + 1 / 16
  x_valid := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ 2 * (1 / 16 : Fraction.Rational) := by decide
      _ = (root.re + 1 / 16) - (root.re - 1 / 16) := by ring1
  y_valid := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ 2 * (1 / 16 : Fraction.Rational) := by decide
      _ = (root.im + 1 / 16) - (root.im - 1 / 16) := by ring1

/-- The square of half-width one sixteenth has strictly positive width and height.

The original square subtracts and adds the positive half-width one
sixteenth in both coordinates. Strict scalar displacement places its
centre between both pairs of retained endpoints. -/
public theorem connectorFixedBox_proper (root : Data.Gaussian.Basic.Canonical) :
    (connectorFixedBox root).Proper := by
  have realLower : root.re - 1 / 16 < root.re := by
    calc
      root.re - 1 / 16 < root.re - 0 :=
        Arithmetic.sub_lt_sub_left_direct (show (0 : Fraction.Rational) < 1 / 16 by decide) root.re
      _ = root.re := by ring1
  have realUpper : root.re < root.re + 1 / 16 := by
    calc
      root.re = root.re + 0 := by ring1
      _ < root.re + 1 / 16 :=
        Arithmetic.add_lt_add_left_direct (show (0 : Fraction.Rational) < 1 / 16 by decide) root.re
  have imaginaryLower : root.im - 1 / 16 < root.im := by
    calc
      root.im - 1 / 16 < root.im - 0 :=
        Arithmetic.sub_lt_sub_left_direct (show (0 : Fraction.Rational) < 1 / 16 by decide) root.im
      _ = root.im := by ring1
  have imaginaryUpper : root.im < root.im + 1 / 16 := by
    calc
      root.im = root.im + 0 := by ring1
      _ < root.im + 1 / 16 :=
        Arithmetic.add_lt_add_left_direct (show (0 : Fraction.Rational) < 1 / 16 by decide) root.im
  exact ⟨realLower.trans realUpper, imaginaryLower.trans imaginaryUpper⟩

/-- The center lies strictly to the right of the square left side.

The retained left endpoint subtracts the positive rational one
sixteenth from the original real coordinate. The same scalar
displacement is therefore strictly below that coordinate. -/
public theorem connectorFixedBox_left (root : Data.Gaussian.Basic.Canonical) :
    (connectorFixedBox root).xLower < root.re := by
  change root.re - 1 / 16 < root.re
  calc
    root.re - 1 / 16 < root.re - 0 :=
      Arithmetic.sub_lt_sub_left_direct (show (0 : Fraction.Rational) < 1 / 16 by decide) root.re
    _ = root.re := by ring1

/-- The center lies strictly to the left of the square right side.

The retained right endpoint adds the positive rational one
sixteenth to the original real coordinate. The same scalar
displacement is therefore strictly above that coordinate. -/
public theorem connectorFixedBox_right (root : Data.Gaussian.Basic.Canonical) :
    root.re < (connectorFixedBox root).xUpper := by
  change root.re < root.re + 1 / 16
  calc
    root.re = root.re + 0 := by ring1
    _ < root.re + 1 / 16 :=
      Arithmetic.add_lt_add_left_direct (show (0 : Fraction.Rational) < 1 / 16 by decide) root.re

/-- The center lies strictly above the square bottom side.

The retained lower endpoint subtracts the positive rational one
sixteenth from the original imaginary coordinate. It is strictly
below that same coordinate. -/
public theorem connectorFixedBox_below (root : Data.Gaussian.Basic.Canonical) :
    (connectorFixedBox root).yLower < root.im := by
  change root.im - 1 / 16 < root.im
  calc
    root.im - 1 / 16 < root.im - 0 :=
      Arithmetic.sub_lt_sub_left_direct (show (0 : Fraction.Rational) < 1 / 16 by decide) root.im
    _ = root.im := by ring1

/-- The center lies strictly below the square top side.

The retained upper endpoint adds the positive rational one
sixteenth to the original imaginary coordinate. It is strictly
above that same coordinate. -/
public theorem connectorFixedBox_above (root : Data.Gaussian.Basic.Canonical) :
    root.im < (connectorFixedBox root).yUpper := by
  change root.im < root.im + 1 / 16
  calc
    root.im = root.im + 0 := by ring1
    _ < root.im + 1 / 16 :=
      Arithmetic.add_lt_add_left_direct (show (0 : Fraction.Rational) < 1 / 16 by decide) root.im

/-- The square of half-width one sixteenth contains its center.

The four retained endpoint comparisons place the original Gaussian
centre between both real endpoints and both imaginary endpoints.
Those same comparisons certify its closed containment. -/
public theorem connectorFixedBox_contains (root : Data.Gaussian.Basic.Canonical) :
    (connectorFixedBox root).Contains root :=
  ⟨(connectorFixedBox_left root).le,
    (connectorFixedBox_right root).le,
    (connectorFixedBox_below root).le,
    (connectorFixedBox_above root).le⟩

/-- The square of half-width one sixteenth centered at the displayed real-axis coordinate.

The original real coordinate fixes the horizontal centre and zero
fixes the imaginary centre. The positive half-width one sixteenth
determines the same four displayed endpoints and ordering proofs. -/
@[expose] public def realAxisSquareSixteenth (x : Fraction.Rational) : Rational.Box where
  xLower := x - 1 / 16
  xUpper := x + 1 / 16
  yLower := -(1 / 16)
  yUpper := 1 / 16
  x_valid := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ 2 * (1 / 16 : Fraction.Rational) := by decide
      _ = (x + 1 / 16) - (x - 1 / 16) := by ring1
  y_valid := by decide

/-- The square of half-width one sixteenth centered at the displayed Gaussian point.

The original Gaussian point determines the centre of the retained
square. Both coordinate intervals use the same positive half-width
one sixteenth and retain their endpoint ordering certificates. -/
@[expose] public def sampleBox (root : Data.Gaussian.Basic.Canonical) : Rational.Box where
  xLower := root.re - 1 / 16
  xUpper := root.re + 1 / 16
  yLower := root.im - 1 / 16
  yUpper := root.im + 1 / 16
  x_valid := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ 2 * (1 / 16 : Fraction.Rational) := by decide
      _ = (root.re + 1 / 16) - (root.re - 1 / 16) := by ring1
  y_valid := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ 2 * (1 / 16 : Fraction.Rational) := by decide
      _ = (root.im + 1 / 16) - (root.im - 1 / 16) := by ring1

/-- The fixed-width square centered on the real axis has positive side lengths.

The original square subtracts and adds one sixteenth from its real
centre and uses the signed fixed endpoints around zero vertically.
Both retained intervals have strictly positive length. -/
public theorem realAxisSquareSixteenth_proper (x : Fraction.Rational) :
  (realAxisSquareSixteenth x).Proper := by
  have realLower : x - 1 / 16 < x := by
    calc
      x - 1 / 16 < x - 0 :=
        Arithmetic.sub_lt_sub_left_direct (show (0 : Fraction.Rational) < 1 / 16 by decide) x
      _ = x := by ring1
  have realUpper : x < x + 1 / 16 := by
    calc
      x = x + 0 := by ring1
      _ < x + 1 / 16 :=
        Arithmetic.add_lt_add_left_direct (show (0 : Fraction.Rational) < 1 / 16 by decide) x
  exact ⟨realLower.trans realUpper,
    by change -(1 / 16 : Fraction.Rational) < 1 / 16; decide⟩

/-- The fixed-width Gaussian sample square has positive side lengths.

The same positive half-width one sixteenth separates the original
centre from both endpoints in each coordinate. The retained real
and imaginary intervals therefore have positive lengths. -/
public theorem sampleBox_proper (root : Data.Gaussian.Basic.Canonical) :
  (sampleBox root).Proper := by
  have realLower : root.re - 1 / 16 < root.re := by
    calc
      root.re - 1 / 16 < root.re - 0 :=
        Arithmetic.sub_lt_sub_left_direct (show (0 : Fraction.Rational) < 1 / 16 by decide) root.re
      _ = root.re := by ring1
  have realUpper : root.re < root.re + 1 / 16 := by
    calc
      root.re = root.re + 0 := by ring1
      _ < root.re + 1 / 16 :=
        Arithmetic.add_lt_add_left_direct (show (0 : Fraction.Rational) < 1 / 16 by decide) root.re
  have imaginaryLower : root.im - 1 / 16 < root.im := by
    calc
      root.im - 1 / 16 < root.im - 0 :=
        Arithmetic.sub_lt_sub_left_direct (show (0 : Fraction.Rational) < 1 / 16 by decide) root.im
      _ = root.im := by ring1
  have imaginaryUpper : root.im < root.im + 1 / 16 := by
    calc
      root.im = root.im + 0 := by ring1
      _ < root.im + 1 / 16 :=
        Arithmetic.add_lt_add_left_direct (show (0 : Fraction.Rational) < 1 / 16 by decide) root.im
  exact ⟨realLower.trans realUpper, imaginaryLower.trans imaginaryUpper⟩

end Purelib.Geometry.Rational.Box.Square.Centered

namespace Purelib.Geometry.Rational.Box.Square.Centered.Affine

/-- Positive square of radius `r` centered at `c`.

The original centre and nonnegative radius determine four rational
endpoints. The retained ordering certificates compare those same
endpoint values through their nonnegative twice-radius differences. -/
@[expose] public def centeredSquare (c : Data.Gaussian.Basic.Canonical) (r : Fraction.Rational)
    (nonnegative : 0 ≤ r) : Rational.Box where
  xLower := c.re - r
  xUpper := c.re + r
  yLower := c.im - r
  yUpper := c.im + r
  x_valid := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ 2 * r :=
        Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative
      _ = (c.re + r) - (c.re - r) := by ring1
  y_valid := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ 2 * r :=
        Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative
      _ = (c.im + r) - (c.im - r) := by ring1

end Purelib.Geometry.Rational.Box.Square.Centered.Affine

namespace Purelib.Geometry.Rational.Box.Square.Centered

/-- A centered square with positive radius has positive side lengths.

The original radius is strictly positive. Subtracting and adding
that same radius places the retained centre strictly between both
pairs of square endpoints. -/
public theorem centeredSquare_proper (c : Data.Gaussian.Basic.Canonical) {r : Fraction.Rational}
    (positive : 0 < r) : (Box.Square.Centered.Affine.centeredSquare c r positive.le).Proper := by
  have realLower : c.re - r < c.re := by
    calc
      c.re - r < c.re - 0 :=
        Arithmetic.sub_lt_sub_left_direct positive c.re
      _ = c.re := by ring1
  have realUpper : c.re < c.re + r := by
    calc
      c.re = c.re + 0 := by ring1
      _ < c.re + r :=
        Arithmetic.add_lt_add_left_direct positive c.re
  have imaginaryLower : c.im - r < c.im := by
    calc
      c.im - r < c.im - 0 :=
        Arithmetic.sub_lt_sub_left_direct positive c.im
      _ = c.im := by ring1
  have imaginaryUpper : c.im < c.im + r := by
    calc
      c.im = c.im + 0 := by ring1
      _ < c.im + r :=
        Arithmetic.add_lt_add_left_direct positive c.im
  exact ⟨realLower.trans realUpper, imaginaryLower.trans imaginaryUpper⟩

/-- A smaller concentric positive square lies strictly inside a larger one.

The original inner and outer squares share their Gaussian centre.
A strict comparison of their nonnegative radii separates each pair
of corresponding endpoints in the required direction. -/
public theorem centeredSquare_strictInterior_of_lt
    (c : Data.Gaussian.Basic.Canonical) {inner outer : Fraction.Rational}
    (innerNonnegative : 0 <= inner) (outerNonnegative : 0 <= outer)
    (strict : inner < outer) :
    (Box.Square.Centered.Affine.centeredSquare c inner innerNonnegative).StrictInterior
      (Box.Square.Centered.Affine.centeredSquare c outer outerNonnegative) := by
  constructor
  · change c.re - outer < c.re - inner
    have negated := Fraction.Order.Arithmetic.neg_lt_neg_direct strict
    calc
      c.re - outer = -outer + c.re := by ring1
      _ < -inner + c.re :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct negated c.re
      _ = c.re - inner := by ring1
  · change c.re + inner < c.re + outer
    simpa only [Fraction.Field.add_comm] using
      Fraction.Order.Arithmetic.add_lt_add_right_direct strict c.re
  · change c.im - outer < c.im - inner
    have negated := Fraction.Order.Arithmetic.neg_lt_neg_direct strict
    calc
      c.im - outer = -outer + c.im := by ring1
      _ < -inner + c.im :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct negated c.im
      _ = c.im - inner := by ring1
  · change c.im + inner < c.im + outer
    simpa only [Fraction.Field.add_comm] using
      Fraction.Order.Arithmetic.add_lt_add_right_direct strict c.im

end Purelib.Geometry.Rational.Box.Square.Centered

namespace Purelib.Geometry.Rational.Box.Square.Centered.Affine

/-- The centered square has squared diagonal eight times the squared radius.

Each retained coordinate interval has length twice the original
nonnegative radius. Adding the squares of these same two side
lengths gives exactly eight times its square. -/
public theorem centeredSquare_diagonalSq (c : Data.Gaussian.Basic.Canonical) {r : Fraction.Rational}
    (nonnegative : 0 ≤ r) :
    (centeredSquare c r nonnegative).diagonalSq = 8 * r ^ 2 := by
  dsimp only [centeredSquare, Rational.Box.diagonalSq]
  ring1

end Purelib.Geometry.Rational.Box.Square.Centered.Affine

namespace Purelib.Geometry.Rational.Box.Square.Centered

/-- Every point of the centered square is within twice the squared radius of its center.

The original containment witness bounds both coordinate displacements
between the signed radius endpoints. Their two square bounds add
to at most twice the same radius square. -/
public theorem centeredSquare_normSq_sub_center_le
    (c : Data.Gaussian.Basic.Canonical) {r : Fraction.Rational} (nonnegative : 0 ≤ r)
    {z : Data.Gaussian.Basic.Canonical} (inside : (Box.Square.Centered.Affine.centeredSquare c r
      nonnegative).Contains z) :
    Data.Gaussian.Norm.Basic.normSq (z - c) ≤ 2 * r ^ 2 := by
  have xLower : -r ≤ z.re - c.re := by
    have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.1 c.re
    calc
      -r = c.re - r - c.re := by ring1
      _ ≤ z.re - c.re := shifted
  have xUpper : z.re - c.re ≤ r := by
    have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2.1 c.re
    calc
      z.re - c.re ≤ c.re + r - c.re := shifted
      _ = r := by ring1
  have yLower : -r ≤ z.im - c.im := by
    have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2.2.1 c.im
    calc
      -r = c.im - r - c.im := by ring1
      _ ≤ z.im - c.im := shifted
  have yUpper : z.im - c.im ≤ r := by
    have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2.2.2 c.im
    calc
      z.im - c.im ≤ c.im + r - c.im := shifted
      _ = r := by ring1
  have xSquare := Rational.Box.sq_le_endpoint_max
    xLower xUpper
  have ySquare := Rational.Box.sq_le_endpoint_max
    yLower yUpper
  have negSquare : (-r) ^ 2 = r ^ 2 := by ring1
  rw [negSquare, Fraction.Order.Basic.max_self] at xSquare ySquare
  calc
    Data.Gaussian.Norm.Basic.normSq (z - c) = (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 := rfl
    _ ≤ r ^ 2 + r ^ 2 := add_le_add xSquare ySquare
    _ = 2 * r ^ 2 := by ring1

end Purelib.Geometry.Rational.Box.Square.Centered
