module

public import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Geometry.Rational.Box.Outside.Sum
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Computed signed squares around nonzero Gaussian centres

Half the largest signed coordinate gives a positive rational half-width.
The original dominant coordinate excludes both zero and the opposite centre,
with exact retained side margins. Those same original coordinates bound the
centre norm and the sum of any two readings in its signed square.
-/

public section

namespace Purelib.Geometry.Rational.Box.Square.Centered

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- The computed largest magnitude among the original two signed centre coordinates. -/
@[expose] def coordinateMaximum (center : Canonical) : Fraction.Rational :=
  max (max center.re (-center.re)) (max center.im (-center.im))

/-- All four original signed coordinates are bounded by their same computed maximum. -/
theorem coordinate_bounds (center : Canonical) :
    center.re ≤ coordinateMaximum center ∧ -center.re ≤ coordinateMaximum center ∧
      center.im ≤ coordinateMaximum center ∧ -center.im ≤ coordinateMaximum center :=
  ⟨(Fraction.Order.Basic.le_max_left _ _).trans (Fraction.Order.Basic.le_max_left _ _),
    (Fraction.Order.Basic.le_max_right _ _).trans (Fraction.Order.Basic.le_max_left _ _),
    (Fraction.Order.Basic.le_max_left _ _).trans (Fraction.Order.Basic.le_max_right _ _),
    (Fraction.Order.Basic.le_max_right _ _).trans (Fraction.Order.Basic.le_max_right _ _)⟩

/-- The computed signed-coordinate maximum is nonnegative. -/
private theorem coordinateMaximum_nonnegative (center : Canonical) : 0 ≤ coordinateMaximum center := by
  have bounds := coordinate_bounds center
  have doubled := Arithmetic.add_le_add_direct bounds.1 bounds.2.1
  rewrite [show center.re + -center.re = (0 : Fraction.Rational) by ring1] at doubled
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := 2) _ (by decide +kernel)
  calc
    (0 : Fraction.Rational) * 2 = 0 := Fraction.Field.zero_mul_direct _
    _ ≤ coordinateMaximum center + coordinateMaximum center := doubled
    _ = coordinateMaximum center * 2 := by ring1

/-- A nonzero original centre has a strictly positive computed signed-coordinate maximum. -/
private theorem coordinateMaximum_positive (center : Canonical) (nonzero : center ≠ 0) :
    0 < coordinateMaximum center := by
  have nonnegative := coordinateMaximum_nonnegative center
  refine ⟨nonnegative, ?_⟩
  intro nonpositive
  have zero := Fraction.Order.Basic.le_antisymm _ _ nonpositive nonnegative
  have bounds := coordinate_bounds center
  have realLower := Arithmetic.neg_le_neg_direct bounds.2.1
  have imaginaryLower := Arithmetic.neg_le_neg_direct bounds.2.2.2
  rewrite [zero, show -(0 : Fraction.Rational) = 0 by decide +kernel, neg_neg] at realLower imaginaryLower
  rewrite [zero] at bounds
  exact nonzero (Basic.ext (Fraction.Order.Basic.le_antisymm _ _ bounds.1 realLower)
    (Fraction.Order.Basic.le_antisymm _ _ bounds.2.2.1 imaginaryLower))

/-- The original centre norm is at most twice the square of its computed signed-coordinate maximum. -/
private theorem normSq_le_maximum (center : Canonical) :
    Norm.Basic.normSq center ≤ 2 * coordinateMaximum center ^ 2 := by
  have bounds := coordinate_bounds center
  have realLower := Arithmetic.neg_le_neg_direct bounds.2.1
  have imaginaryLower := Arithmetic.neg_le_neg_direct bounds.2.2.2
  rewrite [neg_neg] at realLower imaginaryLower
  exact (Arithmetic.add_le_add_direct (Bounds.Square.sq_le_sq_of_bounds realLower bounds.1)
    (Bounds.Square.sq_le_sq_of_bounds imaginaryLower bounds.2.2.1)).trans_eq (by ring1)

set_option genInjectivity false in
/-- Two original outside sides with their exact opposite-centre and zero margins on one signed square. -/
private structure Sides (center : Canonical) (radius : Fraction.Rational) (positive : 0 < radius) where
  /-- The original opposite-centre exclusion witness. -/
  opposite : (Affine.centeredSquare center radius positive.le).OutsideSide (-center)
  /-- Its exact retained side margin. -/ opposite_margin : opposite.margin = 9 * radius ^ 2
  /-- The original zero exclusion witness on the same square. -/
  zero : (Affine.centeredSquare center radius positive.le).OutsideSide 0
  /-- Its exact retained side margin. -/ zero_margin : zero.margin = radius ^ 2

constructive_injectivity Sides

/-- The selected positive real coordinate gives both original left-side exclusions. -/
private def realPositive (center : Canonical) (radius : Fraction.Rational) (positive : 0 < radius)
    (selected : center.re = 2 * radius) : Sides center radius positive := by
  have oppositeLess : (-center).re < (Affine.centeredSquare center radius positive.le).xLower := by
    apply Arithmetic.lt_of_sub_pos_direct
    change 0 < (center.re - radius) - -center.re
    rewrite [selected, show ((2 * radius - radius) - -(2 * radius)) = 3 * radius by ring1]
    exact Arithmetic.mul_pos_direct (by decide +kernel) positive
  have zeroLess : (0 : Canonical).re < (Affine.centeredSquare center radius positive.le).xLower := by
    change (0 : Fraction.Rational) < center.re - radius
    rewrite [selected, show 2 * radius - radius = radius by ring1]
    exact positive
  exact
    { opposite := .left oppositeLess
      opposite_margin := by change ((center.re - radius) - -center.re) ^ 2 = _; rewrite [selected]; ring1
      zero := .left zeroLess
      zero_margin := by change (center.re - radius - 0) ^ 2 = _; rewrite [selected]; ring1 }

/-- The selected negative real coordinate gives both original right-side exclusions. -/
private def realNegative (center : Canonical) (radius : Fraction.Rational) (positive : 0 < radius)
    (selected : -center.re = 2 * radius) : Sides center radius positive := by
  have coordinate : center.re = -(2 * radius) := by
    have reversed := congrArg (fun value : Fraction.Rational => -value) selected
    rewrite [neg_neg] at reversed
    exact reversed
  have oppositeLess : (Affine.centeredSquare center radius positive.le).xUpper < (-center).re := by
    apply Arithmetic.lt_of_sub_pos_direct
    change 0 < -center.re - (center.re + radius)
    rewrite [coordinate, show -( -(2 * radius)) - (-(2 * radius) + radius) = 3 * radius by ring1]
    exact Arithmetic.mul_pos_direct (by decide +kernel) positive
  have zeroLess : (Affine.centeredSquare center radius positive.le).xUpper < (0 : Canonical).re := by
    apply Arithmetic.lt_of_sub_pos_direct
    change 0 < 0 - (center.re + radius)
    rewrite [coordinate, show 0 - (-(2 * radius) + radius) = radius by ring1]
    exact positive
  exact
    { opposite := .right oppositeLess
      opposite_margin := by change (-center.re - (center.re + radius)) ^ 2 = _; rewrite [coordinate]; ring1
      zero := .right zeroLess
      zero_margin := by change (0 - (center.re + radius)) ^ 2 = _; rewrite [coordinate]; ring1 }

/-- The selected positive imaginary coordinate gives both original bottom-side exclusions. -/
private def imaginaryPositive (center : Canonical) (radius : Fraction.Rational) (positive : 0 < radius)
    (selected : center.im = 2 * radius) : Sides center radius positive := by
  have oppositeLess : (-center).im < (Affine.centeredSquare center radius positive.le).yLower := by
    apply Arithmetic.lt_of_sub_pos_direct
    change 0 < (center.im - radius) - -center.im
    rewrite [selected, show ((2 * radius - radius) - -(2 * radius)) = 3 * radius by ring1]
    exact Arithmetic.mul_pos_direct (by decide +kernel) positive
  have zeroLess : (0 : Canonical).im < (Affine.centeredSquare center radius positive.le).yLower := by
    change (0 : Fraction.Rational) < center.im - radius
    rewrite [selected, show 2 * radius - radius = radius by ring1]
    exact positive
  exact
    { opposite := .bottom oppositeLess
      opposite_margin := by change ((center.im - radius) - -center.im) ^ 2 = _; rewrite [selected]; ring1
      zero := .bottom zeroLess
      zero_margin := by change (center.im - radius - 0) ^ 2 = _; rewrite [selected]; ring1 }

/-- The selected negative imaginary coordinate gives both original top-side exclusions. -/
private def imaginaryNegative (center : Canonical) (radius : Fraction.Rational) (positive : 0 < radius)
    (selected : -center.im = 2 * radius) : Sides center radius positive := by
  have coordinate : center.im = -(2 * radius) := by
    have reversed := congrArg (fun value : Fraction.Rational => -value) selected
    rewrite [neg_neg] at reversed
    exact reversed
  have oppositeLess : (Affine.centeredSquare center radius positive.le).yUpper < (-center).im := by
    apply Arithmetic.lt_of_sub_pos_direct
    change 0 < -center.im - (center.im + radius)
    rewrite [coordinate, show -( -(2 * radius)) - (-(2 * radius) + radius) = 3 * radius by ring1]
    exact Arithmetic.mul_pos_direct (by decide +kernel) positive
  have zeroLess : (Affine.centeredSquare center radius positive.le).yUpper < (0 : Canonical).im := by
    apply Arithmetic.lt_of_sub_pos_direct
    change 0 < 0 - (center.im + radius)
    rewrite [coordinate, show 0 - (-(2 * radius) + radius) = radius by ring1]
    exact positive
  exact
    { opposite := .top oppositeLess
      opposite_margin := by change (-center.im - (center.im + radius)) ^ 2 = _; rewrite [coordinate]; ring1
      zero := .top zeroLess
      zero_margin := by change (0 - (center.im + radius)) ^ 2 = _; rewrite [coordinate]; ring1 }

set_option genInjectivity false in
/-- A computed original signed square separating zero and the opposite of its nonzero centre. -/
structure Separation (center : Canonical) where
  /-- The computed positive original half-width. -/ radius : Fraction.Rational
  /-- The retained half-width is strictly positive. -/ positive : 0 < radius
  /-- Twice that same half-width reads the original signed-coordinate maximum. -/
  radius_eq : 2 * radius = coordinateMaximum center
  /-- The original centre norm is bounded by this same retained radius. -/
  norm_le : Norm.Basic.normSq center ≤ 8 * radius ^ 2
  /-- The opposite original centre's explicit strict outside side. -/
  opposite : (Affine.centeredSquare center radius positive.le).OutsideSide (-center)
  /-- The opposite-root gap uses the same original retained radius. -/
  opposite_margin : opposite.margin = 9 * radius ^ 2
  /-- The original zero exclusion witness on this identical square. -/
  zero : (Affine.centeredSquare center radius positive.le).OutsideSide 0
  /-- The zero gap uses the same original retained radius. -/ zero_margin : zero.margin = radius ^ 2

constructive_injectivity Separation

namespace Separation

/-- Compute the signed square and both original outside sides from the nonzero centre's actual coordinates. -/
def build (center : Canonical) (nonzero : center ≠ 0) : Separation center := by
  let radius := coordinateMaximum center / 2
  have positive : 0 < radius :=
    Fraction.Order.Field.div_pos_direct (coordinateMaximum_positive center nonzero) (by decide +kernel)
  have doubled : 2 * radius = coordinateMaximum center := by
    rewrite [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
  have normBound : Norm.Basic.normSq center ≤ 8 * radius ^ 2 := by
    have bound := normSq_le_maximum center
    rewrite [← doubled] at bound
    exact bound.trans_eq (by ring1)
  have sides : Sides center radius positive := by
    by_cases realLargest : max center.im (-center.im) ≤ max center.re (-center.re)
    · have largest : coordinateMaximum center = max center.re (-center.re) :=
        Fraction.Order.Basic.max_eq_left realLargest
      by_cases realPositive : -center.re ≤ center.re
      · have selected : center.re = 2 * radius :=
          (Fraction.Order.Basic.max_eq_left realPositive).symm.trans (largest.symm.trans doubled.symm)
        exact Centered.realPositive center radius positive selected
      · have selected : -center.re = 2 * radius :=
          (Fraction.Order.Basic.max_eq_right
            (Arithmetic.lt_of_not_ge_direct realPositive).le).symm.trans
              (largest.symm.trans doubled.symm)
        exact realNegative center radius positive selected
    · have largest : coordinateMaximum center = max center.im (-center.im) :=
        Fraction.Order.Basic.max_eq_right (Arithmetic.lt_of_not_ge_direct realLargest).le
      by_cases imaginaryPositive : -center.im ≤ center.im
      · have selected : center.im = 2 * radius :=
          (Fraction.Order.Basic.max_eq_left imaginaryPositive).symm.trans (largest.symm.trans doubled.symm)
        exact Centered.imaginaryPositive center radius positive selected
      · have selected : -center.im = 2 * radius :=
          (Fraction.Order.Basic.max_eq_right
            (Arithmetic.lt_of_not_ge_direct imaginaryPositive).le).symm.trans
              (largest.symm.trans doubled.symm)
        exact imaginaryNegative center radius positive selected
  exact
    { radius := radius
      positive := positive
      radius_eq := doubled
      norm_le := normBound
      opposite := sides.opposite
      opposite_margin := sides.opposite_margin
      zero := sides.zero
      zero_margin := sides.zero_margin }

/-- Two readings in the original signed square retain their exact four-radius-squared sum separation. -/
theorem sum_normSq_lower {center first last : Canonical} (separation : Separation center)
    (firstInside : (Affine.centeredSquare center separation.radius separation.positive.le).Contains first)
    (lastInside : (Affine.centeredSquare center separation.radius separation.positive.le).Contains last) :
    4 * separation.radius ^ 2 ≤ Norm.Basic.normSq (first + last) := by
  have lower := separation.zero.sum_normSq_lower firstInside lastInside
  rewrite [separation.zero_margin] at lower
  exact lower

end Separation

end Purelib.Geometry.Rational.Box.Square.Centered
