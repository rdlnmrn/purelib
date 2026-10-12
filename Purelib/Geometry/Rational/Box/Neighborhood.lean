module

public import Purelib.Geometry.Rational.Box.Interior
public import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Data.Rat.Interval.Bisection
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Proper rational neighbourhoods inside retained boxes

A strictly interior Gaussian rational and a positive squared-distance
budget determine one explicit centred square. Its positive radius pays
both the source-displacement budget and all four original side gaps.
-/

public section

namespace Purelib.Geometry.Rational.Box

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Geometry.Rational.Box

/-- Read the midpoints of the original real and imaginary box intervals as one Gaussian rational. -/
@[expose] def midpoint (box : Box) : Gaussian.Basic.Canonical :=
  ⟨Interval.Bisection.midpoint ⟨box.xLower, box.xUpper, box.x_valid⟩,
    Interval.Bisection.midpoint ⟨box.yLower, box.yUpper, box.y_valid⟩⟩

/-- The midpoint of every proper box lies strictly between all four original sides. -/
theorem midpoint_strictContains {box : Box} (proper : box.Proper) : box.StrictContains box.midpoint := by
  have midpointBounds : ∀ lower upper : Fraction.Rational, lower < upper →
      lower < (lower + upper) / 2 ∧ (lower + upper) / 2 < upper := by
    intro lower upper strict
    constructor
    · apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := (2 : Fraction.Rational)) _ (by decide)
      rewrite [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
      calc
        lower * 2 = lower + lower := by ring1
        _ < lower + upper := Fraction.Order.Arithmetic.add_lt_add_left_direct strict _
    · apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := (2 : Fraction.Rational)) _ (by decide)
      rewrite [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
      calc
        lower + upper < upper + upper := Fraction.Order.Arithmetic.add_lt_add_right_direct strict _
        _ = upper * 2 := by ring1
  have realBounds := midpointBounds box.xLower box.xUpper proper.1
  have imaginaryBounds := midpointBounds box.yLower box.yUpper proper.2
  exact ⟨realBounds.1, realBounds.2, imaginaryBounds.1, imaginaryBounds.2⟩

namespace Neighborhood

/-- Compute a positive radius paying the distance request and the original coordinate-side clearance. -/
@[expose] def radius (outer : Box) (center : Gaussian.Basic.Canonical) (distanceSq : Fraction.Rational) :
    Fraction.Rational :=
  min 1 (min (distanceSq * (1 / 4)) (Interior.strictCoordinateGap outer center * (1 / 2)))

/-- A strictly interior centre and positive distance request produce a positive radius. -/
theorem radius_pos {outer : Box} {center : Gaussian.Basic.Canonical}
    (strict : outer.StrictContains center) {distanceSq : Fraction.Rational} (positive : 0 < distanceSq) :
    0 < radius outer center distanceSq :=
  Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Basic.lt_min
      (Fraction.Order.Arithmetic.mul_pos_direct positive (by decide))
      (Fraction.Order.Arithmetic.mul_pos_direct (Interior.strictCoordinateGap_pos strict) (by decide)))

/-- Construct the centred rational square with its exact computed radius and endpoint-order certificates. -/
@[expose] def innerBox (outer : Box) (center : Gaussian.Basic.Canonical)
    (strict : outer.StrictContains center) (distanceSq : Fraction.Rational) (positive : 0 < distanceSq) : Box :=
  Square.Centered.Affine.centeredSquare center (radius outer center distanceSq) (radius_pos strict positive).le

/-- The computed neighbourhood has strictly positive width and height. -/
theorem innerBox_proper {outer : Box} {center : Gaussian.Basic.Canonical}
    (strict : outer.StrictContains center) {distanceSq : Fraction.Rational} (positive : 0 < distanceSq) :
    (innerBox outer center strict distanceSq positive).Proper :=
  Square.Centered.centeredSquare_proper center (radius_pos strict positive)

/-- The retained centre lies strictly inside its computed positive neighbourhood. -/
theorem innerBox_strictContains_center {outer : Box} {center : Gaussian.Basic.Canonical}
    (strict : outer.StrictContains center) {distanceSq : Fraction.Rational} (positive : 0 < distanceSq) :
    (innerBox outer center strict distanceSq positive).StrictContains center := by
  have selectedPositive := radius_pos strict positive
  have lower : ∀ coordinate : Fraction.Rational, coordinate - radius outer center distanceSq < coordinate := by
    intro coordinate
    calc
      coordinate - radius outer center distanceSq < coordinate - 0 :=
        Fraction.Order.Arithmetic.sub_lt_sub_left_direct selectedPositive coordinate
      _ = coordinate := by ring1
  have upper : ∀ coordinate : Fraction.Rational, coordinate < coordinate + radius outer center distanceSq := by
    intro coordinate
    calc
      coordinate = coordinate + 0 := by ring1
      _ < coordinate + radius outer center distanceSq :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct selectedPositive coordinate
  exact ⟨lower center.re, upper center.re, lower center.im, upper center.im⟩

/-- The computed neighbourhood lies strictly inside the original retained box. -/
theorem innerBox_strictInterior {outer : Box} {center : Gaussian.Basic.Canonical}
    (strict : outer.StrictContains center) {distanceSq : Fraction.Rational} (positive : 0 < distanceSq) :
    (innerBox outer center strict distanceSq positive).StrictInterior outer := by
  let gap := Interior.strictCoordinateGap outer center
  let selected := radius outer center distanceSq
  have gapPositive : 0 < gap := Interior.strictCoordinateGap_pos strict
  have radiusLeHalf : selected ≤ gap * (1 / 2) :=
    (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)
  have halfStrict : gap * (1 / 2) < gap := by
    calc
      gap * (1 / 2) < gap * 1 :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct gapPositive (by decide)
      _ = gap := Fraction.Field.mul_one_direct _
  have radiusLess : selected < gap := radiusLeHalf.trans_lt halfStrict
  have leftGap : gap ≤ center.re - outer.xLower := Fraction.Order.Basic.min_le_left _ _
  have rightGap : gap ≤ outer.xUpper - center.re :=
    (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)
  have bottomGap : gap ≤ center.im - outer.yLower :=
    (Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))
  have topGap : gap ≤ outer.yUpper - center.im :=
    (Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _))
  refine ⟨?_, ?_, ?_, ?_⟩
  · change outer.xLower < center.re - selected
    calc
      outer.xLower = center.re - (center.re - outer.xLower) := by ring1
      _ < center.re - selected :=
        Fraction.Order.Arithmetic.sub_lt_sub_left_direct (radiusLess.trans_le leftGap) _
  · change center.re + selected < outer.xUpper
    calc
      center.re + selected < center.re + (outer.xUpper - center.re) :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct (radiusLess.trans_le rightGap) _
      _ = outer.xUpper := by ring1
  · change outer.yLower < center.im - selected
    calc
      outer.yLower = center.im - (center.im - outer.yLower) := by ring1
      _ < center.im - selected :=
        Fraction.Order.Arithmetic.sub_lt_sub_left_direct (radiusLess.trans_le bottomGap) _
  · change center.im + selected < outer.yUpper
    calc
      center.im + selected < center.im + (outer.yUpper - center.im) :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct (radiusLess.trans_le topGap) _
      _ = outer.yUpper := by ring1

/-- Every sample within the selected coordinate-radius square remains strictly inside the retained outer box. -/
theorem strictContains_of_distance_le {outer : Box} {center sample : Gaussian.Basic.Canonical}
    (strict : outer.StrictContains center) {distanceSq : Fraction.Rational} (positive : 0 < distanceSq)
    (near : Gaussian.Norm.Basic.normSq (sample - center) ≤ radius outer center distanceSq ^ 2) :
    outer.StrictContains sample := by
  have inside : (innerBox outer center strict distanceSq positive).Contains sample :=
    Square.Centered.centeredBox_contains_of_normSq_sub_le (radius_pos strict positive).le near
  have nested := innerBox_strictInterior strict positive
  exact ⟨nested.left.trans_le inside.1, inside.2.1.trans_lt nested.right,
    nested.bottom.trans_le inside.2.2.1, inside.2.2.2.trans_lt nested.top⟩

/-- The selected radius makes every neighbourhood displacement strictly smaller than the requested quadrance. -/
private theorem two_mul_radius_sq_lt {outer : Box} {center : Gaussian.Basic.Canonical}
    (strict : outer.StrictContains center) {distanceSq : Fraction.Rational} (positive : 0 < distanceSq) :
    2 * radius outer center distanceSq ^ 2 < distanceSq := by
  let selected := radius outer center distanceSq
  have radiusNonnegative : 0 ≤ selected := (radius_pos strict positive).le
  have radiusLeOne : selected ≤ 1 := Fraction.Order.Basic.min_le_left _ _
  have squareLe : selected ^ 2 ≤ selected := by
    calc
      selected ^ 2 = selected * selected := by ring1
      _ ≤ selected * 1 := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusLeOne radiusNonnegative
      _ = selected := Fraction.Field.mul_one_direct _
  have quarterLe : selected ≤ distanceSq * (1 / 4) :=
    (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)
  calc
    2 * selected ^ 2 ≤ 2 * selected :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareLe (by decide)
    _ ≤ 2 * (distanceSq * (1 / 4)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct quarterLe (by decide)
    _ = distanceSq * (2 * (1 / 4)) := by ring1
    _ = distanceSq * (1 / 2) := by
      rewrite [show (2 * (1 / 4) : Fraction.Rational) = 1 / 2 by decide]
      rfl
    _ < distanceSq * 1 := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct positive (by decide)
    _ = distanceSq := Fraction.Field.mul_one_direct _

/-- The squared diagonal of the computed neighbourhood is strictly below four times its distance request. -/
theorem innerBox_diagonalSq_lt {outer : Box} {center : Gaussian.Basic.Canonical}
    (strict : outer.StrictContains center) {distanceSq : Fraction.Rational} (positive : 0 < distanceSq) :
    (innerBox outer center strict distanceSq positive).diagonalSq < 4 * distanceSq := by
  rewrite [innerBox, Square.Centered.Affine.centeredSquare_diagonalSq]
  calc
    8 * radius outer center distanceSq ^ 2 = 4 * (2 * radius outer center distanceSq ^ 2) := by ring1
    _ < 4 * distanceSq :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
        (two_mul_radius_sq_lt strict positive)

/-- Every sample in the computed neighbourhood pays the exact requested squared-displacement budget. -/
theorem innerBox_distance_lt {outer : Box} {center : Gaussian.Basic.Canonical}
    (strict : outer.StrictContains center) {distanceSq : Fraction.Rational} (positive : 0 < distanceSq)
    {sample : Gaussian.Basic.Canonical} (inside : (innerBox outer center strict distanceSq positive).Contains sample) :
    Gaussian.Norm.Basic.normSq (sample - center) < distanceSq :=
  (Square.Centered.centeredSquare_normSq_sub_center_le center (radius_pos strict positive).le inside).trans_lt
    (two_mul_radius_sq_lt strict positive)

end Neighborhood

end Purelib.Geometry.Rational.Box
