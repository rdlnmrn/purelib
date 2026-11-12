module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Tactic.Ring

/-!
# Actual base-coordinate budgets for the retained radial conic family

The original cubic base reads the exact radial ellipse axes. On scales from
one to two, both axes are bounded by five quarters. The resulting quantified
base and cofactor time budgets retain the original rational quarter charts and
pay their actual squared displacement; no geometric path is replaced by a word
or affine endpoint segment.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Algebra.Field

/-- The exact shorter axis of the radial conic coordinate ellipse. -/
@[expose] def shortAxis (scale : Fraction.Rational) : Fraction.Rational := (scale - scale⁻¹) * (1 / 2)

/-- The exact longer axis of the radial conic coordinate ellipse. -/
@[expose] def longAxis (scale : Fraction.Rational) : Fraction.Rational := (scale + scale⁻¹) * (1 / 2)

/-- The retained original Gaussian reading mapped to its exact base-coordinate ellipse direction. -/
@[expose] def baseDirection (scale : Fraction.Rational) (value : Canonical) : Canonical :=
  ⟨longAxis scale * value.re, shortAxis scale * value.im⟩

/-- The original radial base direction satisfies its exact doubled conic-coordinate readback. -/
private theorem baseDirection_two (scale : Fraction.Rational) (value : Canonical) :
    baseDirection scale value * 2 = Scale.scale scale value + Scale.scale scale⁻¹ (Basic.conj value) := by
  have halfTwo : (1 / 2 : Fraction.Rational) * 2 = 1 := by decide +kernel
  apply Basic.ext
  · simp only [Basic.mul_re, Basic.add_re, Scale.scale_re, baseDirection, longAxis, shortAxis, Basic.conj,
      show (2 : Canonical).re = 2 by decide +kernel, show (2 : Canonical).im = 0 by decide +kernel]
    calc
      _ = ((scale + scale⁻¹) * value.re) * ((1 / 2) * 2) := by ring1
      _ = (scale + scale⁻¹) * value.re := by
        rewrite [halfTwo, Fraction.Field.mul_one_direct]
        rfl
      _ = _ := by ring1
  · simp only [Basic.mul_im, Basic.add_im, Scale.scale_im, baseDirection, longAxis, shortAxis, Basic.conj,
      show (2 : Canonical).re = 2 by decide +kernel, show (2 : Canonical).im = 0 by decide +kernel]
    calc
      _ = ((scale - scale⁻¹) * value.im) * ((1 / 2) * 2) := by ring1
      _ = (scale - scale⁻¹) * value.im := by
        rewrite [halfTwo, Fraction.Field.mul_one_direct]
        rfl
      _ = _ := by ring1

/-- The original radial cubic base retains the collision center, half-gap and computed exact ellipse direction. -/
theorem point_base (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational) (original : UnitVertex)
    (positive : 0 < scale) :
    (point site parameter scale original positive).base =
      center site parameter + halfGap site parameter * baseDirection scale original.value := by
  have abscissa : (point site parameter scale original positive).abscissa =
      halfGap site parameter * baseDirection scale original.value := by
    apply ExplicitField.eq_of_mul_eq_mul_right (by decide +kernel : (2 : Canonical) ≠ 0)
    calc
      _ = (point site parameter scale original positive).minus + (point site parameter scale original positive).plus :=
        ExplicitField.div_mul_cancel _ (by decide +kernel)
      _ = (halfGap site parameter * baseDirection scale original.value) * 2 := by
        rewrite [point_plus, point_minus, Scale.scale_mul_right, Scale.scale_mul_right]
        calc
          _ = halfGap site parameter *
              (Scale.scale scale original.value + Scale.scale scale⁻¹ (Basic.conj original.value)) := by ring1
          _ = halfGap site parameter * (baseDirection scale original.value * 2) :=
            congrArg (fun value => halfGap site parameter * value) (baseDirection_two scale original.value).symm
          _ = _ := by ring1
  rewrite [Point.base, abscissa]
  rfl

/-- Both actual ellipse axes have the computed five-quarter budget throughout the original radial interval. -/
theorem axes_bounds (scale : Fraction.Rational) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2) :
    0 ≤ shortAxis scale ∧ shortAxis scale ≤ longAxis scale ∧ longAxis scale ≤ 5 / 4 := by
  have inverseUpper : scale⁻¹ ≤ 1 := by
    have result := Fraction.Order.Field.inv_le_inv_of_pos_direct (by decide +kernel : (0 : Fraction.Rational) < 1) lower
    rewrite [show (1 : Fraction.Rational)⁻¹ = 1 by decide +kernel] at result
    exact result
  have shortNonnegative : 0 ≤ shortAxis scale := Arithmetic.mul_nonneg_direct
    (Arithmetic.sub_nonneg_direct (inverseUpper.trans lower)) (by decide +kernel)
  have difference : longAxis scale - shortAxis scale = scale⁻¹ := by
    calc
      _ = scale⁻¹ * ((1 / 2) * 2) := by unfold longAxis shortAxis; ring1
      _ = scale⁻¹ := by
        rewrite [show ((1 / 2) * 2 : Fraction.Rational) = 1 by decide +kernel, Fraction.Field.mul_one_direct]
        rfl
  have axesOrdered : shortAxis scale ≤ longAxis scale := by
    apply Arithmetic.le_of_sub_nonneg_direct
    rewrite [difference]
    exact (Fraction.Order.Field.inv_pos_direct positive).le
  have negative : scale - 2 ≤ 0 := by
    have result := Arithmetic.sub_le_sub_right_direct upper 2
    rewrite [show (2 - 2 : Fraction.Rational) = 0 by decide +kernel] at result
    exact result
  have factor : 0 ≤ 2 * scale - 1 := by
    have doubled := Arithmetic.mul_le_mul_of_nonneg_left_direct lower
      (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
    rewrite [Fraction.Field.mul_one_direct] at doubled
    exact Arithmetic.sub_nonneg_direct
      ((by decide +kernel : (1 : Fraction.Rational) ≤ 2).trans doubled)
  have paid := Arithmetic.mul_le_mul_of_nonneg_right_direct negative factor
  rewrite [Fraction.Field.zero_mul_direct] at paid
  have quadratic : 2 * (scale ^ 2 + 1) ≤ 5 * scale := by
    calc
      _ = (scale - 2) * (2 * scale - 1) + 5 * scale := by ring1
      _ ≤ 0 + 5 * scale := Arithmetic.add_le_add_right_direct paid (5 * scale)
      _ = _ := Fraction.Field.zero_add _
  have longFour : longAxis scale * 4 = 2 * (scale + scale⁻¹) := by
    calc
      _ = (scale + scale⁻¹) * ((1 / 2) * 4) := by unfold longAxis; ring1
      _ = (scale + scale⁻¹) * 2 := congrArg (fun value => (scale + scale⁻¹) * value)
        (by decide +kernel : ((1 / 2) * 4 : Fraction.Rational) = 2)
      _ = _ := by ring1
  have longUpper : longAxis scale ≤ 5 / 4 := by
    apply Arithmetic.le_of_mul_le_mul_right_direct (c := 4) _ (by decide +kernel)
    apply Arithmetic.le_of_mul_le_mul_right_direct (c := scale) _ positive
    calc
      _ = 2 * (scale + scale⁻¹) * scale := congrArg (fun value => value * scale) longFour
      _ = 2 * (scale ^ 2 + scale⁻¹ * scale) := by ring1
      _ = 2 * (scale ^ 2 + 1) := by
        rewrite [Fraction.Field.inv_mul_cancel scale positive.ne']
        rfl
      _ ≤ 5 * scale := quadratic
      _ = ((5 / 4) * 4) * scale := congrArg (fun value => value * scale)
        (by decide +kernel : ((5 / 4) * 4 : Fraction.Rational) = 5).symm
  exact ⟨shortNonnegative, axesOrdered, longUpper⟩

/-- Both actual squared ellipse axes have the same computed twenty-five-sixteenth budget. -/
theorem axis_squares (scale : Fraction.Rational) (positive : 0 < scale)
    (lower : 1 ≤ scale) (upper : scale ≤ 2) :
    (shortAxis scale) ^ 2 ≤ 25 / 16 ∧ (longAxis scale) ^ 2 ≤ 25 / 16 := by
  have axes := axes_bounds scale positive lower upper
  have longSquare := Arithmetic.pow_le_pow_direct (axes.1.trans axes.2.1) axes.2.2 2
  rewrite [show (5 / 4 : Fraction.Rational) ^ 2 = 25 / 16 by decide +kernel] at longSquare
  exact ⟨(Arithmetic.pow_le_pow_direct axes.1 axes.2.1 2).trans longSquare, longSquare⟩

/-- The exact base ellipse map retains the original ordered Gaussian difference. -/
theorem baseDirection_sub (scale : Fraction.Rational) (first last : Canonical) :
    baseDirection scale (first - last) = baseDirection scale first - baseDirection scale last := by
  apply Basic.ext
  · change longAxis scale * (first.re - last.re) = longAxis scale * first.re - longAxis scale * last.re
    ring1
  · change shortAxis scale * (first.im - last.im) = shortAxis scale * first.im - shortAxis scale * last.im
    ring1

/-- The original base ellipse map pays its actual Gaussian squared displacement with the computed axis budget. -/
theorem baseDirection_normSq_le (scale : Fraction.Rational) (value : Canonical)
    (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2) :
    Norm.Basic.normSq (baseDirection scale value) ≤ (25 / 16) * Norm.Basic.normSq value := by
  have axes := axis_squares scale positive lower upper
  change (longAxis scale * value.re) ^ 2 + (shortAxis scale * value.im) ^ 2 ≤
    (25 / 16) * (value.re ^ 2 + value.im ^ 2)
  calc
    _ = (longAxis scale) ^ 2 * value.re ^ 2 + (shortAxis scale) ^ 2 * value.im ^ 2 := by ring1
    _ ≤ (25 / 16) * value.re ^ 2 + (25 / 16) * value.im ^ 2 :=
      Arithmetic.add_le_add_direct
        (Arithmetic.mul_le_mul_of_nonneg_right_direct axes.2
          (Arithmetic.sq_nonneg_direct value.re))
        (Arithmetic.mul_le_mul_of_nonneg_right_direct axes.1
          (Arithmetic.sq_nonneg_direct value.im))
    _ = _ := by ring1

/-- The original radial base displacement pays the actual retained unit-direction displacement. -/
theorem base_distance_le (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (first last : UnitVertex) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2) :
    Norm.Basic.normSq ((point site parameter scale first positive).base -
        (point site parameter scale last positive).base) ≤
      (25 / 16) * Norm.Basic.normSq (halfGap site parameter * first.value - halfGap site parameter * last.value) := by
  have difference : (point site parameter scale first positive).base -
      (point site parameter scale last positive).base =
      halfGap site parameter * baseDirection scale (first.value - last.value) := by
    rewrite [point_base, point_base, baseDirection_sub]
    ring1
  have originalDifference : halfGap site parameter * first.value - halfGap site parameter * last.value =
      halfGap site parameter * (first.value - last.value) := by ring1
  rewrite [difference, originalDifference, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
  calc
    _ ≤ Norm.Basic.normSq (halfGap site parameter) *
        ((25 / 16) * Norm.Basic.normSq (first.value - last.value)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (baseDirection_normSq_le scale (first.value - last.value) positive lower upper) (Norm.Basic.normSq_nonneg _)
    _ = _ := by ring1

/-- Every original rational radial quarter has its internally derived finite squared base-distance budget. -/
theorem quarter_base_distance_le (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (first last : Fraction.Rational) :
    Norm.Basic.normSq ((point site parameter scale (Waist.direction quarter first) positive).base -
        (point site parameter scale (Waist.direction quarter last) positive).base) ≤
      (25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2 := by
  have mapped := base_distance_le site parameter scale (Waist.direction quarter first)
    (Waist.direction quarter last) positive lower upper
  have original := Waist.quarter_distance_le site parameter quarter first last
  change Norm.Basic.normSq (halfGap site parameter * (Waist.direction quarter first).value -
    halfGap site parameter * (Waist.direction quarter last).value) ≤
      4 * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2 at original
  calc
    _ ≤ (25 / 16) * Norm.Basic.normSq (halfGap site parameter * (Waist.direction quarter first).value -
        halfGap site parameter * (Waist.direction quarter last).value) := mapped
    _ ≤ (25 / 16) * (4 * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct original (by decide +kernel)
    _ = (25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2 := by
      calc
        _ = ((25 / 16) * 4) * (Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2) := by ring1
        _ = (25 / 4) * (Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2) :=
          congrArg (fun value => value * (Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2))
            (by decide +kernel : ((25 / 16) * 4 : Fraction.Rational) = 25 / 4)
        _ = _ := by ring1

/-- The original radial-quarter cofactor parameter at the actual retained cubic base point. -/
@[expose] def cofactor (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (time : Fraction.Rational) : Canonical :=
  (unitPolynomial site).eval (point site parameter scale (Waist.direction quarter time) positive).base

/-- Every original radial-quarter cofactor path has the same internally derived finite time-variation budget. -/
theorem cofactor_distance_le (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (first last : Fraction.Rational) :
    Norm.Basic.normSq (cofactor site parameter scale quarter positive first -
        cofactor site parameter scale quarter positive last) ≤
      (25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2 := by
  have difference : cofactor site parameter scale quarter positive first -
      cofactor site parameter scale quarter positive last =
      (point site parameter scale (Waist.direction quarter first) positive).base -
        (point site parameter scale (Waist.direction quarter last) positive).base := by
    unfold cofactor
    rewrite [unitPolynomial, Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate_eval,
      Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate_eval]
    ring1
  rewrite [difference]
  exact quarter_base_distance_le site parameter scale quarter positive lower upper first last

/-- The original conic ordinate and base directions have the exact positive-axis scalar product on a unit direction.

The real part uses their two original ellipse axes in opposite order.
Their product factors through the same retained unit squared-norm identity;
no division or independent root selection occurs.
-/
theorem ordinateDirection_mul_conj_baseDirection_re (scale : Fraction.Rational) (original : UnitVertex) :
    (ordinateDirection scale original * Basic.conj (baseDirection scale original.value)).re =
      shortAxis scale * longAxis scale := by
  have unit := original.unit
  change original.value.re ^ 2 + original.value.im ^ 2 = 1 at unit
  change ((scale - scale⁻¹) * (1 / 2) * original.value.re) *
      (longAxis scale * original.value.re) -
    ((scale + scale⁻¹) * (1 / 2) * original.value.im) *
      (-(shortAxis scale * original.value.im)) = _
  change (shortAxis scale * original.value.re) * (longAxis scale * original.value.re) -
    (longAxis scale * original.value.im) * (-(shortAxis scale * original.value.im)) = _
  calc
    _ = shortAxis scale * longAxis scale * (original.value.re ^ 2 + original.value.im ^ 2) := by ring1
    _ = shortAxis scale * longAxis scale * 1 := congrArg (fun value => shortAxis scale * longAxis scale * value) unit
    _ = _ := Fraction.Field.mul_one_direct _

/-- At radial scale two, the same original ordinate/base scalar product is exactly fifteen sixteenths. -/
theorem parallel_ordinate_base_re (original : UnitVertex) :
    (ordinateDirection 2 original * Basic.conj (baseDirection 2 original.value)).re = 15 / 16 :=
  (ordinateDirection_mul_conj_baseDirection_re 2 original).trans
    (by unfold shortAxis longAxis; decide +kernel)

/-- The product of the actual scale-two ordinate and base quadrances is at most two hundred eighty-nine over
two hundred fifty-six.

The same unit-direction equation reduces the product to its exact constant
part plus the product of the two squared components. Their squared difference
is nonnegative, supplying the sharp finite bound without extracting roots.
-/
theorem parallel_ordinate_base_product_bound (original : UnitVertex) :
    Norm.Basic.normSq (ordinateDirection 2 original) * Norm.Basic.normSq (baseDirection 2 original.value) ≤
      (289 / 256 : Fraction.Rational) := by
  have unit := original.unit
  change original.value.re ^ 2 + original.value.im ^ 2 = 1 at unit
  have components : original.value.re ^ 2 * original.value.im ^ 2 ≤ (1 / 4 : Fraction.Rational) := by
    apply Arithmetic.le_of_mul_le_mul_right_direct (c := 4) _ (by decide +kernel)
    calc
      _ = (original.value.re ^ 2 + original.value.im ^ 2) ^ 2 -
          (original.value.re ^ 2 - original.value.im ^ 2) ^ 2 := by ring1
      _ ≤ (original.value.re ^ 2 + original.value.im ^ 2) ^ 2 - 0 :=
        Arithmetic.sub_le_sub_left_direct
          (Arithmetic.sq_nonneg_direct (original.value.re ^ 2 - original.value.im ^ 2)) _
      _ = (original.value.re ^ 2 + original.value.im ^ 2) ^ 2 := by ring1
      _ = 1 := by rewrite [unit]; decide +kernel
      _ = (1 / 4 : Fraction.Rational) * 4 := by decide +kernel
  have exactProduct : Norm.Basic.normSq (ordinateDirection 2 original) *
      Norm.Basic.normSq (baseDirection 2 original.value) =
      (225 / 256 : Fraction.Rational) * (original.value.re ^ 2 + original.value.im ^ 2) ^ 2 +
        original.value.re ^ 2 * original.value.im ^ 2 := by
    change (((3 / 4 : Fraction.Rational) * original.value.re) ^ 2 +
      ((5 / 4 : Fraction.Rational) * original.value.im) ^ 2) *
      (((5 / 4 : Fraction.Rational) * original.value.re) ^ 2 +
        ((3 / 4 : Fraction.Rational) * original.value.im) ^ 2) = _
    calc
      _ = (((3 / 4 : Fraction.Rational) ^ 2) * (5 / 4) ^ 2) *
          (original.value.re ^ 2 + original.value.im ^ 2) ^ 2 +
          (((3 / 4 : Fraction.Rational) ^ 2 - (5 / 4) ^ 2) ^ 2) *
            (original.value.re ^ 2 * original.value.im ^ 2) := by ring1
      _ = _ := by
        rewrite [show (((3 / 4 : Fraction.Rational) ^ 2) * (5 / 4) ^ 2) = 225 / 256 by decide +kernel,
          show (((3 / 4 : Fraction.Rational) ^ 2 - (5 / 4) ^ 2) ^ 2) = 1 by decide +kernel,
          Fraction.Field.one_mul]
        rfl
  rewrite [exactProduct, unit]
  calc
    _ ≤ (225 / 256 : Fraction.Rational) * 1 ^ 2 + 1 / 4 :=
      Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) components
    _ = _ := by decide +kernel

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial
