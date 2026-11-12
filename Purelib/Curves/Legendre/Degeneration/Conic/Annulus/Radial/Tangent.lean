module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Coordinates
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Tangent
import Purelib.Data.Gaussian.Components.Projection
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Actual radial conic tangents with finite quadratic remainders

The original quarter velocity passes through the same exact radial ellipse
map as the original cubic base. Its purely imaginary logarithmic velocity
interchanges the original component axes, giving the actual normalized
ordinate factor without division by that ordinate. The original finite circle
remainder and paid ellipse budget quantify every rational chart increment.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle

/-- The original base ellipse map reads the same retained embedded Gaussian components. -/
private theorem baseDirection_components (scale : Fraction.Rational) (value : Canonical) :
    baseDirection scale value =
      Scale.scale (longAxis scale) (Components.Projection.realPart value) +
        Scale.scale (shortAxis scale) (Components.Projection.imaginaryPart value) := by
  apply Basic.ext
  · change longAxis scale * value.re = longAxis scale * value.re + shortAxis scale * 0
    ring1
  · change shortAxis scale * value.im = longAxis scale * 0 + shortAxis scale * value.im
    ring1

/-- A retained real Gaussian scalar commutes with the original component ellipse map. -/
private theorem baseDirection_mul_real (scale : Fraction.Rational) (value scalar : Canonical)
    (real : scalar.im = 0) :
    baseDirection scale (value * scalar) = baseDirection scale value * scalar := by
  rewrite [baseDirection_components, baseDirection_components,
    Components.Projection.realPart_mul_real _ _ real, Components.Projection.imaginaryPart_mul_real _ _ real,
    Scale.scale_mul_product, Scale.scale_mul_product]
  ring1

/-- The original imaginary logarithmic factor interchanges the actual radial ellipse axes. -/
private theorem baseDirection_mul_imaginary (scale : Fraction.Rational)
    (original : UnitVertex) (scalar : Canonical) (imaginary : scalar.re = 0) :
    baseDirection scale (original.value * scalar) = ordinateDirection scale original * scalar := by
  apply Basic.ext
  · change longAxis scale * (original.value.re * scalar.re - original.value.im * scalar.im) =
      ((scale - scale⁻¹) * (1 / 2)) * original.value.re * scalar.re -
        ((scale + scale⁻¹) * (1 / 2)) * original.value.im * scalar.im
    rewrite [imaginary]
    unfold longAxis
    ring1
  · change shortAxis scale * (original.value.re * scalar.im + original.value.im * scalar.re) =
      ((scale - scale⁻¹) * (1 / 2)) * original.value.re * scalar.im +
        ((scale + scale⁻¹) * (1 / 2)) * original.value.im * scalar.re
    rewrite [imaginary]
    unfold shortAxis
    ring1

/-- The original cubic base velocity retains its original labelled half-gap, radial scale and oriented quarter. -/
@[expose] def baseVelocity (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (time : Fraction.Rational) : Canonical :=
  halfGap site parameter * baseDirection scale (Waist.Tangent.directionVelocity quarter time)

/-- The actual radial base velocity is its original normalized ordinate times the same chart logarithmic velocity.

The identity holds for every positive radial scale and rational chart time.
It preserves the original conic point and applies at the scale-one branch
points as well as throughout the regular scale-two parallel circuit.
-/
theorem baseVelocity_eq_ordinate_mul (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (time : Fraction.Rational) :
    baseVelocity site parameter scale quarter time =
      (point site parameter scale (Waist.direction quarter time) positive).ordinate *
        Stereographic.Tangent.logarithmicVelocity time := by
  unfold baseVelocity
  rewrite [Waist.Tangent.directionVelocity_eq,
    baseDirection_mul_imaginary _ _ _ (Stereographic.Tangent.logarithmicVelocity_real time), point_ordinate]
  ring1

/-- The original retained oriented unit-direction velocity has the same global squared norm bound four. -/
private theorem directionVelocity_normSq_le (quarter : UnitCircuitQuarter) (time : Fraction.Rational) :
    Norm.Basic.normSq (Waist.Tangent.directionVelocity quarter time) ≤ 4 := by
  rewrite [Waist.Tangent.directionVelocity_eq, Norm.Basic.normSq_mul,
    (Waist.direction quarter time).unit, Fraction.Field.one_mul]
  exact Stereographic.Tangent.logarithmicVelocity_normSq_le time

/-- Every actual radial base velocity has its internally paid original half-gap squared norm budget. -/
theorem baseVelocity_normSq_le (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (time : Fraction.Rational) :
    Norm.Basic.normSq (baseVelocity site parameter scale quarter time) ≤
      (25 / 4) * Norm.Basic.normSq (halfGap site parameter) := by
  unfold baseVelocity
  rewrite [Norm.Basic.normSq_mul]
  calc
    _ ≤ Norm.Basic.normSq (halfGap site parameter) *
        ((25 / 16) * Norm.Basic.normSq (Waist.Tangent.directionVelocity quarter time)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (baseDirection_normSq_le scale (Waist.Tangent.directionVelocity quarter time) positive lower upper)
        (Norm.Basic.normSq_nonneg _)
    _ ≤ Norm.Basic.normSq (halfGap site parameter) * ((25 / 16) * 4) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct (directionVelocity_normSq_le quarter time)
          (by decide +kernel)) (Norm.Basic.normSq_nonneg _)
    _ = _ := by
      rewrite [show ((25 / 16) * 4 : Fraction.Rational) = 25 / 4 by decide +kernel]
      exact Fraction.Field.mul_comm _ _

/-- Every finite original radial-quarter base increment has a quantified quadratic tangent remainder.

The bound is on the actual squared Gaussian displacement after subtracting
the retained time increment times the displayed original base velocity. Its
fourth-power remainder keeps the original half-gap and radial admission.
-/
theorem base_remainder_normSq_le (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (time delta : Fraction.Rational) :
    Norm.Basic.normSq ((point site parameter scale (Waist.direction quarter (time + delta)) positive).base -
        (point site parameter scale (Waist.direction quarter time) positive).base -
        Stereographic.Tangent.increment delta * baseVelocity site parameter scale quarter time) ≤
      (25 / 4) * Norm.Basic.normSq (halfGap site parameter) * delta ^ 4 := by
  let remainder := (Waist.direction quarter (time + delta)).value - (Waist.direction quarter time).value -
    Stereographic.Tangent.increment delta * Waist.Tangent.directionVelocity quarter time
  have realScalar : baseDirection scale
      (Stereographic.Tangent.increment delta * Waist.Tangent.directionVelocity quarter time) =
      Stereographic.Tangent.increment delta * baseDirection scale (Waist.Tangent.directionVelocity quarter time) := by
    rewrite [Basic.mul_comm (Stereographic.Tangent.increment delta) (Waist.Tangent.directionVelocity quarter time),
      baseDirection_mul_real _ _ _ (by rfl)]
    exact Basic.mul_comm _ _
  have difference : (point site parameter scale (Waist.direction quarter (time + delta)) positive).base -
      (point site parameter scale (Waist.direction quarter time) positive).base -
      Stereographic.Tangent.increment delta * baseVelocity site parameter scale quarter time =
        halfGap site parameter * baseDirection scale remainder := by
    unfold remainder baseVelocity
    rewrite [point_base, point_base, baseDirection_sub, baseDirection_sub, realScalar]
    ring1
  rewrite [difference, Norm.Basic.normSq_mul]
  calc
    _ ≤ Norm.Basic.normSq (halfGap site parameter) * ((25 / 16) * Norm.Basic.normSq remainder) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (baseDirection_normSq_le scale remainder positive lower upper) (Norm.Basic.normSq_nonneg _)
    _ ≤ Norm.Basic.normSq (halfGap site parameter) * ((25 / 16) * (4 * delta ^ 4)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Waist.Tangent.direction_remainder_normSq_le quarter time delta) (by decide +kernel))
        (Norm.Basic.normSq_nonneg _)
    _ = _ := by
      calc
        _ = ((25 / 16) * 4) * Norm.Basic.normSq (halfGap site parameter) * delta ^ 4 := by ring1
        _ = _ := by
          rewrite [show ((25 / 16) * 4 : Fraction.Rational) = 25 / 4 by decide +kernel]
          rfl

/-- The original ordinate ellipse acts linearly on arbitrary Gaussian directions. -/
private def ordinateMap (scale : Fraction.Rational) (value : Canonical) : Canonical :=
  ⟨shortAxis scale * value.re, longAxis scale * value.im⟩

/-- Subtraction commutes with the original ordinate ellipse map. -/
private theorem ordinateMap_sub (scale : Fraction.Rational) (first last : Canonical) :
    ordinateMap scale (first - last) = ordinateMap scale first - ordinateMap scale last := by
  apply Basic.ext
  · change shortAxis scale * (first.re - last.re) = shortAxis scale * first.re - shortAxis scale * last.re
    ring1
  · change longAxis scale * (first.im - last.im) = longAxis scale * first.im - longAxis scale * last.im
    ring1

/-- A real Gaussian scalar commutes with the original ordinate ellipse map. -/
private theorem ordinateMap_mul_real (scale : Fraction.Rational) (value scalar : Canonical)
    (real : scalar.im = 0) :
    ordinateMap scale (value * scalar) = ordinateMap scale value * scalar := by
  apply Basic.ext
  · change shortAxis scale * (value.re * scalar.re - value.im * scalar.im) =
      shortAxis scale * value.re * scalar.re - longAxis scale * value.im * scalar.im
    rewrite [real]
    ring1
  · change longAxis scale * (value.re * scalar.im + value.im * scalar.re) =
      shortAxis scale * value.re * scalar.im + longAxis scale * value.im * scalar.re
    rewrite [real]
    ring1

/-- An imaginary logarithmic factor changes the original ordinate ellipse into the original base ellipse. -/
private theorem ordinateMap_mul_imaginary (scale : Fraction.Rational)
    (original : UnitVertex) (scalar : Canonical) (imaginary : scalar.re = 0) :
    ordinateMap scale (original.value * scalar) = baseDirection scale original.value * scalar := by
  apply Basic.ext
  · change shortAxis scale * (original.value.re * scalar.re - original.value.im * scalar.im) =
      longAxis scale * original.value.re * scalar.re - shortAxis scale * original.value.im * scalar.im
    rewrite [imaginary]
    ring1
  · change longAxis scale * (original.value.re * scalar.im + original.value.im * scalar.re) =
      longAxis scale * original.value.re * scalar.im + shortAxis scale * original.value.im * scalar.re
    rewrite [imaginary]
    ring1

/-- The original squared-axis budgets bound the ordinate map on any Gaussian direction. -/
private theorem ordinateMap_normSq_le (scale : Fraction.Rational) (value : Canonical)
    (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2) :
    Norm.Basic.normSq (ordinateMap scale value) ≤ (25 / 16) * Norm.Basic.normSq value := by
  have axes := axis_squares scale positive lower upper
  change (shortAxis scale * value.re) ^ 2 + (longAxis scale * value.im) ^ 2 ≤
    (25 / 16) * (value.re ^ 2 + value.im ^ 2)
  calc
    _ = shortAxis scale ^ 2 * value.re ^ 2 + longAxis scale ^ 2 * value.im ^ 2 := by ring1
    _ ≤ (25 / 16) * value.re ^ 2 + (25 / 16) * value.im ^ 2 :=
      Arithmetic.add_le_add_direct
        (Arithmetic.mul_le_mul_of_nonneg_right_direct axes.1
          (Arithmetic.sq_nonneg_direct _))
        (Arithmetic.mul_le_mul_of_nonneg_right_direct axes.2
          (Arithmetic.sq_nonneg_direct _))
    _ = _ := by ring1

/-- The original normalized ordinate velocity retains its labelled half-gap, radial scale and oriented quarter. -/
@[expose] def ordinateVelocity (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (time : Fraction.Rational) : Canonical :=
  halfGap site parameter *
    ⟨shortAxis scale * (Waist.Tangent.directionVelocity quarter time).re,
      longAxis scale * (Waist.Tangent.directionVelocity quarter time).im⟩

/-- The ordinate velocity is the original conic abscissa times the same chart logarithmic velocity. -/
theorem ordinateVelocity_eq_abscissa_mul (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (time : Fraction.Rational) :
    ordinateVelocity site parameter scale quarter time =
      (halfGap site parameter * baseDirection scale (Waist.direction quarter time).value) *
        Stereographic.Tangent.logarithmicVelocity time := by
  change halfGap site parameter * ordinateMap scale (Waist.Tangent.directionVelocity quarter time) = _
  rewrite [Waist.Tangent.directionVelocity_eq,
    ordinateMap_mul_imaginary _ _ _ (Stereographic.Tangent.logarithmicVelocity_real time)]
  ring1

/-- Every actual normalized ordinate velocity has the same internally paid half-gap squared-norm budget. -/
theorem ordinateVelocity_normSq_le (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (time : Fraction.Rational) :
    Norm.Basic.normSq (ordinateVelocity site parameter scale quarter time) ≤
      (25 / 4) * Norm.Basic.normSq (halfGap site parameter) := by
  change Norm.Basic.normSq (halfGap site parameter *
    ordinateMap scale (Waist.Tangent.directionVelocity quarter time)) ≤ _
  rewrite [Norm.Basic.normSq_mul]
  calc
    _ ≤ Norm.Basic.normSq (halfGap site parameter) *
        ((25 / 16) * Norm.Basic.normSq (Waist.Tangent.directionVelocity quarter time)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (ordinateMap_normSq_le scale (Waist.Tangent.directionVelocity quarter time) positive lower upper)
        (Norm.Basic.normSq_nonneg _)
    _ ≤ Norm.Basic.normSq (halfGap site parameter) * ((25 / 16) * 4) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct
          (directionVelocity_normSq_le quarter time) (by decide +kernel)) (Norm.Basic.normSq_nonneg _)
    _ = _ := by
      rewrite [show ((25 / 16) * 4 : Fraction.Rational) = 25 / 4 by decide +kernel]
      exact Fraction.Field.mul_comm _ _

/-- Every original normalized ordinate increment has a quantified quadratic tangent remainder.

The exact source and target conic ordinates retain their original radial scale
and oriented quarter. The original finite direction remainder and squared-axis
budget give an explicit fourth-power chart-increment bound, without observing
a numerical primitive or replacing either endpoint.
-/
theorem ordinate_remainder_normSq_le (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (time delta : Fraction.Rational) :
    Norm.Basic.normSq ((point site parameter scale (Waist.direction quarter (time + delta)) positive).ordinate -
        (point site parameter scale (Waist.direction quarter time) positive).ordinate -
        Stereographic.Tangent.increment delta * ordinateVelocity site parameter scale quarter time) ≤
      (25 / 4) * Norm.Basic.normSq (halfGap site parameter) * delta ^ 4 := by
  let remainder := (Waist.direction quarter (time + delta)).value - (Waist.direction quarter time).value -
    Stereographic.Tangent.increment delta * Waist.Tangent.directionVelocity quarter time
  have realScalar : ordinateMap scale
      (Stereographic.Tangent.increment delta * Waist.Tangent.directionVelocity quarter time) =
      Stereographic.Tangent.increment delta * ordinateMap scale (Waist.Tangent.directionVelocity quarter time) := by
    rewrite [Basic.mul_comm (Stereographic.Tangent.increment delta) (Waist.Tangent.directionVelocity quarter time),
      ordinateMap_mul_real _ _ _ (by rfl)]
    exact Basic.mul_comm _ _
  have difference : (point site parameter scale (Waist.direction quarter (time + delta)) positive).ordinate -
      (point site parameter scale (Waist.direction quarter time) positive).ordinate -
      Stereographic.Tangent.increment delta * ordinateVelocity site parameter scale quarter time =
        halfGap site parameter * ordinateMap scale remainder := by
    rewrite [point_ordinate, point_ordinate]
    change halfGap site parameter * ordinateMap scale (Waist.direction quarter (time + delta)).value -
      halfGap site parameter * ordinateMap scale (Waist.direction quarter time).value -
      Stereographic.Tangent.increment delta *
        (halfGap site parameter * ordinateMap scale (Waist.Tangent.directionVelocity quarter time)) = _
    unfold remainder
    rewrite [ordinateMap_sub, ordinateMap_sub, realScalar]
    ring1
  rewrite [difference, Norm.Basic.normSq_mul]
  calc
    _ ≤ Norm.Basic.normSq (halfGap site parameter) * ((25 / 16) * Norm.Basic.normSq remainder) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (ordinateMap_normSq_le scale remainder positive lower upper) (Norm.Basic.normSq_nonneg _)
    _ ≤ Norm.Basic.normSq (halfGap site parameter) * ((25 / 16) * (4 * delta ^ 4)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Waist.Tangent.direction_remainder_normSq_le quarter time delta) (by decide +kernel))
        (Norm.Basic.normSq_nonneg _)
    _ = _ := by
      calc
        _ = ((25 / 16) * 4) * Norm.Basic.normSq (halfGap site parameter) * delta ^ 4 := by ring1
        _ = _ := by
          rewrite [show ((25 / 16) * 4 : Fraction.Rational) = 25 / 4 by decide +kernel]
          rfl

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent
