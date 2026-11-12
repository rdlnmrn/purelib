module

public import Purelib.Polynomial.Clearance.Circle
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Geometry.Rational.Circle
public import Purelib.Geometry.Rational.Box.Hull
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Coefficient-computed rational collars

A positive whole-circle residual margin and one original box Horner fold
determine an explicit positive quadrance-defect width. A rational point inside
that collar cannot also have polynomial residual below one eighth of the margin.
-/

namespace Purelib.Polynomial.Clearance.Circle

open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.Geometry.Rational.Circle (boundingBox inside_boundingBox Retraction)
open Dense.Gaussian
open Basic.CanonicalCoefficients (CoefficientPolynomial)
open Rat.Fraction (Rational)
open Rat.Fraction.Order

/-- A coefficient-computed collar gives a positive residual bound near the original unit circle. -/
public theorem collar_lower {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial)
    (ambient : Box) (point : Gaussian.Basic.Canonical) (inside : ambient.Contains point) :
    let bounding := Box.Hull.hull ambient boundingBox
    let lipschitz := Bounds.Box.denseLipschitzBound polynomial bounding
    let width := min 1 (clearance.bound / (16 * lipschitz))
    (point.normSq - 1) ^ 2 ≤ width ^ 2 →
      clearance.bound / 8 < Gaussian.Norm.Basic.normSq (polynomial.eval point) := by
  let bounding := Box.Hull.hull ambient boundingBox
  let lipschitz := Bounds.Box.denseLipschitzBound polynomial bounding
  let width := min 1 (clearance.bound / (16 * lipschitz))
  change (point.normSq - 1) ^ 2 ≤ width ^ 2 →
    clearance.bound / 8 < Gaussian.Norm.Basic.normSq (polynomial.eval point)
  intro near
  have lipschitzPositive : 0 < lipschitz := Bounds.Box.denseLipschitzBound_pos polynomial bounding
  have scalePositive : 0 < 16 * lipschitz := Arithmetic.mul_pos_direct (by decide) lipschitzPositive
  have widthPositive : 0 < width :=
    Rat.Fraction.Order.Basic.lt_min (by decide) (Field.div_pos_direct clearance.positive scalePositive)
  have widthSquared : width ^ 2 ≤ width := by
    have bound := Arithmetic.mul_le_mul_of_nonneg_left_direct
      (show width ≤ 1 from Rat.Fraction.Order.Basic.min_le_left _ _) widthPositive.le
    simpa only [pow_two, Rat.Fraction.Field.mul_one_direct] using bound
  let retraction := Retraction.prepare point
  have pointInside : bounding.Contains point := Box.Hull.hull_contains_left inside
  have circleInside : bounding.Contains retraction.point :=
    Box.Hull.hull_contains_right (inside_boundingBox retraction.unit)
  have distance : Gaussian.Norm.Basic.normSq (point - retraction.point) ≤ width := by
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    exact (retraction.distance_le.trans near).trans widthSquared
  have functionDistance : Gaussian.Norm.Basic.normSq
      (polynomial.eval point - polynomial.eval retraction.point) ≤ lipschitz * width :=
    (Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound polynomial pointInside circleInside).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct distance lipschitzPositive.le)
  have payment : width * (16 * lipschitz) ≤ clearance.bound :=
    (Field.le_div_iff_pos scalePositive).mp (Rat.Fraction.Order.Basic.min_le_right _ _)
  have functionBound : Gaussian.Norm.Basic.normSq
      (polynomial.eval point - polynomial.eval retraction.point) ≤ clearance.bound / 16 := by
    apply (Field.le_div_iff_pos (show (0 : Rational) < 16 by decide)).mpr
    calc
      Gaussian.Norm.Basic.normSq (polynomial.eval point - polynomial.eval retraction.point) * 16 ≤
          (lipschitz * width) * 16 :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct functionDistance (by decide)
      _ = width * (16 * lipschitz) := by ring1
      _ ≤ clearance.bound := payment
  by_cases small : Gaussian.Norm.Basic.normSq (polynomial.eval point) ≤ clearance.bound / 8
  · have triangle := Gaussian.Norm.Bounds.normSq_add_le_two
      (polynomial.eval point) (-(polynomial.eval point - polynomial.eval retraction.point))
    have sumIdentity : polynomial.eval point + -(polynomial.eval point - polynomial.eval retraction.point) =
        polynomial.eval retraction.point := by ring1
    rw [sumIdentity, Gaussian.Norm.Basic.normSq_neg] at triangle
    have upper : Gaussian.Norm.Basic.normSq (polynomial.eval retraction.point) ≤
        2 * (clearance.bound / 8 + clearance.bound / 16) :=
      triangle.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct small functionBound) (by decide))
    have strict : 2 * (clearance.bound / 8 + clearance.bound / 16) < clearance.bound := by
      apply Arithmetic.lt_of_mul_lt_mul_right_direct (c := (16 : Rational)) _ (by decide)
      calc
        (2 * (clearance.bound / 8 + clearance.bound / 16)) * 16 =
            4 * ((clearance.bound / 8) * 8) + 2 * ((clearance.bound / 16) * 16) := by ring1
        _ = 4 * clearance.bound + 2 * clearance.bound := by
          rw [Rat.Fraction.Field.div_mul_cancel_of_ne _ 8 (by decide),
            Rat.Fraction.Field.div_mul_cancel_of_ne _ 16 (by decide)]
        _ = 6 * clearance.bound := by ring1
        _ < 16 * clearance.bound :=
          Arithmetic.mul_lt_mul_of_pos_right_direct (by decide) clearance.positive
        _ = clearance.bound * 16 := Rat.Fraction.Field.mul_comm _ _
    exact (lt_irrefl clearance.bound
      ((clearance.lower retraction.point retraction.unit).trans_lt (upper.trans_lt strict))).elim
  · exact lt_of_not_ge small

set_option genInjectivity false in
/-- An original polynomial's retained coefficient-computed rational collar.

The original residual certificate remains an index. The enclosing box, shared
value/slope fold and derived Lipschitz payment are cached once with their exact
construction equations. -/
public structure Collar {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial) (ambient : Box) where
  /-- The box containing both the original ambient box and unit circle. -/ bounding : Box
  /-- The enclosing box is the original coordinatewise hull. -/ bounding_eq :
    bounding = Box.Hull.hull ambient boundingBox
  /-- The once-computed original polynomial value/slope fold. -/ bounds : Polynomial.Bounds.Horner
  /-- The fold uses this original polynomial and retained enclosing box. -/ bounds_eq :
    bounds = Bounds.Box.denseHornerNormBounds polynomial bounding
  /-- The positive squared-distance multiplier. -/ lipschitz : Rational
  /-- The multiplier projects this same retained slope bound. -/ lipschitz_eq : lipschitz = max 1 bounds.slope
  /-- The positive norm-defect width of the rational collar. -/ width : Rational
  /-- The width pays the original residual margin and same retained multiplier. -/ width_eq :
    width = min 1 (clearance.bound / (16 * lipschitz))
  /-- The retained collar width is strictly positive. -/ positive : 0 < width

constructive_injectivity Collar

namespace Collar

/-- Compute the original enclosing box and coefficient fold once, then retain their explicit collar width. -/
@[expose] public def prepare {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial) (ambient : Box) :
    Collar clearance ambient :=
  let bounding := Box.Hull.hull ambient boundingBox
  let bounds := Bounds.Box.denseHornerNormBounds polynomial bounding
  let lipschitz := max 1 bounds.slope
  { bounding, bounding_eq := rfl, bounds, bounds_eq := rfl, lipschitz, lipschitz_eq := rfl
    width := min 1 (clearance.bound / (16 * lipschitz)), width_eq := rfl
    positive := Rat.Fraction.Order.Basic.lt_min (by decide)
      (Field.div_pos_direct clearance.positive
        (Arithmetic.mul_pos_direct (by decide)
          ((show (0 : Rational) < 1 by decide).trans_le (Rat.Fraction.Order.Basic.le_max_left _ _)))) }

/-- The same retained collar bounds original polynomial residuals at every near-boundary point. -/
public theorem near_lower {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial} {ambient : Box}
    (collar : Collar clearance ambient) {point : Gaussian.Basic.Canonical} (inside : ambient.Contains point)
    (near : (point.normSq - 1) ^ 2 ≤ collar.width ^ 2) :
    clearance.bound / 8 < Gaussian.Norm.Basic.normSq (polynomial.eval point) := by
  rw [collar.width_eq, collar.lipschitz_eq, collar.bounds_eq, collar.bounding_eq] at near
  exact collar_lower clearance ambient point inside near

/-- Small residual forces an exact positive squared norm-defect gap from the whole circle. -/
public theorem small_residual_away {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {ambient : Box} (collar : Collar clearance ambient) {point : Gaussian.Basic.Canonical}
    (inside : ambient.Contains point)
    (small : Gaussian.Norm.Basic.normSq (polynomial.eval point) < clearance.bound / 8) :
    collar.width ^ 2 < (point.normSq - 1) ^ 2 := by
  apply lt_of_not_ge
  intro near
  exact (lt_irrefl (clearance.bound / 8) (collar.near_lower inside near |>.trans small)).elim

end Collar
end Purelib.Polynomial.Clearance.Circle
