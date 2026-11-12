module

public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Coefficient-derived nonzero neighborhoods of the origin -/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Origin

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Gaussian.Basic (Canonical)
open Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rational

/-- The retained half-unit coordinate square used for the same polynomial's finite Lipschitz scan. -/
@[expose] def coordinateBox : Box := Box.symmetric (1/2) (by decide)

set_option genInjectivity false in
/-- An original polynomial's positive coefficient-derived floor near its nonzero origin value.

The exact evaluation quadrance and coordinate-square Lipschitz bound are computed
once. Their retained radius and floor concern this same polynomial, without
isolating roots or supplying a successful numerical floor.
-/
structure Neighborhood (polynomial : CoefficientPolynomial) where
  /-- The actual origin evaluation quadrance. -/ valueNorm : Rational
  /-- The quadrance comes from this original polynomial's exact origin value. -/
  valueNorm_eq : valueNorm = normSq (polynomial.eval 0)
  /-- The exact origin value has positive quadrance. -/ valueNorm_positive : 0 < valueNorm
  /-- The retained coordinate-square Lipschitz multiplier. -/ lipschitz : Rational
  /-- This multiplier is computed from the same original coefficient table. -/
  lipschitz_eq : lipschitz = Bounds.Box.denseLipschitzBound polynomial coordinateBox
  /-- The same retained multiplier is positive. -/ lipschitz_positive : 0 < lipschitz
  /-- The computed safe squared norm around the origin. -/ radiusSq : Rational
  /-- The radius is computed from these same retained scalar observations. -/
  radiusSq_eq : radiusSq = min (1/4) (valueNorm / (8 * lipschitz))
  /-- The computed radius is strictly positive. -/ radiusSq_positive : 0 < radiusSq
  /-- The computed uniform cofactor norm floor. -/ lower : Rational
  /-- The floor reads the same retained exact origin quadrance. -/ lower_eq : lower = valueNorm / 4
  /-- The retained floor is strictly positive. -/ lower_positive : 0 < lower

constructive_injectivity Neighborhood

/-- Compute a safe neighborhood and positive floor from the same polynomial's nonzero exact origin value. -/
def prepare (polynomial : CoefficientPolynomial) (nonzero : polynomial.eval 0 ≠ 0) : Neighborhood polynomial :=
  let valueNorm := normSq (polynomial.eval 0)
  let positive := Norm.Basic.normSq_pos nonzero
  let lipschitz := Bounds.Box.denseLipschitzBound polynomial coordinateBox
  let lipschitzPositive := Bounds.Box.denseLipschitzBound_pos polynomial coordinateBox
  let denominatorPositive := Arithmetic.mul_pos_direct (by decide : (0 : Rational) < 8) lipschitzPositive
  let radiusSq := min (1/4) (valueNorm / (8 * lipschitz))
  let radiusPositive := Basic.lt_min (by decide : (0 : Rational) < 1/4)
    (Field.div_pos_direct positive denominatorPositive)
  let lower := valueNorm / 4
  let lowerPositive := Field.div_pos_direct positive (by decide : (0 : Rational) < 4)
  ⟨valueNorm, rfl, positive, lipschitz, rfl, lipschitzPositive, radiusSq, rfl, radiusPositive,
    lower, rfl, lowerPositive⟩

/-- Every point within the retained squared radius meets the same original polynomial's positive norm floor. -/
theorem Neighborhood.lower_le {polynomial : CoefficientPolynomial} (neighborhood : Neighborhood polynomial)
    {point : Canonical} (near : normSq point ≤ neighborhood.radiusSq) :
    neighborhood.lower ≤ normSq (polynomial.eval point) := by
  have radiusLeQuarter : neighborhood.radiusSq ≤ 1/4 := by
    rewrite [neighborhood.radiusSq_eq]
    exact Basic.min_le_left _ _
  have pointInside : coordinateBox.Contains point := by
    have coordinates := Norm.Bounds.coordinate_bounds_of_normSq_le
      (r := (1/2 : Rational)) (by decide) (by
        have square : (1/2 : Rational) ^ 2 = 1/4 := by decide
        rewrite [square]
        exact near.trans radiusLeQuarter)
    exact coordinates
  have zeroInside : coordinateBox.Contains (0 : Canonical) := by decide
  have variation := Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound polynomial zeroInside pointInside
  rewrite [Purelib.Data.Gaussian.Basic.zero_sub, Norm.Basic.normSq_neg,
    ← neighborhood.lipschitz_eq] at variation
  have radiusBound : neighborhood.radiusSq ≤ neighborhood.valueNorm / (8 * neighborhood.lipschitz) := by
    rewrite [neighborhood.radiusSq_eq]
    exact Basic.min_le_right _ _
  have denominatorPositive := Arithmetic.mul_pos_direct (by decide : (0 : Rational) < 8)
    neighborhood.lipschitz_positive
  have paid := (Field.le_div_iff_pos denominatorPositive).mp radiusBound
  have scaled : neighborhood.lipschitz * neighborhood.radiusSq ≤ neighborhood.valueNorm / 8 := by
    apply (Field.le_div_iff_pos (by decide : (0 : Rational) < 8)).mpr
    have identity : neighborhood.lipschitz * neighborhood.radiusSq * 8 =
        neighborhood.radiusSq * (8 * neighborhood.lipschitz) := by ring0
    rewrite [identity]
    exact paid
  have movement : normSq (polynomial.eval 0 - polynomial.eval point) ≤ neighborhood.valueNorm / 8 :=
    variation.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct near
      neighborhood.lipschitz_positive.le).trans scaled)
  have half := Norm.Bounds.half_normSq_sub_le_normSq_sub
    (polynomial.eval 0) (polynomial.eval 0 - polynomial.eval point)
  have difference : polynomial.eval 0 - (polynomial.eval 0 - polynomial.eval point) =
      polynomial.eval point := by ring0
  rewrite [difference, ← neighborhood.valueNorm_eq] at half
  have translated := Arithmetic.add_le_add_direct
    (Basic.le_refl (neighborhood.valueNorm / 2)) (Arithmetic.neg_le_neg_direct movement)
  change neighborhood.valueNorm / 2 - neighborhood.valueNorm / 8 ≤
    neighborhood.valueNorm / 2 - normSq (polynomial.eval 0 - polynomial.eval point) at translated
  have fraction := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (by decide : (1 / 4 : Rational) ≤ 1 / 2 - 1 / 8) neighborhood.valueNorm_positive.le
  have exactFractions : (1 / 4 : Rational) * neighborhood.valueNorm = neighborhood.valueNorm / 4 := by
    rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
    ring0
  have exactDifference : ((1 / 2 : Rational) - 1 / 8) * neighborhood.valueNorm =
      neighborhood.valueNorm / 2 - neighborhood.valueNorm / 8 := by
    rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
    ring0
  rewrite [exactFractions, exactDifference] at fraction
  rewrite [neighborhood.lower_eq]
  exact fraction.trans (translated.trans half)

end Purelib.Polynomial.Dense.Gaussian.Bounds.Origin

end
