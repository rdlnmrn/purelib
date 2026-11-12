module
public import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
public import Purelib.Approximation.Rational.Uniform.Modulus
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Effective uniform variation of finite rational polynomials

The original finite dense coefficient list computes its squared Horner slope
bound on the rational unit interval. A positive rational factor above that
bound provides an explicit source modulus without square roots or an oracle.
-/

public section

namespace Purelib.Polynomial.Dense.Rational.Bounds.Uniform

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial.Dense.Rational

/-- Add one to the original polynomial's computed unit-interval squared slope bound. -/
@[expose] def slopeFactor (polynomial : Basic.CoordinatePolynomial) : Fraction.Rational :=
  Lipschitz.denseEvalSqLipschitzBound polynomial ⟨0, 1, by decide⟩ + 1

/-- The finite polynomial slope factor is strictly positive, including for a zero slope. -/
theorem slopeFactor_pos (polynomial : Basic.CoordinatePolynomial) : 0 < slopeFactor polynomial := by
  have nonnegative := (Lipschitz.denseHornerSqBounds_nonneg polynomial ⟨0, 1, by decide⟩).2
  have shifted := Arithmetic.add_le_add_right_direct nonnegative 1
  rw [Fraction.Field.zero_add] at shifted
  have oneLe : (1 : Fraction.Rational) ≤ slopeFactor polynomial := shifted
  exact (by decide : (0 : Fraction.Rational) < 1).trans_le oneLe

/-- The original squared slope bound is bounded by the square of its positive factor. -/
theorem slope_le_factor_sq (polynomial : Basic.CoordinatePolynomial) :
    Lipschitz.denseEvalSqLipschitzBound polynomial ⟨0, 1, by decide⟩ ≤ (slopeFactor polynomial) ^ 2 := by
  let slope := Lipschitz.denseEvalSqLipschitzBound polynomial ⟨0, 1, by decide⟩
  have nonnegative : 0 ≤ slope := (Lipschitz.denseHornerSqBounds_nonneg polynomial ⟨0, 1, by decide⟩).2
  have square := Arithmetic.sq_nonneg_direct slope
  have extra := Arithmetic.add_le_add_direct
    (Arithmetic.add_le_add_direct square nonnegative) (by decide : (0 : Fraction.Rational) ≤ 1)
  have zero : (0 : Fraction.Rational) + 0 + 0 = 0 := by decide
  rw [zero] at extra
  have shifted := Arithmetic.add_le_add_right_direct extra slope
  change slope ≤ (slope + 1) ^ 2
  calc
    slope = 0 + slope := by ring1
    _ ≤ (slope ^ 2 + slope + 1) + slope := shifted
    _ = (slope + 1) ^ 2 := by ring1

/-- The computed factor turns a rational distance request into two directed polynomial variation bounds.

Both points belong to the rational unit interval. The finite Horner slope
certificate bounds squared differences, and the positive factor converts the
square estimate to the requested unsquared rational variation. -/
theorem eval_variation (polynomial : Basic.CoordinatePolynomial) (variation : Fraction.Rational)
    (first second : Fraction.Rational) (firstLower : 0 ≤ first) (ordered : first ≤ second) (secondUpper : second ≤ 1)
    (small : second - first < variation / slopeFactor polynomial) :
    polynomial.eval first - variation ≤ polynomial.eval second ∧
      polynomial.eval second ≤ polynomial.eval first + variation := by
  let slope := Lipschitz.denseEvalSqLipschitzBound polynomial ⟨0, 1, by decide⟩
  let factor := slopeFactor polynomial
  let distance := second - first
  have factorPositive : 0 < factor := slopeFactor_pos polynomial
  have distanceNonnegative : 0 ≤ distance := Arithmetic.sub_nonneg_direct ordered
  have radiusNonnegative : 0 ≤ factor * distance :=
    Arithmetic.mul_nonneg_direct factorPositive.le distanceNonnegative
  have firstUpper : first ≤ 1 := Fraction.Order.Basic.le_trans _ _ _ ordered secondUpper
  have secondLower : 0 ≤ second := Fraction.Order.Basic.le_trans _ _ _ firstLower ordered
  have horner := Lipschitz.eval_sub_sq_le polynomial ⟨0, 1, by decide⟩
    ⟨firstLower, firstUpper⟩ ⟨secondLower, secondUpper⟩
  have oppositeSquare : (first - second) ^ 2 = distance ^ 2 := by
    change (first - second) ^ 2 = (second - first) ^ 2
    ring1
  rw [oppositeSquare] at horner
  have slopeBound : slope ≤ factor ^ 2 := slope_le_factor_sq polynomial
  have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct slopeBound
    (Arithmetic.sq_nonneg_direct distance)
  have squareBound : (polynomial.eval first - polynomial.eval second) ^ 2 ≤ (factor * distance) ^ 2 := by
    calc
      _ ≤ slope * distance ^ 2 := horner
      _ ≤ factor ^ 2 * distance ^ 2 := scaled
      _ = (factor * distance) ^ 2 := by ring1
  have firstDifference : polynomial.eval first - polynomial.eval second ≤ factor * distance :=
    Arithmetic.nonnegative_le_of_sq_le_sq radiusNonnegative squareBound
  have reversedSquare : (polynomial.eval second - polynomial.eval first) ^ 2 =
      (polynomial.eval first - polynomial.eval second) ^ 2 := by ring1
  have secondDifference : polynomial.eval second - polynomial.eval first ≤ factor * distance := by
    apply Arithmetic.nonnegative_le_of_sq_le_sq radiusNonnegative
    rw [reversedSquare]
    exact squareBound
  have paid : factor * distance < variation := by
    have scaledDistance := (Fraction.Order.Field.lt_div_iff_pos factorPositive).mp small
    have commute : distance * factor = factor * distance := by ring1
    rw [commute] at scaledDistance
    exact scaledDistance
  have firstBound := Fraction.Order.Basic.le_trans _ _ _ firstDifference paid.le
  have secondBound := Fraction.Order.Basic.le_trans _ _ _ secondDifference paid.le
  have firstAdded := Arithmetic.sub_le_iff_le_add_direct.mp firstBound
  have firstCommute : variation + polynomial.eval second = polynomial.eval second + variation := by ring1
  rw [firstCommute] at firstAdded
  have lower := Arithmetic.sub_le_iff_le_add_direct.mpr firstAdded
  have upper := Arithmetic.sub_le_iff_le_add_direct.mp secondBound
  have secondCommute : variation + polynomial.eval first = polynomial.eval first + variation := by ring1
  rw [secondCommute] at upper
  exact ⟨lower, upper⟩

/-- Compute an effective unit-interval modulus from the original finite rational polynomial. -/
@[expose] def modulus (polynomial : Basic.CoordinatePolynomial) : Rational.Uniform.Modulus polynomial.eval where
  radius := fun variation => variation / slopeFactor polynomial
  radius_pos := fun _ positive => Fraction.Order.Field.div_pos_direct positive (slopeFactor_pos polynomial)
  variation := fun variation _ => eval_variation polynomial variation

end Purelib.Polynomial.Dense.Rational.Bounds.Uniform

end
