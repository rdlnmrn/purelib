module
public import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
public import Purelib.Approximation.Rational.Segment.Increment
public import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Gaussian.Norm.Coordinates
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# Ordered real increments of finite Gaussian polynomial primitives

A retained Gaussian polynomial primitive supplies its finite Taylor
remainder. A rational lower bound on a signed real coordinate of its
derivative then controls the signed real primitive increment along the
original rational segment, by finite midpoint subdivision.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Real

open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate

/-- A nonnegative rational remainder is bounded by the square of one plus that remainder. -/
private theorem remainder_le_square (remainder : Fraction.Rational) (nonnegative : 0 ≤ remainder) :
    remainder ≤ (remainder + 1) ^ 2 := by
  have square := Arithmetic.sq_nonneg_direct remainder
  have extra := Arithmetic.add_le_add_direct
    (Arithmetic.add_le_add_direct square nonnegative) (by decide : (0 : Fraction.Rational) ≤ 1)
  have zero : (0 : Fraction.Rational) + 0 + 0 = 0 := by decide
  rw [zero] at extra
  have shifted := Arithmetic.add_le_add_right_direct extra remainder
  calc
    remainder = 0 + remainder := by ring1
    _ ≤ (remainder ^ 2 + remainder + 1) + remainder := shifted
    _ = (remainder + 1) ^ 2 := by ring1

/-- A signed real derivative lower bound controls the actual primitive's rational endpoint increment.

The original finite primitive and its Gaussian box remain fixed. The sign
has square one, so the same squared Taylor remainder applies to either real
orientation. Finite midpoint subdivision removes that quadratic remainder. -/
theorem increment_lower {coefficient : Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (primitive : DensePrimitive coefficient box) (interval : Purelib.Data.Rat.Interval)
    (boxInside : ∀ point, interval.Contains point → box.Contains (RationalEmbedding.realPoint point))
    (sign linear : Fraction.Rational) (signSquare : sign ^ 2 = 1)
    (coefficientLower : ∀ point, interval.Contains point →
      linear ≤ sign * (coefficient.eval (RationalEmbedding.realPoint point)).re)
    {first last : Fraction.Rational} (firstInside : interval.Contains first)
    (lastInside : interval.Contains last) (ordered : last ≤ first) :
    linear * (first - last) ≤
      sign * (primitive.value.eval (RationalEmbedding.realPoint first)).re -
        sign * (primitive.value.eval (RationalEmbedding.realPoint last)).re := by
  let remainder := primitive.remainderBound + 1
  have remainderNonnegative : 0 ≤ remainder := by
    have shifted := Arithmetic.add_le_add_direct primitive.remainderBound_nonnegative
      (by decide : (0 : Fraction.Rational) ≤ 1)
    exact shifted
  let reading := fun point => sign * (primitive.value.eval (RationalEmbedding.realPoint point)).re
  have localBound : ∀ {x y}, interval.Contains x → interval.Contains y → y ≤ x →
      linear * (x - y) - remainder * (x - y) ^ 2 ≤ reading x - reading y := by
    intro x y xInside yInside xy
    let firstValue := primitive.value.eval (RationalEmbedding.realPoint x) -
      primitive.value.eval (RationalEmbedding.realPoint y)
    let firstOrder := coefficient.eval (RationalEmbedding.realPoint y) *
      (RationalEmbedding.realPoint x - RationalEmbedding.realPoint y)
    have gaussian := primitive.increment_bound (boxInside y yInside) (boxInside x xInside)
    have coordinate := Norm.Coordinates.re_sub_sq_le_basic_normSq firstValue firstOrder
    have square := coordinate.trans gaussian
    rw [RationalEmbedding.realPoint_sub, RationalEmbedding.normSq_realPoint] at square
    have remainderBound := remainder_le_square primitive.remainderBound primitive.remainderBound_nonnegative
    have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct remainderBound
      (Arithmetic.sq_nonneg_direct ((x - y) ^ 2))
    have signedSquare : (sign * (firstValue.re - firstOrder.re)) ^ 2 = (firstValue.re - firstOrder.re) ^ 2 := by
      calc
        _ = sign ^ 2 * (firstValue.re - firstOrder.re) ^ 2 := by ring1
        _ = (firstValue.re - firstOrder.re) ^ 2 := by rw [signSquare]; ring1
    have bound : (sign * (firstValue.re - firstOrder.re)) ^ 2 ≤ (remainder * (x - y) ^ 2) ^ 2 := by
      rw [signedSquare]
      calc
        _ ≤ primitive.remainderBound * ((x - y) ^ 2) ^ 2 := square
        _ ≤ remainder ^ 2 * ((x - y) ^ 2) ^ 2 := scaled
        _ = (remainder * (x - y) ^ 2) ^ 2 := by ring1
    have radiusNonnegative : 0 ≤ remainder * (x - y) ^ 2 :=
      Arithmetic.mul_nonneg_direct remainderNonnegative (Arithmetic.sq_nonneg_direct _)
    have error := Arithmetic.neg_le_of_sq_le_sq_direct radiusNonnegative bound
    have distance := Arithmetic.sub_nonneg_direct xy
    have derivative := Arithmetic.mul_le_mul_of_nonneg_right_direct
      (coefficientLower y yInside) distance
    have combined := Arithmetic.add_le_add_direct derivative error
    have firstOrderRe : firstOrder.re =
        (coefficient.eval (RationalEmbedding.realPoint y)).re * (x - y) := by
      dsimp only [firstOrder]
      rw [RationalEmbedding.realPoint_sub, Basic.mul_re, RationalEmbedding.realPoint_re,
        RationalEmbedding.realPoint_im]
      ring1
    have firstValueRe : firstValue.re =
        (primitive.value.eval (RationalEmbedding.realPoint x)).re -
          (primitive.value.eval (RationalEmbedding.realPoint y)).re := Basic.sub_re _ _
    rw [firstOrderRe, firstValueRe] at combined
    have leftIdentity : linear * (x - y) + -(remainder * (x - y) ^ 2) =
        linear * (x - y) - remainder * (x - y) ^ 2 := by ring1
    have rightIdentity : sign * (coefficient.eval (RationalEmbedding.realPoint y)).re * (x - y) +
        sign * (((primitive.value.eval (RationalEmbedding.realPoint x)).re -
          (primitive.value.eval (RationalEmbedding.realPoint y)).re) -
          (coefficient.eval (RationalEmbedding.realPoint y)).re * (x - y)) = reading x - reading y := by
      dsimp only [reading]
      ring1
    rw [leftIdentity, rightIdentity] at combined
    exact combined
  exact Segment.Increment.remove_quadratic reading interval linear remainder remainderNonnegative localBound
    firstInside lastInside ordered

end Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Real

end
