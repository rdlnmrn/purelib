module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Bounds.Abs
import Purelib.Data.Rat.Bounds.Scale
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Data.Rat.Interval.Radius
public import Purelib.Geometry.Rational.Plane.Turn.Basic
public import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Polynomial.Clearance.Pair.Operations
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Purelib.Algebra.Semiring.Normalization

namespace Purelib.Polynomial.Dense.Rational.Pair.Turn.Bounds

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rational
open Purelib.Algebra.Semiring

/-- A positive ambient squared radius forcing the two endpoint vectors of a
clear polynomial pair to make a narrow complex turn.

The original value and difference Horner bounds are retained for both
polynomials. Two exact quotient thresholds share the same positive
clearance and their minimum supplies the squared-radius request. -/
@[expose] public def narrowTurnResolutionRadiusSq
    {A B : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate A B root) : Fraction.Rational :=
  let differenceCoefficient :=
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound A root +
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound B root
  let normBound :=
    Dense.Rational.Bounds.Horner.evalSqBound A root +
      Dense.Rational.Bounds.Horner.evalSqBound B root
  min (clearance.bound / (differenceCoefficient + 1))
    (clearance.bound ^ 2 /
      (36 * normBound * differenceCoefficient + 1))

/-- Positive pair clearance gives a positive squared-radius threshold for a narrow endpoint turn.

Both original denominator coefficients are nonnegative and are
increased by one. The retained positive clearance and its square
therefore give two positive quotients in the original minimum. -/
public theorem narrowTurnResolutionRadiusSq_pos
    {A B : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate A B root) :
    0 < narrowTurnResolutionRadiusSq clearance := by
  let differenceCoefficient :=
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound A root +
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound B root
  let normBound :=
    Dense.Rational.Bounds.Horner.evalSqBound A root +
      Dense.Rational.Bounds.Horner.evalSqBound B root
  have differenceNonnegative : 0 ≤ differenceCoefficient :=
    add_nonneg (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg A root).2
      (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg B root).2
  have normNonnegative : 0 ≤ normBound :=
    add_nonneg
      (Dense.Rational.Bounds.Horner.evalSqBound_nonneg A root)
      (Dense.Rational.Bounds.Horner.evalSqBound_nonneg B root)
  have thirtySixNonnegative : 0 ≤ (36 : Fraction.Rational) :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 36) (by decide)).le
  have onePositive : 0 < (1 : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct
      (n := 1) (by decide)
  have crossCoefficientNonnegative :
      0 ≤ 36 * normBound * differenceCoefficient :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct
        thirtySixNonnegative normNonnegative)
      differenceNonnegative
  unfold narrowTurnResolutionRadiusSq
  apply Fraction.Order.Basic.lt_min
  · apply Fraction.Order.Field.div_pos_direct clearance.positive
    calc
      0 < 1 := onePositive
      _ ≤ differenceCoefficient + 1 :=
        by
          simpa only [zero_add] using
            Arithmetic.add_le_add_right_direct
              differenceNonnegative (1 : Fraction.Rational)
  · apply Fraction.Order.Field.div_pos_direct
    · simpa only [pow_two] using
        Arithmetic.mul_pos_direct
          clearance.positive clearance.positive
    · calc
        0 < 1 := onePositive
        _ ≤ 36 * normBound * differenceCoefficient + 1 :=
          by
            simpa only [zero_add] using
              Arithmetic.add_le_add_right_direct
                crossCoefficientNonnegative (1 : Fraction.Rational)

/-- Below the computed squared radius, the two endpoint coordinate vectors
satisfy the narrow-turn cross-product bound.

The original endpoint evaluations and difference bounds use the same
refined interval and retained clearance. The two squared-radius tests
bound the cross product and keep its scaled absolute value below
the original endpoint dot product. -/
public theorem narrowComplexTurn_of_refined_radiusSq
    {A B : Dense.Rational.Basic.CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate A B root)
    (refines : interval.Refines root)
    (radiusSmall : Interval.Radius.sampleRadiusSq interval interval.lower <
      narrowTurnResolutionRadiusSq clearance) :
    Plane.Turn.Basic.NarrowComplexTurn
      (A.eval interval.lower) (B.eval interval.lower)
      (A.eval interval.upper) (B.eval interval.upper) := by
  let radius := Interval.Radius.sampleRadiusSq interval interval.lower
  let differenceCoefficient :=
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound A root +
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound B root
  let normBound :=
    Dense.Rational.Bounds.Horner.evalSqBound A root +
      Dense.Rational.Bounds.Horner.evalSqBound B root
  let a := A.eval interval.lower
  let b := B.eval interval.lower
  let c := A.eval interval.upper
  let d := B.eval interval.upper
  let da := c - a
  let db := d - b
  let differenceSq := da ^ 2 + db ^ 2
  let cross := a * d - b * c
  let dot := a * c + b * d
  have radiusNonnegative : 0 ≤ radius := Interval.Radius.sampleRadiusSq_nonneg interval
  have differenceCoefficientNonnegative : 0 ≤ differenceCoefficient :=
    add_nonneg (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg A root).2
      (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg B root).2
  have normBoundNonnegative : 0 ≤ normBound :=
    add_nonneg
      (Dense.Rational.Bounds.Horner.evalSqBound_nonneg A root)
      (Dense.Rational.Bounds.Horner.evalSqBound_nonneg B root)
  have upperInside : root.Contains interval.upper :=
    ⟨refines.1.trans interval.valid, refines.2⟩
  have lowerInside : root.Contains interval.lower :=
    ⟨refines.1, interval.valid.trans refines.2⟩
  have endpointDistance :
      (interval.upper - interval.lower) ^ 2 ≤ radius :=
    Interval.Radius.sub_sq_le_sampleRadiusSq interval ⟨interval.valid, le_rfl⟩
  have daBound : da ^ 2 ≤
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound A root * radius := by
    have localBound := Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le A interval
      (x := interval.upper) (y := interval.lower)
      ⟨interval.valid, le_rfl⟩ ⟨le_rfl, interval.valid⟩
    have ambientProduct := Arithmetic.mul_le_mul_direct
      (Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound_le_of_refines A refines)
      endpointDistance
      (Arithmetic.sq_nonneg_direct
        (interval.upper - interval.lower))
      (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg A root).2
    exact localBound.trans (by
      simpa only [da, c, a] using ambientProduct)
  have dbBound : db ^ 2 ≤
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound B root * radius := by
    have localBound := Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le B interval
      (x := interval.upper) (y := interval.lower)
      ⟨interval.valid, le_rfl⟩ ⟨le_rfl, interval.valid⟩
    have ambientProduct := Arithmetic.mul_le_mul_direct
      (Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound_le_of_refines B refines)
      endpointDistance
      (Arithmetic.sq_nonneg_direct
        (interval.upper - interval.lower))
      (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg B root).2
    exact localBound.trans (by
      simpa only [db, d, b] using ambientProduct)
  have differenceBound : differenceSq ≤ differenceCoefficient * radius := by
    dsimp only [differenceSq, differenceCoefficient]
    calc
      da ^ 2 + db ^ 2 ≤
          Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound A root * radius +
            Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound B root * radius :=
        add_le_add daBound dbBound
      _ = (Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound A root +
          Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound B root) * radius := by ring1
  have firstRadius : radius < clearance.bound /
      (differenceCoefficient + 1) :=
    radiusSmall.trans_le (Fraction.Order.Basic.min_le_left _ _)
  have differenceBelowClearance : differenceSq < clearance.bound :=
    differenceBound.trans_lt
      (Data.Rat.Bounds.Scale.coefficient_mul_lt_of_radius_lt_div_add_one
        differenceCoefficientNonnegative radiusNonnegative firstRadius)
  have lowerClearance : clearance.bound ≤ a ^ 2 + b ^ 2 := by
    simpa only [a, b] using clearance.lower interval.lower lowerInside
  have upperClearance : clearance.bound ≤ c ^ 2 + d ^ 2 := by
    simpa only [c, d] using clearance.lower interval.upper upperInside
  have lowerNormBound : a ^ 2 + b ^ 2 ≤ normBound := by
    dsimp only [normBound, a, b]
    exact add_le_add
      (Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound A root lowerInside)
      (Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound B root lowerInside)
  have differenceNonnegative : 0 ≤ differenceSq :=
    add_nonneg (Arithmetic.sq_nonneg_direct da)
      (Arithmetic.sq_nonneg_direct db)
  have crossBound : cross ^ 2 ≤
      normBound * (differenceCoefficient * radius) := by
    have cauchy : cross ^ 2 ≤
        (a ^ 2 + b ^ 2) * differenceSq := by
      have base := Data.Rat.Bounds.Square.cross_sq_le_product_sums a b da db
      have crossIdentity : cross = a * db - b * da := by
        dsimp only [cross, da, db, a, b, c, d]
        ring1
      rw [crossIdentity]
      exact base
    exact cauchy.trans
      (Arithmetic.mul_le_mul_direct lowerNormBound
        differenceBound differenceNonnegative normBoundNonnegative)
  have thirtySixNonnegative : 0 ≤ (36 : Fraction.Rational) :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 36) (by decide)).le
  have crossCoefficientNonnegative :
      0 ≤ 36 * normBound * differenceCoefficient :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct thirtySixNonnegative
        normBoundNonnegative)
      differenceCoefficientNonnegative
  have secondRadius : radius < clearance.bound ^ 2 /
      (36 * normBound * differenceCoefficient + 1) :=
    radiusSmall.trans_le (Fraction.Order.Basic.min_le_right _ _)
  have scaledCrossBelow : 36 * cross ^ 2 < clearance.bound ^ 2 := by
    calc
      36 * cross ^ 2 ≤
          36 * (normBound * (differenceCoefficient * radius)) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          crossBound thirtySixNonnegative
      _ = (36 * normBound * differenceCoefficient) * radius := by ring1
      _ < clearance.bound ^ 2 :=
        Data.Rat.Bounds.Scale.coefficient_mul_lt_of_radius_lt_div_add_one
          crossCoefficientNonnegative radiusNonnegative secondRadius
  have sixAbsCrossBelow : 6 * Fraction.abs (cross) < clearance.bound := by
    apply Data.Rat.Bounds.Square.lt_of_sq_lt_sq_of_nonneg clearance.positive.le
    calc
      (6 * Fraction.abs (cross)) ^ 2 = 36 * cross ^ 2 := by
        rw [Normalization.product_pow 6 (Fraction.abs cross) 2, Data.Rat.Bounds.Abs.abs_sq_direct]
        ring1
      _ < clearance.bound ^ 2 := scaledCrossBelow
  have sumLess : differenceSq + clearance.bound <
      (a ^ 2 + b ^ 2) + (c ^ 2 + d ^ 2) := by
    have first := Arithmetic.add_lt_add_right_direct
      (differenceBelowClearance.trans_le lowerClearance) clearance.bound
    exact first.trans_le
      (add_le_add (le_refl (a ^ 2 + b ^ 2)) upperClearance)
  have clearanceBelowTwiceDot : clearance.bound < 2 * dot := by
    have positiveDifference := Arithmetic.sub_pos_direct sumLess
    have shifted := Arithmetic.add_lt_add_right_direct
      positiveDifference clearance.bound
    calc
      clearance.bound = 0 + clearance.bound := by ring1
      _ < ((a ^ 2 + b ^ 2) + (c ^ 2 + d ^ 2) -
            (differenceSq + clearance.bound)) + clearance.bound := shifted
      _ = 2 * dot := by
        dsimp only [differenceSq, da, db, dot]
        ring1
  have scaledNarrow : 2 * (3 * Fraction.abs (cross)) < 2 * dot := by
    calc
      2 * (3 * Fraction.abs (cross)) = 6 * Fraction.abs (cross) := by ring1
      _ < clearance.bound := sixAbsCrossBelow
      _ < 2 * dot := clearanceBelowTwiceDot
  have narrow : 3 * Fraction.abs (cross) < dot :=
    Data.Rat.Bounds.Square.lt_of_two_mul_lt_two_mul_direct scaledNarrow
  simpa only [Plane.Turn.Basic.NarrowComplexTurn,
    cross, dot, a, b, c, d] using narrow

end Purelib.Polynomial.Dense.Rational.Pair.Turn.Bounds
