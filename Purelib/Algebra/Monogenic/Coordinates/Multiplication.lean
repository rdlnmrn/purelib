module

public import Purelib.Algebra.Monogenic.Coordinates.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Multiplication discrepancies of original cyclic readings

An original generator-action estimate propagates through its same finitely
many powers. The original coordinate reconstruction then reduces general
product discrepancies to scalar-action and power-action discrepancies.
-/

public section

namespace Purelib.Algebra.Monogenic.Cyclic.Element

open Purelib.Algebra.Ring (Weight)
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Algebra.FiniteSum.Rational.Order
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction

variable {K : Type*} [CommRing K] {dimension : Nat} {generator : SquareMatrix K dimension}
variable {cyclic : Cyclic generator}

/-- The original finite generator powers propagate one uniform action-discrepancy estimate.

The power-weight ceiling concerns only the original retained powers below
the cyclic dimension. Every requested exponent is bounded by that dimension;
the rational growth factor depends on the same candidate's squared norm.
-/
theorem evaluate_root_pow_mul_normSq_sub_le (parent : Ring.Weight K) (function : K → Canonical)
    (point : Canonical) (step powerWeight radius : Rational)
    (stepNonnegative : 0 ≤ step) (powerWeightNonnegative : 0 ≤ powerWeight) (radiusNonnegative : 0 ≤ radius)
    (pointBound : Norm.Basic.normSq point ≤ radius)
    (powerWeightBound : ∀ index : Fin dimension,
      (weight cyclic parent).value (root cyclic ^ index.val) ≤ powerWeight)
    (stepBound : ∀ value : Element cyclic,
      Norm.Basic.normSq (evaluate function point (root cyclic * value) - point * evaluate function point value) ≤
        step * (weight cyclic parent).value value)
    (exponent : Nat) (bounded : exponent ≤ dimension) (value : Element cyclic) :
    Norm.Basic.normSq (evaluate function point (root cyclic ^ exponent * value) -
        point ^ exponent * evaluate function point value) ≤
      (step * (weight cyclic parent).multiplier * powerWeight) * (2 * (1 + radius)) ^ exponent *
        (weight cyclic parent).value value := by
  let lifted := weight cyclic parent
  let factor := step * lifted.multiplier * powerWeight
  let ratio := 2 * (1 + radius)
  have factorNonnegative : 0 ≤ factor := Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct stepNonnegative lifted.multiplier_nonnegative) powerWeightNonnegative
  have oneLeRatio : (1 : Rational) ≤ ratio := by
    have radiusOne : (1 : Rational) ≤ 1 + radius :=
      (Order.Arithmetic.add_le_add_direct (le_rfl : (1 : Rational) ≤ 1) radiusNonnegative)
    apply (by decide : (1 : Rational) ≤ 2).trans
    have bound := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusOne (by decide : (0 : Rational) ≤ 2)
    rewrite [mul_one] at bound
    exact bound
  change _ ≤ factor * ratio ^ exponent * lifted.value value
  induction exponent with
  | zero =>
      rewrite [pow_zero, _root_.one_mul, pow_zero, _root_.one_mul, sub_self,
        Norm.Basic.normSq_zero, pow_zero, mul_one]
      exact Order.Arithmetic.mul_nonneg_direct factorNonnegative (lifted.nonnegative value)
  | succ exponent previous =>
      have exponentBound : exponent < dimension := Nat.lt_of_succ_le bounded
      have powerBound := powerWeightBound ⟨exponent, exponentBound⟩
      have previousBound := previous (Nat.le_of_succ_le bounded)
      have firstBound :
          Norm.Basic.normSq (evaluate function point (root cyclic * (root cyclic ^ exponent * value)) -
            point * evaluate function point (root cyclic ^ exponent * value)) ≤ factor * lifted.value value := by
        apply (stepBound _).trans
        apply (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (lifted.mul_le _ _) stepNonnegative).trans
        apply (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct powerBound lifted.multiplier_nonnegative)
            (lifted.nonnegative value)) stepNonnegative).trans
        apply Eq.le
        change step * ((lifted.multiplier * powerWeight) * lifted.value value) =
          (step * lifted.multiplier * powerWeight) * lifted.value value
        ring0
      have secondBound : Norm.Basic.normSq (point *
          (evaluate function point (root cyclic ^ exponent * value) -
            point ^ exponent * evaluate function point value)) ≤
          radius * (factor * ratio ^ exponent * lifted.value value) := by
        rewrite [Norm.Basic.normSq_mul]
        exact Order.Arithmetic.mul_le_mul_direct pointBound previousBound
          (Norm.Basic.normSq_nonneg _) radiusNonnegative
      have oneLePower : (1 : Rational) ≤ ratio ^ exponent := by
        have bound := Order.Arithmetic.pow_le_pow_direct (by decide : (0 : Rational) ≤ 1) oneLeRatio exponent
        rewrite [one_pow] at bound
        exact bound
      have inflated : factor * lifted.value value ≤ factor * ratio ^ exponent * lifted.value value := by
        have bound := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct oneLePower factorNonnegative) (lifted.nonnegative value)
        rewrite [mul_one] at bound
        exact bound
      have originalPower : root cyclic ^ (exponent + 1) * value =
          root cyclic * (root cyclic ^ exponent * value) := by
        rewrite [pow_succ, _root_.mul_assoc]
        exact _root_.mul_left_comm _ _ _
      have targetPower : point ^ (exponent + 1) * evaluate function point value =
          point * (point ^ exponent * evaluate function point value) := by
        rewrite [pow_succ, _root_.mul_assoc]
        exact _root_.mul_left_comm _ _ _
      have decomposition :
          evaluate function point (root cyclic ^ (exponent + 1) * value) -
            point ^ (exponent + 1) * evaluate function point value =
          (evaluate function point (root cyclic * (root cyclic ^ exponent * value)) -
            point * evaluate function point (root cyclic ^ exponent * value)) +
          point * (evaluate function point (root cyclic ^ exponent * value) -
            point ^ exponent * evaluate function point value) := by
        rewrite [originalPower, targetPower]
        have telescope (first middle tail scalar : Canonical) :
            first - scalar * tail = (first - scalar * middle) + scalar * (middle - tail) := by ring0
        exact telescope _ _ _ _
      rewrite [decomposition]
      apply (Norm.Bounds.normSq_add_le_two _ _).trans
      apply (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct (firstBound.trans inflated) secondBound) (by decide)).trans
      apply Eq.le
      rewrite [pow_succ]
      have collected (power : Rational) :
          2 * (factor * power * lifted.value value + radius * (factor * power * lifted.value value)) =
            factor * (power * (2 * (1 + radius))) * lifted.value value := by ring0
      exact collected _

/-- Scalar-action and bounded power-action estimates bound every original product-reading discrepancy.

The original coordinate reconstruction supplies the finite summands. Their
coefficient weights are bounded by the same original matrix total, and the
original power matrices supply the only power-weight ceiling.
-/
theorem evaluate_mul_normSq_sub_le (parent : Ring.Weight K) (function : K → Canonical)
    (mapZero : function 0 = 0)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (point : Canonical) (gain scalarError powerError powerWeight : Rational)
    (gainNonnegative : 0 ≤ gain) (scalarErrorNonnegative : 0 ≤ scalarError)
    (powerErrorNonnegative : 0 ≤ powerError) (powerWeightNonnegative : 0 ≤ powerWeight)
    (coefficientBound : ∀ coefficient, Norm.Basic.normSq (function coefficient) ≤ gain * parent.value coefficient)
    (powerWeightBound : ∀ index : Fin dimension,
      (weight cyclic parent).value (root cyclic ^ index.val) ≤ powerWeight)
    (scalarBound : ∀ coefficient (value : Element cyclic),
      Norm.Basic.normSq (evaluate function point (scalar cyclic coefficient * value) -
        function coefficient * evaluate function point value) ≤
          scalarError * parent.value coefficient * (weight cyclic parent).value value)
    (powerBound : ∀ (index : Fin dimension) (value : Element cyclic),
      Norm.Basic.normSq (evaluate function point (root cyclic ^ index.val * value) -
        point ^ index.val * evaluate function point value) ≤ powerError * (weight cyclic parent).value value)
    (left right : Element cyclic) :
    Norm.Basic.normSq (evaluate function point (left * right) -
        evaluate function point left * evaluate function point right) ≤
      ((2 : Rational) ^ dimension * 2 *
        (scalarError * (weight cyclic parent).multiplier * powerWeight + gain * powerError)) *
          (weight cyclic parent).value left * (weight cyclic parent).value right := by
  let lifted := weight cyclic parent
  let scalarTerm := fun index : Fin dimension =>
    evaluate function point (scalar cyclic (left.matrix index cyclic.origin) * (root cyclic ^ index.val * right)) -
      function (left.matrix index cyclic.origin) * evaluate function point (root cyclic ^ index.val * right)
  let powerTerm := fun index : Fin dimension => function (left.matrix index cyclic.origin) *
    (evaluate function point (root cyclic ^ index.val * right) - point ^ index.val * evaluate function point right)
  let factor := 2 * (scalarError * lifted.multiplier * powerWeight + gain * powerError)
  have factorNonnegative : 0 ≤ factor := Order.Arithmetic.mul_nonneg_direct (by decide)
    (Order.Arithmetic.add_le_add_direct
      (Order.Arithmetic.mul_nonneg_direct
        (Order.Arithmetic.mul_nonneg_direct scalarErrorNonnegative lifted.multiplier_nonnegative)
        powerWeightNonnegative)
      (Order.Arithmetic.mul_nonneg_direct gainNonnegative powerErrorNonnegative))
  have scalarTermBound (index : Fin dimension) : Norm.Basic.normSq (scalarTerm index) ≤
      (scalarError * lifted.multiplier * powerWeight) * parent.value (left.matrix index cyclic.origin) *
        lifted.value right := by
    have originalWeight := (lifted.mul_le (root cyclic ^ index.val) right).trans
      (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (powerWeightBound index) lifted.multiplier_nonnegative)
        (lifted.nonnegative right))
    apply (scalarBound _ _).trans
    apply (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct originalWeight
      (Order.Arithmetic.mul_nonneg_direct scalarErrorNonnegative (parent.nonnegative _))).trans
    apply Eq.le
    ring0
  have powerTermBound (index : Fin dimension) : Norm.Basic.normSq (powerTerm index) ≤
      (gain * powerError) * parent.value (left.matrix index cyclic.origin) * lifted.value right := by
    change Norm.Basic.normSq (function (left.matrix index cyclic.origin) * _) ≤ _
    rewrite [Norm.Basic.normSq_mul]
    apply (Order.Arithmetic.mul_le_mul_direct (coefficientBound _) (powerBound index right)
      (Norm.Basic.normSq_nonneg _) (Order.Arithmetic.mul_nonneg_direct gainNonnegative
        (parent.nonnegative _))).trans
    apply Eq.le
    ring0
  have entryBound (index : Fin dimension) : Norm.Basic.normSq (scalarTerm index + powerTerm index) ≤
      (factor * lifted.value right) * parent.value (left.matrix index cyclic.origin) := by
    apply (Norm.Bounds.normSq_add_le_two _ _).trans
    apply (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct (scalarTermBound index) (powerTermBound index)) (by decide)).trans
    apply Eq.le
    change 2 * ((scalarError * lifted.multiplier * powerWeight) *
      parent.value (left.matrix index cyclic.origin) * lifted.value right +
      (gain * powerError) * parent.value (left.matrix index cyclic.origin) * lifted.value right) =
        ((2 * (scalarError * lifted.multiplier * powerWeight + gain * powerError)) * lifted.value right) *
          parent.value (left.matrix index cyclic.origin)
    ring0
  have sumBound := Norm.normSq_sumFin_le (fun index => scalarTerm index + powerTerm index)
    (fun index => (factor * lifted.value right) * parent.value (left.matrix index cyclic.origin)) entryBound
  rewrite [evaluate_mul_sub function mapZero mapAdd]
  apply sumBound.trans
  rewrite [sumFin_mul_left]
  apply (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (SquareMatrix.Weight.column_le_total parent left.matrix cyclic.origin)
      (Order.Arithmetic.mul_nonneg_direct factorNonnegative (lifted.nonnegative right)))
    (Order.Arithmetic.pow_nonneg_direct (by decide : (0 : Rational) ≤ 2) dimension)).trans
  apply Eq.le
  change 2 ^ dimension * ((factor * lifted.value right) * lifted.value left) =
    (2 ^ dimension * 2 * (scalarError * lifted.multiplier * powerWeight + gain * powerError)) *
      lifted.value left * lifted.value right
  change 2 ^ dimension * (((2 *
    (scalarError * lifted.multiplier * powerWeight + gain * powerError)) * lifted.value right) * lifted.value left) = _
  ring0

end Purelib.Algebra.Monogenic.Cyclic.Element

end
