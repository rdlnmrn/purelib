module

public import Purelib.Algebra.Monogenic.Coordinates
public import Purelib.Algebra.Monogenic.Weight
public import Purelib.Data.Gaussian.Norm.Weight
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Rational bounds for original cyclic-coordinate readings

The original distinguished-column reading is bounded by the complete weight
of the same retained matrix. The only pointwise inputs bound the original
coefficient reading and the finitely many original candidate powers.
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

/-- A bounded coefficient reading and its same finite candidate powers bound the original algebra reading.

The retained original cyclic dimension supplies the squared-sum factor.
Only the distinguished column is read; its original entry weights are paid
by the total of the same original matrix, without reconstructing its powers.
-/
theorem evaluate_normSq_le (parent : Ring.Weight K) (function : K → Canonical) (mapZero : function 0 = 0)
    (gain ceiling : Rational) (gainNonnegative : 0 ≤ gain) (ceilingNonnegative : 0 ≤ ceiling)
    (coefficientBound : ∀ scalar, Norm.Basic.normSq (function scalar) ≤ gain * parent.value scalar)
    (point : Canonical) (powerBound : ∀ index : Fin dimension, Norm.Basic.normSq (point ^ index.val) ≤ ceiling)
    (value : Element cyclic) :
    Norm.Basic.normSq (evaluate function point value) ≤
      ((2 : Rational) ^ dimension * gain * ceiling) * (weight cyclic parent).value value := by
  unfold evaluate
  rewrite [eval_map_polynomial function mapZero]
  have sumBound := Norm.weight.sum_le
    (fun index : Fin dimension => function (value.matrix index cyclic.origin) * point ^ index.val)
  change Norm.Basic.normSq _ ≤ 2 ^ dimension *
    sumFin (fun index : Fin dimension =>
      Norm.Basic.normSq (function (value.matrix index cyclic.origin) * point ^ index.val)) at sumBound
  have entryBound (index : Fin dimension) :
      Norm.Basic.normSq (function (value.matrix index cyclic.origin) * point ^ index.val) ≤
        (gain * ceiling) * parent.value (value.matrix index cyclic.origin) := by
    rewrite [Norm.Basic.normSq_mul]
    apply (Order.Arithmetic.mul_le_mul_direct (coefficientBound _) (powerBound index)
      (Norm.Basic.normSq_nonneg _) (Order.Arithmetic.mul_nonneg_direct gainNonnegative
        (parent.nonnegative _))).trans
    apply Eq.le
    ring0
  calc
    _ ≤ 2 ^ dimension * sumFin (fun index : Fin dimension =>
        Norm.Basic.normSq (function (value.matrix index cyclic.origin) * point ^ index.val)) := sumBound
    _ ≤ 2 ^ dimension *
        ((gain * ceiling) * sumFin (fun index => parent.value (value.matrix index cyclic.origin))) := by
      apply Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
        (Order.Arithmetic.pow_nonneg_direct (by decide : (0 : Rational) ≤ 2) dimension)
      exact (IndexedBudget.sumFin_le entryBound).trans (sumFin_mul_left _ _).le
    _ ≤ 2 ^ dimension * ((gain * ceiling) * SquareMatrix.Weight.total parent value.matrix) :=
      Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (SquareMatrix.Weight.column_le_total parent value.matrix cyclic.origin)
          (Order.Arithmetic.mul_nonneg_direct gainNonnegative ceilingNonnegative))
        (Order.Arithmetic.pow_nonneg_direct (by decide : (0 : Rational) ≤ 2) dimension)
    _ = _ := by
      change 2 ^ dimension * ((gain * ceiling) * SquareMatrix.Weight.total parent value.matrix) =
        (2 ^ dimension * gain * ceiling) * SquareMatrix.Weight.total parent value.matrix
      ring0

/-- An original coefficient multiplication-error bound controls the same scalar-action reading discrepancy.

The discrepancy is read by the original Horner evaluator and paid by the
same original coefficient and matrix weights. Its only point bounds concern
the same finitely many candidate powers.
-/
theorem evaluate_scalar_mul_normSq_sub_le (parent : Ring.Weight K) (function : K → Canonical)
    (mapZero : function 0 = 0) (error ceiling : Rational)
    (errorNonnegative : 0 ≤ error) (ceilingNonnegative : 0 ≤ ceiling)
    (productBound : ∀ left right,
      Norm.Basic.normSq (function (left * right) - function left * function right) ≤
        error * parent.value left * parent.value right)
    (point : Canonical) (powerBound : ∀ index : Fin dimension, Norm.Basic.normSq (point ^ index.val) ≤ ceiling)
    (coefficient : K) (value : Element cyclic) :
    Norm.Basic.normSq (evaluate function point (scalar cyclic coefficient * value) -
        function coefficient * evaluate function point value) ≤
      ((2 : Rational) ^ dimension * error * ceiling) * parent.value coefficient *
        (weight cyclic parent).value value := by
  let discrepancy := fun entry => function (coefficient * entry) - function coefficient * function entry
  have discrepancyZero : discrepancy 0 = 0 := by
    change function (coefficient * 0) - function coefficient * function 0 = 0
    rewrite [mul_zero, mapZero, mul_zero, sub_self]
    rfl
  have bounded := evaluate_normSq_le parent discrepancy discrepancyZero (error * parent.value coefficient)
    ceiling (Order.Arithmetic.mul_nonneg_direct errorNonnegative (parent.nonnegative coefficient)) ceilingNonnegative
    (productBound coefficient) point powerBound value
  calc
    _ = Norm.Basic.normSq (evaluate discrepancy point value) :=
      congrArg Norm.Basic.normSq (evaluate_scalar_mul_sub function mapZero point coefficient value)
    _ ≤ (2 ^ dimension * (error * parent.value coefficient) * ceiling) * (weight cyclic parent).value value := bounded
    _ = _ := by ring0

/-- Original generator-column residuals and coefficient-product errors uniformly bound its action discrepancy.

All constants refer to the same original generator, matrix entry weights
and candidate powers. The residual ceiling bounds the original mapped
generator columns, independently of the algebra element being read.
-/
theorem evaluate_root_mul_normSq_sub_le (parent : Ring.Weight K) (function : K → Canonical)
    (mapZero : function 0 = 0)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (gain error ceiling residual : Rational) (gainNonnegative : 0 ≤ gain) (errorNonnegative : 0 ≤ error)
    (residualNonnegative : 0 ≤ residual)
    (coefficientBound : ∀ scalar, Norm.Basic.normSq (function scalar) ≤ gain * parent.value scalar)
    (productBound : ∀ left right,
      Norm.Basic.normSq (function (left * right) - function left * function right) ≤
        error * parent.value left * parent.value right)
    (point : Canonical) (powerBound : ∀ index : Fin dimension, Norm.Basic.normSq (point ^ index.val) ≤ ceiling)
    (residualBound : ∀ column : Fin dimension,
      Norm.Basic.normSq (sumFin (fun row => function (generator row column) * point ^ row.val) -
        point * point ^ column.val) ≤ residual) (value : Element cyclic) :
    Norm.Basic.normSq (evaluate function point (root cyclic * value) - point * evaluate function point value) ≤
      (2 * ((2 : Rational) ^ dimension * gain * residual +
        (2 ^ dimension * 2 ^ dimension * error * ceiling) * SquareMatrix.Weight.total parent generator)) *
          (weight cyclic parent).value value := by
  let factor := (2 : Rational) ^ dimension
  let total := (weight cyclic parent).value value
  let columns := fun column =>
    sumFin (fun row => function (generator row column) * point ^ row.val) - point * point ^ column.val
  let errors := fun row column => function (generator row column * value.matrix column cyclic.origin) -
    function (generator row column) * function (value.matrix column cyclic.origin)
  have factorNonnegative : 0 ≤ factor := Order.Arithmetic.pow_nonneg_direct (by decide) dimension
  have mainBound : Norm.Basic.normSq (sumFin (fun column =>
      function (value.matrix column cyclic.origin) * columns column)) ≤ (factor * gain * residual) * total := by
    have bound := Norm.normSq_sumFin_mul_le
      (fun column => function (value.matrix column cyclic.origin)) columns
      (fun column => gain * parent.value (value.matrix column cyclic.origin)) (fun _ => residual)
      (fun _ => coefficientBound _) residualBound
    have sumEqual : sumFin (fun column => (gain * parent.value (value.matrix column cyclic.origin)) * residual) =
        (gain * residual) * sumFin (fun column => parent.value (value.matrix column cyclic.origin)) := by
      apply (sumFin_congr (right := fun column => (gain * residual) *
        parent.value (value.matrix column cyclic.origin)) ?_).trans (sumFin_mul_left _ _)
      intro column
      ring0
    apply bound.trans
    rewrite [sumEqual]
    calc
      _ = (factor * gain * residual) * sumFin (fun column => parent.value (value.matrix column cyclic.origin)) := by
        ring0
      _ ≤ _ := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (SquareMatrix.Weight.column_le_total parent value.matrix cyclic.origin)
        (Order.Arithmetic.mul_nonneg_direct
          (Order.Arithmetic.mul_nonneg_direct factorNonnegative gainNonnegative) residualNonnegative)
  have rowBound (row : Fin dimension) :
      Norm.Basic.normSq (sumFin (errors row)) ≤ (factor * error * total) *
        sumFin (fun column => parent.value (generator row column)) := by
    have bound := Norm.normSq_sumFin_le (errors row)
      (fun column => (error * total) * parent.value (generator row column)) (fun column => by
        apply (productBound _ _).trans
        calc
          _ ≤ (error * parent.value (generator row column)) * total :=
            Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (SquareMatrix.Weight.entry_le_total parent value.matrix column cyclic.origin)
              (Order.Arithmetic.mul_nonneg_direct errorNonnegative (parent.nonnegative _))
          _ = _ := by ring0)
    apply bound.trans
    apply Eq.le
    rewrite [sumFin_mul_left]
    change factor * ((error * total) * _) = (factor * error * total) * _
    ring0
  have errorsBound : Norm.Basic.normSq (sumFin (fun row => sumFin (errors row) * point ^ row.val)) ≤
      (factor * factor * error * ceiling * SquareMatrix.Weight.total parent generator) * total := by
    have bound := Norm.normSq_sumFin_mul_le (fun row => sumFin (errors row)) (fun row => point ^ row.val)
      (fun row => (factor * error * total) * sumFin (fun column => parent.value (generator row column)))
      (fun _ => ceiling) rowBound powerBound
    have sumEqual : sumFin (fun row =>
        ((factor * error * total) * sumFin (fun column => parent.value (generator row column))) * ceiling) =
        ((factor * error * total) * ceiling) * SquareMatrix.Weight.total parent generator := by
      apply (sumFin_congr (right := fun row => ((factor * error * total) * ceiling) *
        sumFin (fun column => parent.value (generator row column))) ?_).trans (sumFin_mul_left _ _)
      intro row
      ring0
    apply bound.trans
    apply Eq.le
    rewrite [sumEqual]
    change factor * (((factor * error * total) * ceiling) * _) = (factor * factor * error * ceiling * _) * total
    ring0
  have decomposition := evaluate_root_mul_sub function mapZero mapAdd point value
  have errorsEqual : sumFin (fun row => sumFin (fun column => errors row column * point ^ row.val)) =
      sumFin (fun row => sumFin (errors row) * point ^ row.val) :=
    sumFin_congr (fun _ => sumFin_mul_right _ _)
  change _ = sumFin (fun column => function (value.matrix column cyclic.origin) * columns column) +
    sumFin (fun row => sumFin (fun column => errors row column * point ^ row.val)) at decomposition
  rewrite [errorsEqual] at decomposition
  rewrite [decomposition]
  apply (Norm.Bounds.normSq_add_le_two _ _).trans
  apply (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct mainBound errorsBound) (by decide : (0 : Rational) ≤ 2)).trans
  apply Eq.le
  change 2 * ((factor * gain * residual) * total +
    (factor * factor * error * ceiling * SquareMatrix.Weight.total parent generator) * total) =
      (2 * (factor * gain * residual +
        (factor * factor * error * ceiling) * SquareMatrix.Weight.total parent generator)) * total
  ring0

end Purelib.Algebra.Monogenic.Cyclic.Element

end
