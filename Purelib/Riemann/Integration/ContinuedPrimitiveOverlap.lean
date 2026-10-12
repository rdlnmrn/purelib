module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison

import Purelib.Riemann.Normalization.ContinuedInverseRootOverlap
public import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Refinement rates for actual cached primitive increments

An unflipped inverse-model transition compares the two retained primitive
polynomials directly. Fixed numerator and inverse ceilings give a common
quarter-rate at independent later indices. No Taylor remainder is charged,
and the polynomial extensions used by the proof have no executable role.
-/

namespace Purelib.Riemann.Integration.ContinuedPrimitiveOverlap

open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate (DensePrimitive)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_antitone)

variable {polynomial numerator : Polynomial} {leftCount rightCount : Nat}
  {left : ContinuedNeighborhood polynomial leftCount} {right : ContinuedNeighborhood polynomial rightCount}
  {leftIndex rightIndex : Nat} {start finish : Gaussian}

open Purelib.Polynomial.Dense.Gaussian in
/-- Retain the original primitive polynomial on its full inverse-model box with a Taylor remainder certificate.

The value and derivative equation are unchanged; the explicit box Taylor bound certifies increments throughout the exact
original model box. -/
public def onModelBox {count index : Nat} {patch : ContinuedNeighborhood polynomial count}
    (model : PrimitiveModel patch index numerator) : Primitive.Certificate.DensePrimitive model.coefficient
      patch.base.box where
  value := model.primitive.value
  derivative_eq := model.primitive.derivative_eq
  remainderBound := Bounds.Box.Taylor.denseTaylorRemainderBound model.primitive.value patch.base.box
  remainderBound_nonnegative := (Bounds.Box.Taylor.denseTaylorRemainderBound_pos _ _).le
  increment_bound := by
    intro first last firstInside lastInside
    have estimate := Bounds.Box.Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
      model.primitive.value lastInside firstInside
    rw [model.primitive.derivative_eq] at estimate
    exact estimate

open Purelib in
open Purelib.Data.Rat in
open Purelib.Riemann.Normalization in
open Purelib.Riemann.Readings in
/-- An unflipped original inverse-model transition bounds the mismatch of its two primitive increments.

The two continued patches share the same numerator and retained edge endpoints. Their model bounds, original
numerator/inverse bounds and squared movement determine the comparison allowance. -/
theorem PrimitiveModel.increment_mismatch_le
    (first : PrimitiveModel left leftIndex numerator) (second : PrimitiveModel right rightIndex numerator)
    (edge : EdgeTransition (left.base.refine leftIndex) (right.base.refine rightIndex) start finish)
    (unflipped : edge.sample.alignment.flip = false)
    (bounds : PrimitiveOverlapBounds (SeededPrimitiveBounds.clearance left.base) numerator) :
    normSq (first.primitive.value.eval finish - first.primitive.value.eval start +
      (second.primitive.value.eval start - second.primitive.value.eval finish)) ≤
      12 * ((left.base.refine leftIndex).bound + (right.base.refine rightIndex).bound) *
        (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start) := by
  have estimate := Riemann.Comparison.PrimitiveEdgeComparison.EdgeTransition.primitive_increment_le edge bounds
    (onModelBox first) (onModelBox second)
    first.coefficient_eq second.coefficient_eq (first := 1) (last := 0) ⟨by decide, le_rfl⟩ ⟨le_rfl, by decide⟩
  have sign : edge.sign = 1 := by unfold EdgeTransition.sign; rw [unflipped]; rfl
  rw [sign, _root_.one_mul, InverseModelEdgeTransition.line_one, InverseModelEdgeTransition.line_zero] at estimate
  dsimp only [onModelBox] at estimate
  have same : first.primitive.value.eval finish - first.primitive.value.eval start +
      (second.primitive.value.eval start - second.primitive.value.eval finish) =
      (first.primitive.value.eval finish - first.primitive.value.eval start) -
        (second.primitive.value.eval finish - second.primitive.value.eval start) := by ring1
  rw [same]
  exact estimate.trans_eq (by
    have scalarZero : (1 : Fraction.Rational) - 0 = 1 := by ring1
    rw [scalarZero, one_pow, Fraction.Field.mul_one_direct])

set_option genInjectivity false in
open Purelib.Riemann.Readings in
/-- The retained overlap bounds and cached initial mismatch scale for two original primitive models.

The scale preserves both initial model bounds, the original numerator and inverse bounds, and the exact endpoint
movement squared. -/
structure PrimitivePairBudget (left : ContinuedNeighborhood polynomial leftCount)
    (right : ContinuedNeighborhood polynomial rightCount) (numerator : Polynomial) (start finish : Gaussian) where
  /-- The exact original primitive overlap bounds from the left retained clearance and common numerator. -/ bounds :
    PrimitiveOverlapBounds (SeededPrimitiveBounds.clearance left.base) numerator
  /-- The cached original mismatch scale before geometric refinement. -/ scale : Coordinate
  /-- The scale equals twelve times the original model-bound sum, numerator-inverse bound product and endpoint squared
    movement. -/ scale_eq : scale = 12 * (left.base.model.bound + right.base.model.bound) *
    (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start)

constructive_injectivity PrimitivePairBudget

namespace PrimitivePairBudget

open Purelib.Riemann.Readings in
/-- Cache the original overlap bounds and their exact endpoint-weighted mismatch scale. -/
def build (left : ContinuedNeighborhood polynomial leftCount) (right : ContinuedNeighborhood polynomial rightCount)
    (numerator : Polynomial) (start finish : Gaussian) : PrimitivePairBudget left right numerator start finish :=
  let bounds := PrimitiveOverlapBounds.build (SeededPrimitiveBounds.clearance left.base) numerator
  ⟨bounds, 12 * (left.base.model.bound + right.base.model.bound) *
    (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start), rfl⟩

open Purelib.Data.Rat in
/-- The retained numerator and inverse upper-bound product is nonnegative. -/
private theorem product_nonnegative (budget : PrimitivePairBudget left right numerator start finish) :
    0 ≤ budget.bounds.numeratorUpper * budget.bounds.inverseUpper :=
  Fraction.Order.Arithmetic.mul_nonneg_direct budget.bounds.numeratorUpper_nonnegative
    budget.bounds.inverseUpper_positive.le

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The original cached primitive-pair mismatch scale is nonnegative. -/
theorem scale_nonnegative (budget : PrimitivePairBudget left right numerator start finish) : 0 ≤ budget.scale := by
  rw [budget.scale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg left.base.model.bound_nonnegative right.base.model.bound_nonnegative))
      budget.product_nonnegative) (Basic.Canonical.normSq_nonneg _)

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Normalization in
/-- The original unflipped primitive increment mismatch is bounded by the retained geometric quarter allowance.

The common comparison index is covered independently by both model indices; the same original numerator bounds and edge
endpoints determine the decaying scale. -/
theorem increment_le (budget : PrimitivePairBudget left right numerator start finish)
    (first : PrimitiveModel left leftIndex numerator) (second : PrimitiveModel right rightIndex numerator)
    (edge : EdgeTransition (left.base.refine leftIndex) (right.base.refine rightIndex) start finish)
    (unflipped : edge.sample.alignment.flip = false) (index : Nat)
    (leftLater : index ≤ leftIndex) (rightLater : index ≤ rightIndex) :
    normSq (first.primitive.value.eval finish - first.primitive.value.eval start +
      (second.primitive.value.eval start - second.primitive.value.eval finish)) ≤ Geometric.Basic.quarterRadius
        budget.scale index := by
  apply (ContinuedPrimitiveOverlap.PrimitiveModel.increment_mismatch_le first second edge unflipped budget.bounds).trans
  have leftBound : (left.base.refine leftIndex).bound ≤ Geometric.Basic.quarterRadius left.base.model.bound index := by
    rw [OwnerSeededInverseRoot.SeededNeighborhood.refine, Model.refine_bound]
    exact quarterRadius_antitone left.base.model.bound_nonnegative leftLater
  have rightBound : (right.base.refine rightIndex).bound ≤ Geometric.Basic.quarterRadius right.base.model.bound index :=
    by
    rw [OwnerSeededInverseRoot.SeededNeighborhood.refine, Model.refine_bound]
    exact quarterRadius_antitone right.base.model.bound_nonnegative rightLater
  calc
    _ ≤ 12 * (Geometric.Basic.quarterRadius left.base.model.bound index + Geometric.Basic.quarterRadius
      right.base.model.bound index) *
        (budget.bounds.numeratorUpper * budget.bounds.inverseUpper) * normSq (finish - start) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add leftBound rightBound) (by decide))
          budget.product_nonnegative) (Basic.Canonical.normSq_nonneg _)
    _ = _ := by
      rw [budget.scale_eq]
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

end PrimitivePairBudget

set_option genInjectivity false in
/-- Both original continued patches contain the exact edge endpoints and retain their common primitive comparison
budget.

The four containment witnesses remain attached to their respective original patches; the numerator and ordered endpoints
index the same cached pair budget. -/
structure PrimitivePairGeometry (left : ContinuedNeighborhood polynomial leftCount)
    (right : ContinuedNeighborhood polynomial rightCount) (numerator : Polynomial) (start finish : Gaussian) where
  /-- The original left patch contains the exact retained starting point. -/ leftStart : left.box.Contains start
  /-- The original left patch contains the exact retained finishing point. -/ leftFinish : left.box.Contains finish
  /-- The original right patch contains the exact retained starting point. -/ rightStart : right.box.Contains start
  /-- The original right patch contains the exact retained finishing point. -/ rightFinish : right.box.Contains finish
  /-- The retained pair budget for these exact original patches, numerator and ordered endpoints. -/ budget :
    PrimitivePairBudget left right numerator start finish

constructive_injectivity PrimitivePairGeometry

end Purelib.Riemann.Integration.ContinuedPrimitiveOverlap
