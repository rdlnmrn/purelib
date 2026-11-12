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
import Purelib.Approximation.Rational.Geometric.Search
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

open Purelib.Data.Rat.Fraction.Order

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
open Purelib.Approximation.Rational.Geometric

variable {polynomial numerator : Polynomial} {leftCount rightCount : Nat}
  {left : ContinuedNeighborhood polynomial leftCount} {right : ContinuedNeighborhood polynomial rightCount}
  {leftIndex rightIndex : Nat} {start finish : Gaussian}

open Purelib in
open Purelib.Data.Rat in
open Purelib.Riemann.Normalization in
open Purelib.Riemann.Readings in
/-- An unflipped original inverse-model transition bounds the mismatch of its two primitive increments.

The two continued patches share the same numerator and retained edge endpoints. Their model bounds, original
numerator/inverse bounds and squared movement determine the comparison allowance. -/
theorem PrimitiveModel.increment_mismatch_le {pairs : Nat}
    (first : PrimitiveModel left leftIndex numerator pairs) (second : PrimitiveModel right rightIndex numerator pairs)
    (edge : EdgeTransition (left.base.refine leftIndex) (right.base.refine rightIndex) start finish)
    (unflipped : edge.sample.alignment.flip = false)
    (bounds : PrimitiveOverlapBounds (SeededPrimitiveBounds.clearance left.base) numerator) :
    normSq (first.primitive.value.eval finish - first.primitive.value.eval start +
      (second.primitive.value.eval start - second.primitive.value.eval finish)) ≤
      12 * ((left.base.refine leftIndex).bound + (right.base.refine rightIndex).bound) *
        bounds.weight pairs * normSq (finish - start) := by
  have estimate := Comparison.PrimitiveEdgeComparison.EdgeTransition.primitive_increment_le
    (pairs := pairs) edge bounds
    (first.primitive.onBox left.base.box) (second.primitive.onBox right.base.box)
    first.coefficient_eq (fun point => by cases pairs <;> exact second.coefficient_eq point)
    (first := 1) (last := 0) ⟨by decide, le_rfl⟩ ⟨le_rfl, by decide⟩
  have sign : edge.sign = 1 := by unfold EdgeTransition.sign; rw [unflipped]; rfl
  rw [sign, _root_.one_mul, InverseModelEdgeTransition.line_one, InverseModelEdgeTransition.line_zero] at estimate
  dsimp only [DensePrimitive.onBox] at estimate
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
    (right : ContinuedNeighborhood polynomial rightCount) (numerator : Polynomial) (start finish : Gaussian)
    (pairs : optParam Nat 0) where
  /-- The exact original primitive overlap bounds from the left retained clearance and common numerator. -/ bounds :
    PrimitiveOverlapBounds (SeededPrimitiveBounds.clearance left.base) numerator
  /-- The cached original mismatch scale before geometric refinement. -/ scale : Coordinate
  /-- The scale uses the original model-bound sum, actual pair-indexed overlap weight and endpoint squared movement. -/
  scale_eq : scale = 12 * (left.base.model.bound + right.base.model.bound) *
    bounds.weight pairs * normSq (finish - start)

constructive_injectivity PrimitivePairBudget

namespace PrimitivePairBudget

variable {pairs : Nat}

open Purelib.Riemann.Readings in
/-- Cache the original overlap bounds and their exact endpoint-weighted mismatch scale. -/
def build (left : ContinuedNeighborhood polynomial leftCount) (right : ContinuedNeighborhood polynomial rightCount)
    (numerator : Polynomial) (start finish : Gaussian) (pairs : optParam Nat 0) :
    PrimitivePairBudget left right numerator start finish pairs :=
  let bounds := PrimitiveOverlapBounds.build (SeededPrimitiveBounds.clearance left.base) numerator
  match pairs with
  | 0 => ⟨bounds, 12 * (left.base.model.bound + right.base.model.bound) *
      (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start), rfl⟩
  | remaining + 1 => ⟨bounds, 12 * (left.base.model.bound + right.base.model.bound) *
      bounds.weight (remaining + 1) * normSq (finish - start), rfl⟩

open Purelib.Data.Rat in
/-- The original retained numerator, inverse and odd-power overlap weight is nonnegative. -/
private theorem weight_nonnegative (budget : PrimitivePairBudget left right numerator start finish pairs) :
    0 ≤ budget.bounds.weight pairs := budget.bounds.weight_nonnegative pairs

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The original cached primitive-pair mismatch scale is nonnegative. -/
theorem scale_nonnegative (budget : PrimitivePairBudget left right numerator start finish pairs) :
    0 ≤ budget.scale := by
  rw [budget.scale_eq]
  exact Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg left.base.model.bound_nonnegative right.base.model.bound_nonnegative))
      budget.weight_nonnegative) (normSq_nonneg _)

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Normalization in
/-- The original unflipped primitive increment mismatch is bounded by the retained geometric quarter allowance.

The common comparison index is covered independently by both model indices; the same original numerator bounds and edge
endpoints determine the decaying scale. -/
theorem increment_le (budget : PrimitivePairBudget left right numerator start finish pairs)
    (first : PrimitiveModel left leftIndex numerator pairs) (second : PrimitiveModel right rightIndex numerator pairs)
    (edge : EdgeTransition (left.base.refine leftIndex) (right.base.refine rightIndex) start finish)
    (unflipped : edge.sample.alignment.flip = false) (index : Nat)
    (leftLater : index ≤ leftIndex) (rightLater : index ≤ rightIndex) :
    normSq (first.primitive.value.eval finish - first.primitive.value.eval start +
      (second.primitive.value.eval start - second.primitive.value.eval finish)) ≤ quarterRadius
        budget.scale index := by
  apply (PrimitiveModel.increment_mismatch_le first second edge unflipped budget.bounds).trans
  have leftBound : (left.base.refine leftIndex).bound ≤ quarterRadius left.base.model.bound index := by
    rw [OwnerSeededInverseRoot.SeededNeighborhood.refine, Model.refine_bound]
    exact quarterRadius_antitone left.base.model.bound_nonnegative leftLater
  have rightBound : (right.base.refine rightIndex).bound ≤ quarterRadius right.base.model.bound index :=
    by
    rw [OwnerSeededInverseRoot.SeededNeighborhood.refine, Model.refine_bound]
    exact quarterRadius_antitone right.base.model.bound_nonnegative rightLater
  calc
    _ ≤ 12 * (quarterRadius left.base.model.bound index + quarterRadius
      right.base.model.bound index) *
        budget.bounds.weight pairs * normSq (finish - start) :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add leftBound rightBound) (by decide))
          budget.weight_nonnegative) (normSq_nonneg _)
    _ = _ := by
      rw [budget.scale_eq]
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

section

open Purelib.Data.Rat

/-- Compute one retained finite request for the same cached primitive-pair mismatch scale.

The original Selection stores its quotient, ceiling, binary fuel, selected
stage and actual attained allowance. Neither inverse model, numerator
bound, endpoint reading nor primitive polynomial is reconstructed.
-/
def choose (budget : PrimitivePairBudget left right numerator start finish pairs) (current : Nat)
    (target : Fraction.Rational) (positive : 0 < target) : Search.Selection budget.scale current target :=
  Search.Selection.build budget.scale budget.scale_nonnegative current target positive

/-- Actual independently refined primitive increments meet their same retained selected allowance.

Both supplied models cover the actual chosen stage. The unflipped
transition concerns those exact original model values and ordered edge
endpoints; the cached selection is not recomputed by this bound.
-/
theorem selected_increment_le (budget : PrimitivePairBudget left right numerator start finish pairs)
    {current : Nat} {target : Fraction.Rational} (selection : Search.Selection budget.scale current target)
    (first : PrimitiveModel left leftIndex numerator pairs) (second : PrimitiveModel right rightIndex numerator pairs)
    (edge : EdgeTransition (left.base.refine leftIndex) (right.base.refine rightIndex) start finish)
    (unflipped : edge.sample.alignment.flip = false)
    (leftLater : selection.stage ≤ leftIndex) (rightLater : selection.stage ≤ rightIndex) :
    normSq (first.primitive.value.eval finish - first.primitive.value.eval start +
      (second.primitive.value.eval start - second.primitive.value.eval finish)) ≤ selection.allowance :=
  (budget.increment_le first second edge unflipped selection.stage leftLater rightLater).trans_eq
    selection.allowance_eq.symm

/-- The same actual primitive increments strictly meet the target of their retained finite selection. -/
theorem selected_increment_lt (budget : PrimitivePairBudget left right numerator start finish pairs)
    {current : Nat} {target : Fraction.Rational} (selection : Search.Selection budget.scale current target)
    (first : PrimitiveModel left leftIndex numerator pairs) (second : PrimitiveModel right rightIndex numerator pairs)
    (edge : EdgeTransition (left.base.refine leftIndex) (right.base.refine rightIndex) start finish)
    (unflipped : edge.sample.alignment.flip = false)
    (leftLater : selection.stage ≤ leftIndex) (rightLater : selection.stage ≤ rightIndex) :
    normSq (first.primitive.value.eval finish - first.primitive.value.eval start +
      (second.primitive.value.eval start - second.primitive.value.eval finish)) < target :=
  (budget.selected_increment_le selection first second edge unflipped leftLater rightLater).trans_lt
    selection.accurate
end

end PrimitivePairBudget

set_option genInjectivity false in
/-- Both original continued patches contain the exact edge endpoints and retain their common primitive comparison
budget.

The four containment witnesses remain attached to their respective original patches; the numerator and ordered endpoints
index the same cached pair budget. -/
structure PrimitivePairGeometry (left : ContinuedNeighborhood polynomial leftCount)
    (right : ContinuedNeighborhood polynomial rightCount) (numerator : Polynomial) (start finish : Gaussian)
    (pairs : optParam Nat 0) where
  /-- The original left patch contains the exact retained starting point. -/ leftStart : left.box.Contains start
  /-- The original left patch contains the exact retained finishing point. -/ leftFinish : left.box.Contains finish
  /-- The original right patch contains the exact retained starting point. -/ rightStart : right.box.Contains start
  /-- The original right patch contains the exact retained finishing point. -/ rightFinish : right.box.Contains finish
  /-- The retained pair budget for these exact original patches, numerator and ordered endpoints. -/ budget :
    PrimitivePairBudget left right numerator start finish pairs

constructive_injectivity PrimitivePairGeometry

end Purelib.Riemann.Integration.ContinuedPrimitiveOverlap
