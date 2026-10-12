module
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Field.Defs

@[expose] public section

/-!
# Fixed overlap signs across finite polynomial refinement

Newton correction stays on the same local branch. Once models meet the
triple-overlap budget, their nearest-sign comparison is unchanged by any
independently selected finite refinement indices. The resulting overlap
cache reuses its original bit, rather than comparing the larger polynomials
again. This concerns polynomial sheets; identification with transported
operational owners remains a separate geometric obligation.
-/

namespace Purelib.Riemann.Normalization.InverseModelRefinementSigns

open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment OverlapSample)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A candidate within the reference's squared norm is at least as close as its negation. -/
theorem nearest_of_close {reference candidate : Gaussian}
    (close : normSq (reference - candidate) ≤ normSq reference) :
    normSq (reference - candidate) ≤ normSq (reference + candidate) := by
  apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct (c := normSq (reference - candidate))
  calc
    _ = 2 * normSq (reference - candidate) := by ring1
    _ ≤ 2 * normSq reference := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct close (by decide)
    _ ≤ 2 * (normSq reference + normSq candidate) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (le_add_of_nonneg_right (Basic.Canonical.normSq_nonneg _)) (by decide)
    _ = _ := by simp only [normSq, Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im]; ring1

namespace SignAlignment

open Purelib.Data.Gaussian in
/-- Reverse a sign alignment while retaining its exact Boolean sign.

The original reference becomes the candidate, with the same sign applied
to its value. Coordinate identities transport the retained nearestness
inequality in each Boolean branch. -/
def reverse {reference candidate : Gaussian} (alignment : SignAlignment reference candidate) :
    SignAlignment candidate reference where
  flip := alignment.flip
  value := if alignment.flip then -reference else reference
  value_eq := rfl
  nearest := by
    rcases alignment with ⟨flip, value, valueEq, nearest⟩
    rw [valueEq] at nearest
    cases flip
    · change normSq (reference - candidate) ≤ normSq (reference + candidate) at nearest
      change normSq (candidate - reference) ≤ normSq (candidate + reference)
      calc
        _ = normSq (reference - candidate) := by
          simp only [normSq, Basic.sub_re, Basic.sub_im]
          ring1
        _ ≤ normSq (reference + candidate) := nearest
        _ = _ := by
          simp only [normSq, Basic.add_re, Basic.add_im]
          ring1
    · change normSq (reference - -candidate) ≤ normSq (reference + -candidate) at nearest
      change normSq (candidate - -reference) ≤ normSq (candidate + -reference)
      calc
        _ = normSq (reference - -candidate) := by
          simp only [normSq, Basic.sub_re, Basic.sub_im, Basic.neg_re, Basic.neg_im]
          ring1
        _ ≤ normSq (reference + -candidate) := nearest
        _ = _ := by
          simp only [normSq, Basic.add_re, Basic.add_im, Basic.neg_re, Basic.neg_im]
          ring1

end SignAlignment

namespace Model

variable {polynomial : Polynomial} {box : Box}

/-- The original model's defining inverse-root residual satisfies its retained bound at a contained point. -/
private theorem residual_at (model : Model polynomial box) (point : Gaussian) (inside : box.Contains point) :
    normSq (1 - polynomial.eval point * (model.value.eval point) ^ 2) ≤ model.bound := by
  rw [← model.residual_eq]
  exact model.residualBound point inside

open Purelib.Approximation.Rational in
/-- Refining an original overlap-small model retains its one-over-256 bound. -/
private theorem refined_small (model : Model polynomial box) (small : model.bound ≤ 1 / 256) (index : Nat) :
    (model.refine index).bound ≤ 1 / 256 :=
  ((model.refine_bound index).trans_le
    (Geometric.Basic.quarterRadius_le_scale model.bound_nonnegative index)).trans small

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Normalization in
/-- The original Newton correction aligns with its input model without a sign flip.

The exact residual bound controls the correction distance, and the retained alignment uses the same original point and
box containment. -/
def stepAlignment (model : Model polynomial box) (point : Gaussian) (inside : box.Contains point) :
    SignAlignment (model.value.eval point) (model.step.value.eval point) := by
  refine ⟨false, model.step.value.eval point, rfl, nearest_of_close ?_⟩
  have correctionEq : model.step.value.eval point = model.value.eval point * (1 + half * model.residual.eval point) :=
    by
    dsimp only [InverseRootPolynomial.Model.step]
    rewrite [Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_add,
      Dense.Basic.DensePolynomial.eval_constant, Dense.Basic.DensePolynomial.eval_scale]
    exact Eq.refl _
  rw [correctionEq]
  have difference : model.value.eval point - model.value.eval point * (1 + half * model.residual.eval point) =
      -(model.value.eval point * (half * model.residual.eval point)) := by ring1
  rw [difference, Basic.Canonical.normSq_neg, Basic.Canonical.normSq_mul, Basic.Canonical.normSq_mul, show normSq half =
    (1 / 4 : Coordinate) by decide]
  have residual := (model.residualBound point inside).trans model.bound_small
  calc
    _ ≤ normSq (model.value.eval point) * ((1 / 4) * (1 / 16)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct residual (by decide)) (Basic.Canonical.normSq_nonneg
          _)
    _ ≤ normSq (model.value.eval point) * 1 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide +kernel) (Basic.Canonical.normSq_nonneg _)
    _ = _ := Fraction.Field.mul_one_direct _

open Purelib.Data.Gaussian in
open Purelib.Riemann.Normalization in
/-- Every refinement of an overlap-small original model aligns with it without a sign flip. -/
theorem refine_self_flip (model : Model polynomial box) (small : model.bound ≤ 1 / 256)
    (point : Gaussian) (inside : box.Contains point) (index : Nat) :
    (SignAlignment.build (model.value.eval point) ((model.refine index).value.eval point)).flip = false := by
  induction index with
  | zero =>
      change (SignAlignment.build (model.value.eval point) (model.value.eval point)).flip = false
      unfold SignAlignment.build
      rw [dif_pos (by rw [Basic.sub_self, Basic.Canonical.normSq_zero]; exact Basic.Canonical.normSq_nonneg _)]
  | succ index ih =>
      have composed := InverseModelOverlapCocycle.SignAlignment.cocycle
        (SignAlignment.build (model.value.eval point) ((model.refine index).value.eval point))
        ((InverseModelRefinementSigns.Model.stepAlignment (model.refine index)) point inside)
        (SignAlignment.build (model.value.eval point) ((model.refine (index + 1)).value.eval point))
        ((InverseModelRefinementSigns.Model.residual_at model) point inside)
          ((InverseModelRefinementSigns.Model.residual_at (model.refine index)) point inside)
        ((InverseModelRefinementSigns.Model.residual_at (model.refine (index + 1))) point inside)
        small ((InverseModelRefinementSigns.Model.refined_small model) small index)
          ((InverseModelRefinementSigns.Model.refined_small model) small (index + 1))
      rw [ih] at composed
      exact composed

end Model

namespace OverlapSample

variable {polynomial : Polynomial} {leftBox rightBox : Box}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {point : Gaussian}

open Purelib.Riemann.Normalization
/-- Refining both original overlap models preserves their exact retained alignment sign.

Both original models remain small on the same contained point; their separate refinement depths are retained without
changing the selected sign. -/
theorem refine_flip (sample : OverlapSample left right point)
    (leftInside : leftBox.Contains point) (rightInside : rightBox.Contains point)
    (leftSmall : left.bound ≤ 1 / 256) (rightSmall : right.bound ≤ 1 / 256)
    (leftIndex rightIndex : Nat) :
    (OverlapSample.build (left.refine leftIndex) (right.refine rightIndex) point).alignment.flip = sample.alignment.flip
      := by
  let leftSelf := SignAlignment.build (left.value.eval point) ((left.refine leftIndex).value.eval point)
  let old := SignAlignment.build (left.value.eval point) (right.value.eval point)
  let middle := SignAlignment.build ((left.refine leftIndex).value.eval point) (right.value.eval point)
  have first := InverseModelOverlapCocycle.SignAlignment.cocycle (InverseModelRefinementSigns.SignAlignment.reverse
    leftSelf) old middle
    ((InverseModelRefinementSigns.Model.residual_at (left.refine leftIndex)) point leftInside)
      ((InverseModelRefinementSigns.Model.residual_at left) point leftInside)
    ((InverseModelRefinementSigns.Model.residual_at right) point rightInside)
      ((InverseModelRefinementSigns.Model.refined_small left) leftSmall leftIndex) leftSmall rightSmall
  have selfFalse : (InverseModelRefinementSigns.SignAlignment.reverse leftSelf).flip = false :=
    (InverseModelRefinementSigns.Model.refine_self_flip left) leftSmall point leftInside leftIndex
  rw [selfFalse] at first
  have second := InverseModelOverlapCocycle.SignAlignment.cocycle middle
    (SignAlignment.build (right.value.eval point) ((right.refine rightIndex).value.eval point))
    (SignAlignment.build ((left.refine leftIndex).value.eval point) ((right.refine rightIndex).value.eval point))
    ((InverseModelRefinementSigns.Model.residual_at (left.refine leftIndex)) point leftInside)
      ((InverseModelRefinementSigns.Model.residual_at right) point rightInside)
    ((InverseModelRefinementSigns.Model.residual_at (right.refine rightIndex)) point rightInside)
    ((InverseModelRefinementSigns.Model.refined_small left) leftSmall leftIndex) rightSmall
      ((InverseModelRefinementSigns.Model.refined_small right) rightSmall rightIndex)
  rw [(InverseModelRefinementSigns.Model.refine_self_flip right) rightSmall point rightInside rightIndex,
      first] at second
  have oldBit : old.flip = sample.alignment.flip := (InverseModelEdgeTransition.OverlapSample.flip_eq_build sample
    leftInside rightInside).symm
  change (SignAlignment.build ((left.refine leftIndex).value.eval point) ((right.refine rightIndex).value.eval
    point)).flip = _
  rw [second, oldBit]
  cases sample.alignment.flip <;> rfl

/-- Build an overlap sample for exact refined-value readbacks while retaining the original alignment sign.

The two supplied model-value equalities identify the original refinements at their separate depths, and the retained
sign determines the same nearest candidate route. -/
def ofRefined (sample : OverlapSample left right point)
    (leftInside : leftBox.Contains point) (rightInside : rightBox.Contains point)
    (leftSmall : left.bound ≤ 1 / 256) (rightSmall : right.bound ≤ 1 / 256)
    (leftIndex rightIndex : Nat) (leftRefined : Model polynomial leftBox) (rightRefined : Model polynomial rightBox)
    (leftEq : leftRefined.value.eval point = (left.refine leftIndex).value.eval point)
    (rightEq : rightRefined.value.eval point = (right.refine rightIndex).value.eval point) :
    OverlapSample leftRefined rightRefined point :=
  let leftValue := leftRefined.value.eval point
  let rightValue := rightRefined.value.eval point
  ⟨leftValue, rfl, rightValue, rfl,
    ⟨sample.alignment.flip, if sample.alignment.flip then -rightValue else rightValue, rfl, by
      have same := InverseModelRefinementSigns.OverlapSample.refine_flip sample leftInside rightInside leftSmall
        rightSmall leftIndex rightIndex
      have retained : (SignAlignment.build leftValue rightValue).flip = sample.alignment.flip := by
        dsimp only [leftValue, rightValue]
        rw [leftEq, rightEq]
        exact same
      rw [← retained, ← (SignAlignment.build leftValue rightValue).value_eq]
      exact (SignAlignment.build leftValue rightValue).nearest⟩⟩

end OverlapSample

end Purelib.Riemann.Normalization.InverseModelRefinementSigns
