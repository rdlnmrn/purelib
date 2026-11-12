module
import Purelib.Approximation.Gaussian.Name.Coherent.Based
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Affine

public import Purelib.Riemann.Normalization.ContinuedInverseRoot
public import Purelib.Riemann.Normalization.InverseModelRootSamples
public import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

@[expose] public section

/-!
# Operational identification of polynomial overlap signs

Two patches naming the same operational root select the same polynomial
sheet, at arbitrary independent refinement indices. The proof requests only
one finite comparison of root candidates. Its normalized error budget does
not need an exact root or a lower bound for the refined polynomial values.
Generated model caches are accepted by their values at the overlap anchor.
-/

section

open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (Owner)
open Purelib.Riemann.Normalization.InverseModelOverlap (OverlapSample)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical

namespace Purelib.Riemann.Normalization.ContinuedInverseRootOverlap

open Purelib.Data in
/-- Two inverse values close to the same normalized root choose the same nearest sheet.

Each squared mismatch is at most one divided by 32; the resulting difference norm is no greater than the sum norm. -/
private theorem nearest_of_common_mismatch {root left right : Gaussian}
    (leftSmall : normSq (1 - root * left) ≤ 1 / 32)
    (rightSmall : normSq (1 - root * right) ≤ 1 / 32) :
    normSq (left - right) ≤ normSq (left + right) := by
  have rootNonzero : root ≠ 0 := by
    intro zero
    rw [zero, Gaussian.Basic.zero_mul, Gaussian.Basic.sub_zero, normSq_one] at leftSmall
    exact (not_lt_of_ge leftSmall) (by decide +kernel : (1 / 32 : Coordinate) < 1)
  have lower : (15 / 32 : Coordinate) ≤ normSq (root * left) := by
    have bound := Gaussian.Norm.Bounds.half_normSq_sub_le_normSq_sub (1 : Gaussian) (1 - root * left)
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at bound
    rw [show (1 : Gaussian) - (1 - root * left) = root * left by ring1, normSq_one] at bound
    exact (show (15 / 32 : Coordinate) = 1 / 2 - 1 / 32 by decide +kernel).trans_le
      ((Arithmetic.sub_le_sub_left_direct leftSmall _).trans bound)
  have difference : normSq (root * (left - right)) ≤ normSq (root * left) := by
    calc
      _ = normSq ((1 - root * right) - (1 - root * left)) := congrArg normSq (by ring1)
      _ ≤ 2 * (normSq (1 - root * right) + normSq (1 - root * left)) := (by
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using (Gaussian.Norm.Bounds.normSq_sub_le_two _ _))
      _ ≤ 2 * (1 / 32 + 1 / 32 : Coordinate) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add rightSmall leftSmall) (by decide)
      _ ≤ 15 / 32 := by decide +kernel
      _ ≤ _ := lower
  have close : normSq (left - right) ≤ normSq left := by
    rw [normSq_mul, normSq_mul, Rat.Fraction.Field.mul_comm (normSq
      root),
      Rat.Fraction.Field.mul_comm (normSq root)] at difference
    exact Arithmetic.le_of_mul_le_mul_right_direct difference (by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using (Gaussian.Norm.Basic.normSq_pos rootNonzero))
  apply Arithmetic.le_of_add_le_add_right_direct (c := normSq (left - right))
  calc
    _ = 2 * normSq (left - right) := by ring1
    _ ≤ 2 * normSq left := Arithmetic.mul_le_mul_of_nonneg_left_direct close (by decide)
    _ ≤ 2 * (normSq left + normSq right) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct (le_add_of_nonneg_right
        (normSq_nonneg _)) (by decide)
    _ = _ := by
      simp only [normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im];
      ring1

open Purelib.Approximation in
open Purelib.Data in
/-- One actual finite comparison transfers two normalized sample bounds to the original nearest-sheet inequality. -/
private theorem nearest_of_equivalent_samples (first last : Gaussian.Sequence.ApproximationData)
    (equivalent : Gaussian.Equivalence.Equivalent first last) (firstStart lastStart : Nat)
    (left right : InverseRootPolynomial.Gaussian)
    (leftSmall : ∀ index, firstStart ≤ index → normSq (1 - first.sample index * left) ≤ 1 / 32)
    (rightSmall : ∀ index, lastStart ≤ index → normSq (1 - last.sample index * right) ≤ 1 / 128) :
    normSq (left - right) ≤ normSq (left + right) := by
  let scale := normSq right + 1
  have scalePositive : 0 < scale := lt_of_lt_of_le (by decide +kernel : (0 : Coordinate) < 1)
    (le_add_of_nonneg_left (normSq_nonneg _))
  let target : Coordinate := (1 / 128) / scale
  have targetPositive : 0 < target := Field.div_pos_direct (by decide +kernel) scalePositive
  let comparison := equivalent.compare firstStart lastStart target targetPositive
  let firstValue := first.sample comparison.leftIndex
  let secondValue := last.sample comparison.rightIndex
  have firstMismatch := leftSmall comparison.leftIndex comparison.left_ge
  have secondMismatch := rightSmall comparison.rightIndex comparison.right_ge
  have close : normSq (firstValue - secondValue) ≤ target := by
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, firstValue, secondValue] using
      (comparison.close (Nat.le_refl _) (Nat.le_refl _)).le
  have multiplied : normSq ((firstValue - secondValue) * right) ≤ 1 / 128 := by
    rw [normSq_mul]
    calc
      _ ≤ target * normSq right :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct close (normSq_nonneg _)
      _ ≤ target * scale := Arithmetic.mul_le_mul_of_nonneg_left_direct
        (le_add_of_nonneg_right (by decide +kernel : (0 : Coordinate) ≤ 1)) targetPositive.le
      _ = 1 / 128 := Rat.Fraction.Field.div_mul_cancel_of_ne _ _ scalePositive.ne'
  apply nearest_of_common_mismatch firstMismatch
  calc
    _ = normSq ((1 - secondValue * right) - (firstValue - secondValue) * right) :=
      congrArg normSq (by ring1)
    _ ≤ 2 * (normSq (1 - secondValue * right) + normSq ((firstValue - secondValue) * right)) := by
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
        (Gaussian.Norm.Bounds.normSq_sub_le_two _ _)
    _ ≤ 2 * (1 / 128 + 1 / 128 : Coordinate) := Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct secondMismatch multiplied) (by decide +kernel)
    _ = 1 / 32 := by decide +kernel

end Purelib.Riemann.Normalization.ContinuedInverseRootOverlap

section

variable {polynomial : Polynomial} {leftCount rightCount : Nat}
  {left : ContinuedNeighborhood polynomial leftCount} {right : ContinuedNeighborhood polynomial rightCount}
  {point : Gaussian}

namespace Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

open Purelib.Approximation
open Purelib.Data
/-- Operationally equivalent roots select the same polynomial sheet at independent refinement indices.

The shared point lies in both continuation boxes. A finite root comparison proves the nearestness inequality without
changing either retained process or model. -/
theorem equivalent_nearest (first
  : Point left point) (second : Point right point)
    (leftInside : left.box.Contains point) (rightInside : right.box.Contains point)
    (roots : Gaussian.Equivalence.NamedEquivalent first.certificate.value.name second.certificate.value.name)
    (leftIndex rightIndex : Nat) :
    normSq ((left.base.refine leftIndex).value.eval point - (right.base.refine rightIndex).value.eval point) ≤
      normSq ((left.base.refine leftIndex).value.eval point + (right.base.refine rightIndex).value.eval point) := by
  let firstRoot := first.certificate.value.based (first.residualState (1 / 4096) (by decide +kernel))
  let secondRoot := second.certificate.value.based (second.residualState (1 / 4096) (by decide +kernel))
  let equivalent := Gaussian.Equivalence.NamedEquivalent.trans
    (first.certificate.value.basedEquivalent (first.residualState (1 / 4096) (by decide +kernel))).symm
    (Gaussian.Equivalence.NamedEquivalent.trans roots
      (second.certificate.value.basedEquivalent (second.residualState (1 / 4096) (by decide +kernel))))
  apply ContinuedInverseRootOverlap.nearest_of_equivalent_samples
    (Gaussian.Name.Sampling.approximation firstRoot.name) (Gaussian.Name.Sampling.approximation secondRoot.name)
    equivalent 0 0 ((left.base.refine leftIndex).value.eval point) ((right.base.refine rightIndex).value.eval point)
  · intro index _
    have possible := Gaussian.Process.Sampling.witnessAt_possible_start
      firstRoot.name.process firstRoot.name.state index
    have mismatch := first.polynomial_mismatch leftInside (1 / 4096) (by decide +kernel) le_rfl possible leftIndex
    exact (mismatch.trans ((Arithmetic.add_le_add_direct
      (Rational.Geometric.Basic.quarterRadius_le_scale (by decide +kernel) leftIndex) le_rfl).trans_eq
        (by decide +kernel : (1 / 256 : Coordinate) + 16 * (1 / 4096) = 1 / 128))).trans (by decide +kernel)
  · intro index _
    have possible := Gaussian.Process.Sampling.witnessAt_possible_start
      secondRoot.name.process secondRoot.name.state index
    have mismatch := second.polynomial_mismatch rightInside (1 / 4096) (by decide +kernel) le_rfl possible rightIndex
    exact mismatch.trans ((Arithmetic.add_le_add_direct
      (Rational.Geometric.Basic.quarterRadius_le_scale (by decide +kernel) rightIndex) le_rfl).trans_eq
        (by decide +kernel : (1 / 256 : Coordinate) + 16 * (1 / 4096) = 1 / 128))

/-- Actual finite samples of one original inverse model and an operationally equal continued root select the same sheet.

The model cache supplies its exact original root samples and containment.
A single finite comparison to the continued root's actual residual state
pays the normalized sample mismatch, at independent model indices. The
model, polynomial, numerical caches and continued owner are all retained.
-/
theorem samples_nearest {leftBox : InverseRootPolynomial.Box}
    {model : Model polynomial leftBox} (data : InverseModelRootSamples.RootSamples model point)
    (small : model.bound ≤ 1 / 256) (leftInside : leftBox.Contains point)
    (second : Point right point) (rightInside : right.box.Contains point)
    (roots : Gaussian.Equivalence.Equivalent (data.approximation small leftInside)
      (Gaussian.Name.Sampling.approximation second.certificate.value.name)) (leftIndex rightIndex : Nat) :
    normSq ((model.refine (leftIndex + 2)).value.eval point - (right.base.refine rightIndex).value.eval point) ≤
      normSq ((model.refine (leftIndex + 2)).value.eval point + (right.base.refine rightIndex).value.eval point) := by
  let secondRoot := second.certificate.value.based (second.residualState (1 / 4096) (by decide +kernel))
  let equivalent := roots.trans
    (second.certificate.value.basedEquivalent (second.residualState (1 / 4096) (by decide +kernel)))
  apply ContinuedInverseRootOverlap.nearest_of_equivalent_samples (data.approximation small leftInside)
    (Gaussian.Name.Sampling.approximation secondRoot.name) equivalent (leftIndex + 2) 0
    ((model.refine (leftIndex + 2)).value.eval point) ((right.base.refine rightIndex).value.eval point)
  · intro index later
    exact data.sample_polynomial_mismatch small leftInside leftIndex index later
  · intro index _
    have possible := Gaussian.Process.Sampling.witnessAt_possible_start
      secondRoot.name.process secondRoot.name.state index
    have mismatch := second.polynomial_mismatch rightInside (1 / 4096) (by decide +kernel) le_rfl possible rightIndex
    exact mismatch.trans ((Arithmetic.add_le_add_direct
      (Rational.Geometric.Basic.quarterRadius_le_scale (by decide +kernel) rightIndex) le_rfl).trans_eq
        (by decide +kernel : (1 / 256 : Coordinate) + 16 * (1 / 4096) = 1 / 128))

end Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

end

section
open Purelib.Riemann
open Purelib.Approximation

namespace Purelib.Riemann.Normalization.ContinuedInverseRootOverlap.OverlapSample

/-- Construct an unflipped overlap sample from operational root equivalence.

Retain the supplied model caches and their evaluation equations; execution computes only the two cached polynomial
values at the shared point. -/
def ofEquivalentPoints {polynomial : Polynomial} {leftCount rightCount : Nat}
    {left : ContinuedNeighborhood polynomial leftCount} {right : ContinuedNeighborhood polynomial rightCount}
    {point : Gaussian} (first : Point left point) (second : Point right
      point)
    (leftInside : left.box.Contains point) (rightInside : right.box.Contains point)
    (roots : Gaussian.Equivalence.NamedEquivalent first.certificate.value.name second.certificate.value.name)
    (leftIndex rightIndex : Nat) (leftModel : Model polynomial left.base.box) (rightModel : Model polynomial
      right.base.box)
    (leftEq : leftModel.value.eval point = (left.base.refine leftIndex).value.eval point)
    (rightEq : rightModel.value.eval point = (right.base.refine rightIndex).value.eval point) :
    OverlapSample leftModel rightModel point :=
  let leftValue := leftModel.value.eval point
  let rightValue := rightModel.value.eval point
  ⟨leftValue, rfl, rightValue, rfl, ⟨false, rightValue, rfl, by
    dsimp only [leftValue, rightValue]
    rw [leftEq, rightEq]
    exact Point.equivalent_nearest first second leftInside
      rightInside roots leftIndex rightIndex⟩⟩

end Purelib.Riemann.Normalization.ContinuedInverseRootOverlap.OverlapSample

namespace Purelib.Riemann.Normalization.ContinuedInverseRootOverlap.EdgeTransition

/-- Build a common-edge transition from root equivalence at its starting point.

Both endpoints lie in both continuation boxes, and the supplied cached models agree there with their selected
refinements. The starting overlap fixes the unflipped sign along the whole edge. -/
def ofEquivalentPoints {polynomial : Polynomial} {leftCount rightCount : Nat}
    {left : ContinuedNeighborhood polynomial leftCount} {right : ContinuedNeighborhood polynomial rightCount}
    {start finish : Gaussian} (first : Point left start) (second : Point
      right start)
    (leftStart : left.box.Contains start) (leftFinish : left.box.Contains finish)
    (rightStart : right.box.Contains start) (rightFinish : right.box.Contains finish)
    (roots : Gaussian.Equivalence.NamedEquivalent first.certificate.value.name second.certificate.value.name)
    (leftIndex rightIndex : Nat) (leftModel : Model polynomial left.base.box) (rightModel : Model polynomial
      right.base.box)
    (leftEq : leftModel.value.eval start = (left.base.refine leftIndex).value.eval start)
    (rightEq : rightModel.value.eval start = (right.base.refine rightIndex).value.eval start) :
    EdgeTransition leftModel rightModel start finish where
  leftStart := left.box_refines.contains leftStart
  leftFinish := left.box_refines.contains leftFinish
  rightStart := right.box_refines.contains rightStart
  rightFinish := right.box_refines.contains rightFinish
  sample := OverlapSample.ofEquivalentPoints first second leftStart rightStart
    roots
    leftIndex rightIndex leftModel rightModel leftEq rightEq

end Purelib.Riemann.Normalization.ContinuedInverseRootOverlap.EdgeTransition

end

namespace Purelib.Riemann.Normalization.ContinuedInverseRootOverlap.EdgeTransition

open Purelib.Riemann in
open Purelib.Geometry in
/-- Bound the discrepancy between the original model polynomials along an unflipped common edge.

For a unit-interval parameter, the squared difference is at most six times the summed residual bounds times the left
polynomial's squared norm. -/
theorem unflipped_distance_le {polynomial : Polynomial} {leftBox rightBox : Box}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {start finish : Gaussian}
    (edge : EdgeTransition left right start finish) (unflipped : edge.sample.alignment.flip = false)
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    normSq (left.value.eval (Rational.Affine.line start (finish - start) parameter) -
      right.value.eval (Rational.Affine.line start (finish - start) parameter)) ≤
    6 * (left.bound + right.bound) * normSq (left.value.eval (Rational.Affine.line start (finish - start) parameter)) :=
      by
  have bound := EdgeTransition.sampleAt_distance_le edge parameter inside
  rw [EdgeTransition.sampleAt_selected edge] at bound
  have signEq : edge.sign = 1 := by
    unfold EdgeTransition.sign; rw [unflipped];
    rfl
  rw [signEq, _root_.one_mul] at bound
  exact bound

end Purelib.Riemann.Normalization.ContinuedInverseRootOverlap.EdgeTransition

end
