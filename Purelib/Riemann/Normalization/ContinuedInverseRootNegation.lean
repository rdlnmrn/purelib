module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Riemann.Normalization.ContinuedInverseRootOverlap
import Purelib.Riemann.RootContinuation.SquareRootNegation
import Purelib.Tactic.Ring
import Purelib.Approximation.Gaussian.Name.Coherent.Based
public import Purelib.Riemann.Normalization.ContinuedInverseRoot

public section

/-!
# Opposite operational roots fix the negative polynomial transition

One finite comparison of the actual root channels determines the opposite
sign of independently refined inverse polynomials. The existing finite
edge-sign theorem propagates this sign over the whole common straight edge.
-/

namespace Purelib.Riemann.Normalization.ContinuedInverseRootNegation

open Purelib.Data.Rat

open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

open Purelib.Data in
/-- Small residuals against one root force the unflipped nearest-sign relation.

If both squared mismatches are at most 1/32, the difference of the inverse readings is no larger in squared norm than
their sum. -/
private theorem nearest_of_mismatch {root left right : Gaussian}
    (leftSmall : normSq (1 - root * left) ≤ 1 / 32)
    (rightSmall : normSq (1 - root * right) ≤ 1 / 32) :
    normSq (left - right) ≤ normSq (left + right) := by
  have rootNonzero : root ≠ 0 := by
    intro zero
    rw [zero, Gaussian.Basic.zero_mul, Gaussian.Basic.sub_zero, Gaussian.Basic.Canonical.normSq_one] at leftSmall
    exact (not_lt_of_ge leftSmall) (by decide +kernel : (1 / 32 : Coordinate) < 1)
  have lower : (15 / 32 : Coordinate) ≤ normSq (root * left) := by
    have bound := Gaussian.Norm.Bounds.half_normSq_sub_le_normSq_sub (1 : Gaussian) (1 - root * left)
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at bound
    rw [show (1 : Gaussian) - (1 - root * left) = root * left by ring1, Gaussian.Basic.Canonical.normSq_one] at bound
    exact (show (15 / 32 : Coordinate) = 1 / 2 - 1 / 32 by decide +kernel).trans_le
      ((Rat.Fraction.Order.Arithmetic.sub_le_sub_left_direct leftSmall _).trans bound)
  have difference : normSq (root * (left - right)) ≤ normSq (root * left) := by
    calc
      _ = normSq ((1 - root * right) - (1 - root * left)) := congrArg normSq (by ring1)
      _ ≤ 2 * (normSq (1 - root * right) + normSq (1 - root * left)) := (by
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using (Gaussian.Norm.Bounds.normSq_sub_le_two _ _))
      _ ≤ 2 * (1 / 32 + 1 / 32 : Coordinate) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add rightSmall leftSmall) (by decide +kernel)
      _ ≤ 15 / 32 := by decide +kernel
      _ ≤ _ := lower
  have close : normSq (left - right) ≤ normSq left := by
    rw [Gaussian.Basic.Canonical.normSq_mul, Gaussian.Basic.Canonical.normSq_mul, Rat.Fraction.Field.mul_comm (normSq
      root),
      Rat.Fraction.Field.mul_comm (normSq root)] at difference
    exact Rat.Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct difference (by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using (Gaussian.Norm.Basic.normSq_pos rootNonzero))
  apply Rat.Fraction.Order.Arithmetic.le_of_add_le_add_right_direct (c := normSq (left - right))
  calc
    _ = 2 * normSq (left - right) := by ring1
    _ ≤ 2 * normSq left := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct close (by decide +kernel)
    _ ≤ 2 * (normSq left + normSq right) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (le_add_of_nonneg_right
        (Gaussian.Basic.Canonical.normSq_nonneg _)) (by decide +kernel)
    _ = _ := by
      simp only [normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im];
      ring1

namespace ContinuedNeighborhood.Point

variable {polynomial : Polynomial} {leftCount rightCount : Nat}
  {left : ContinuedNeighborhood polynomial leftCount} {right : ContinuedNeighborhood polynomial rightCount}
  {point : Gaussian}

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Opposite operational root names force the flipped nearest-sign relation.

One finite comparison of the actual retained root channels proves the relation for arbitrary independent
inverse-polynomial refinement indices at a common contained point. -/
theorem negative_nearest (first : Point left point) (second : Point right point)
    (leftInside : left.box.Contains point) (rightInside : right.box.Contains point)
    (roots : Gaussian.Equivalence.NamedEquivalent first.certificate.value.neg.name second.certificate.value.name)
    (leftIndex rightIndex : Nat) :
    normSq ((left.base.refine leftIndex).value.eval point + (right.base.refine rightIndex).value.eval point) ≤
      normSq ((left.base.refine leftIndex).value.eval point - (right.base.refine rightIndex).value.eval point) := by
  let firstRoot := first.certificate.value.based (first.residualState (1 / 4096) (by decide +kernel))
  let secondRoot := second.certificate.value.based (second.residualState (1 / 4096) (by decide +kernel))
  let equivalent := (RootContinuation.SquareRootNegation.neg_equivalent firstRoot first.certificate.value
    (first.certificate.value.basedEquivalent (first.residualState (1 / 4096) (by decide +kernel))).symm).trans
    (roots.trans (second.certificate.value.basedEquivalent (second.residualState (1 / 4096) (by decide +kernel))))
  let rightValue := (right.base.refine rightIndex).value.eval point
  let scale := normSq rightValue + 1
  have scalePositive : 0 < scale := lt_of_lt_of_le (by decide +kernel : (0 : Coordinate) < 1)
    (le_add_of_nonneg_left (Gaussian.Basic.Canonical.normSq_nonneg _))
  let target : Coordinate := (1 / 128) / scale
  have targetPositive : 0 < target := Rat.Fraction.Order.Field.div_pos_direct (by decide +kernel) scalePositive
  let comparison := equivalent.compare 0 0 target targetPositive
  let firstValue := (Gaussian.Name.Sampling.approximation firstRoot.name).sample comparison.leftIndex
  let secondValue := (Gaussian.Name.Sampling.approximation secondRoot.name).sample comparison.rightIndex
  have firstPossible := Gaussian.Process.Sampling.witnessAt_possible_start firstRoot.name.process firstRoot.name.state
    comparison.leftIndex
  have secondPossible := Gaussian.Process.Sampling.witnessAt_possible_start secondRoot.name.process
    secondRoot.name.state comparison.rightIndex
  have firstMismatch : normSq (1 - firstValue * (left.base.refine leftIndex).value.eval point) ≤ 1 / 128 :=
    (first.polynomial_mismatch leftInside (1 / 4096) (by decide +kernel) le_rfl firstPossible leftIndex).trans
      ((add_le_add (Rational.Geometric.Basic.quarterRadius_le_scale (by decide +kernel) leftIndex) le_rfl).trans_eq
        (by decide +kernel : (1 / 256 : Coordinate) + 16 * (1 / 4096) = 1 / 128))
  have secondMismatch : normSq (1 - secondValue * rightValue) ≤ 1 / 128 :=
    (second.polynomial_mismatch rightInside (1 / 4096) (by decide +kernel) le_rfl secondPossible rightIndex).trans
      ((add_le_add (Rational.Geometric.Basic.quarterRadius_le_scale (by decide +kernel) rightIndex) le_rfl).trans_eq
        (by decide +kernel : (1 / 256 : Coordinate) + 16 * (1 / 4096) = 1 / 128))
  have close : normSq (firstValue + secondValue) ≤ target := by
    have close := (comparison.close (Nat.le_refl _) (Nat.le_refl _)).le
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at close
    change normSq ((Gaussian.Name.Sampling.approximation firstRoot.neg.name).sample comparison.leftIndex -
      (Gaussian.Name.Sampling.approximation secondRoot.name).sample comparison.rightIndex) ≤ target at close
    rw [RootContinuation.SquareRootNegation.neg_sample] at close
    change normSq (-firstValue - secondValue) ≤ target at close
    rw [show -firstValue - secondValue = -(firstValue + secondValue) by ring1,
        Gaussian.Basic.Canonical.normSq_neg] at close
    exact close
  have multiplied : normSq ((firstValue + secondValue) * rightValue) ≤ 1 / 128 := by
    rw [Gaussian.Basic.Canonical.normSq_mul]
    calc
      _ ≤ target * normSq rightValue :=
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct close (Gaussian.Basic.Canonical.normSq_nonneg _)
      _ ≤ target * scale := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (le_add_of_nonneg_right (by decide +kernel : (0 : Coordinate) ≤ 1)) targetPositive.le
      _ = 1 / 128 := Rat.Fraction.Field.div_mul_cancel_of_ne _ _ scalePositive.ne'
  have mismatch : normSq (1 - firstValue * (-rightValue)) ≤ 1 / 32 := by
    calc
      _ = normSq ((1 - secondValue * rightValue) + (firstValue + secondValue) * rightValue) := congrArg normSq (by
        ring1)
      _ ≤ 2 * (normSq (1 - secondValue * rightValue) + normSq ((firstValue + secondValue) * rightValue)) := (by
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using (Gaussian.Norm.Bounds.normSq_add_le_two _ _))
      _ ≤ 2 * (1 / 128 + 1 / 128 : Coordinate) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add secondMismatch multiplied)
          (by decide +kernel)
      _ = 1 / 32 := by decide +kernel
  have nearest := nearest_of_mismatch (firstMismatch.trans (by decide +kernel : (1 / 128 : Coordinate) ≤ 1 / 32))
    mismatch
  have leftRead : normSq ((left.base.refine leftIndex).value.eval point - -rightValue) =
      normSq ((left.base.refine leftIndex).value.eval point + rightValue) := congrArg normSq (by ring1)
  exact leftRead.symm.trans_le (nearest.trans_eq (congrArg normSq
    (show (left.base.refine leftIndex).value.eval point + -rightValue =
      (left.base.refine leftIndex).value.eval point - rightValue by ring1)))

end ContinuedNeighborhood.Point

end Purelib.Riemann.Normalization.ContinuedInverseRootNegation
