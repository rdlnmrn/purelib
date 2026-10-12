module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Chordal.Basic
public import Purelib.Geometry.Projective.Chordal.Probe.Omega
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Hermitian

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Data.Rat.Distance

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Chordal

open Purelib.Geometry.Projective.Line.Hermitian

section
@[expose] public section

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

namespace Purelib.Geometry.Projective.Chordal.Probe

/-- Squared output separation of the nonconstant `omega`-distance probe is at most twice the squared chordal separation
of its valid inputs. -/
theorem chordalOmegaProbe_squaredSensitive :
    Probe.SquaredProbeSensitive Probe.chordalOmegaProbe 2 := by
  intro left right leftValid rightValid
  let leftWeight := Proj.weight left
  let rightWeight := Proj.weight right
  let denominator := leftWeight * rightWeight
  let first := left.q * right.p
  let second := right.q * left.p
  have leftWeightPositive : 0 < leftWeight :=
    Proj.weight_pos leftValid
  have rightWeightPositive : 0 < rightWeight :=
    Proj.weight_pos rightValid
  have denominatorPositive : 0 < denominator :=
    Fraction.Order.Arithmetic.mul_pos_direct leftWeightPositive
      rightWeightPositive
  have probeDifference : Probe.chordalOmegaProbe left - Probe.chordalOmegaProbe right =
      (Data.Gaussian.Norm.Basic.normSq first - Data.Gaussian.Norm.Basic.normSq second) / denominator
        := by
    rw [Probe.chordalSq_omega_eq_weight, Probe.chordalSq_omega_eq_weight]
    change Data.Gaussian.Norm.Basic.normSq left.q / leftWeight - Data.Gaussian.Norm.Basic.normSq
      right.q / rightWeight =
      (Data.Gaussian.Norm.Basic.normSq first - Data.Gaussian.Norm.Basic.normSq second) / (leftWeight *
        rightWeight)
    calc
      Data.Gaussian.Norm.Basic.normSq left.q / leftWeight - Data.Gaussian.Norm.Basic.normSq right.q /
        rightWeight =
          (Data.Gaussian.Norm.Basic.normSq left.q * rightWeight -
            Data.Gaussian.Norm.Basic.normSq right.q * leftWeight) /
              (leftWeight * rightWeight) :=
        Fraction.Field.div_sub_div_direct
          (Data.Gaussian.Norm.Basic.normSq left.q) leftWeight (Data.Gaussian.Norm.Basic.normSq
            right.q) rightWeight
          leftWeightPositive.ne' rightWeightPositive.ne'
      _ = (Data.Gaussian.Norm.Basic.normSq first - Data.Gaussian.Norm.Basic.normSq second) /
          (leftWeight * rightWeight) := by
        apply congrArg (fun numerator =>
          numerator / (leftWeight * rightWeight))
        dsimp only [first, second, leftWeight, rightWeight,
          Proj.weight]
        rw [Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul]
        ring1
  have crossIdentity : first - second =
      -(Proj.cross left right) := by
    apply Data.Gaussian.Basic.ext <;>
      dsimp only [first, second, Proj.cross] <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re,
        Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;>
      ring1
  have numeratorBound :
      (Data.Gaussian.Norm.Basic.normSq first - Data.Gaussian.Norm.Basic.normSq second) ^ 2 ≤
        2 * Data.Gaussian.Norm.Basic.normSq (Proj.cross left right) * denominator := by
    have differenceBound := Data.Gaussian.normSq_difference_sq_le_two_mul first second
    rw [crossIdentity, Data.Gaussian.Norm.Basic.normSq_neg] at differenceBound
    calc
      (Data.Gaussian.Norm.Basic.normSq first - Data.Gaussian.Norm.Basic.normSq second) ^ 2 ≤
          2 * Data.Gaussian.Norm.Basic.normSq (Proj.cross left right) *
            (Data.Gaussian.Norm.Basic.normSq first + Data.Gaussian.Norm.Basic.normSq second) :=
              differenceBound
      _ ≤ 2 * Data.Gaussian.Norm.Basic.normSq (Proj.cross left right) *
          denominator :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Probe.crossProductNorms_le_weightProduct left right)
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (Data.Gaussian.Norm.Basic.normSq_nonneg (Proj.cross left right)))
  have quotientSquare :
      ((Data.Gaussian.Norm.Basic.normSq first - Data.Gaussian.Norm.Basic.normSq second) / denominator)
        ^ 2 =
        (Data.Gaussian.Norm.Basic.normSq first - Data.Gaussian.Norm.Basic.normSq second) ^ 2 /
          denominator ^ 2 := by
    calc
      ((Data.Gaussian.Norm.Basic.normSq first - Data.Gaussian.Norm.Basic.normSq second) / denominator)
        ^ 2 =
          ((Data.Gaussian.Norm.Basic.normSq first - Data.Gaussian.Norm.Basic.normSq second) /
            denominator) *
            ((Data.Gaussian.Norm.Basic.normSq first - Data.Gaussian.Norm.Basic.normSq second) /
              denominator) := by ring1
      _ = ((Data.Gaussian.Norm.Basic.normSq first - Data.Gaussian.Norm.Basic.normSq second) *
          (Data.Gaussian.Norm.Basic.normSq first - Data.Gaussian.Norm.Basic.normSq second)) /
            (denominator * denominator) :=
        Fraction.Field.div_mul_div_direct _ _ _ _
      _ = (Data.Gaussian.Norm.Basic.normSq first - Data.Gaussian.Norm.Basic.normSq second) ^ 2 /
          (denominator * denominator) := by
        apply congrArg (fun numerator =>
          numerator / (denominator * denominator))
        ring1
      _ = (Data.Gaussian.Norm.Basic.normSq first - Data.Gaussian.Norm.Basic.normSq second) ^ 2 /
          denominator ^ 2 := by
        apply congrArg (fun divisor =>
          (Data.Gaussian.Norm.Basic.normSq first - Data.Gaussian.Norm.Basic.normSq second) ^ 2 /
            divisor)
        ring1
  rw [NaturalLp.rationalSeparation_sq, probeDifference,
    quotientSquare, Chordal.Basic.chordalSq_eq_cross]
  have denominatorSquarePositive : 0 < denominator ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct denominatorPositive 2
  apply (Fraction.Order.Field.div_le_iff_pos
    denominatorSquarePositive).2
  calc
    (Data.Gaussian.Norm.Basic.normSq first - Data.Gaussian.Norm.Basic.normSq second) ^ 2 ≤
        2 * Data.Gaussian.Norm.Basic.normSq (Proj.cross left right) * denominator :=
      numeratorBound
    _ = (2 *
        (Data.Gaussian.Norm.Basic.normSq (Proj.cross left right) / denominator)) *
          denominator ^ 2 := by
      rw [pow_two]
      have cancel := Fraction.Field.div_mul_cancel_of_ne
        (Data.Gaussian.Norm.Basic.normSq (Proj.cross left right)) denominator
        denominatorPositive.ne'
      have replaceCancel := congrArg (fun value =>
        2 * value * denominator) cancel
      calc
        2 * Data.Gaussian.Norm.Basic.normSq (Proj.cross left right) * denominator =
            2 * ((Data.Gaussian.Norm.Basic.normSq (Proj.cross left right) /
              denominator) * denominator) * denominator :=
          replaceCancel.symm
        _ = (2 *
            (Data.Gaussian.Norm.Basic.normSq (Proj.cross left right) / denominator)) *
              (denominator * denominator) := by ring1

end Purelib.Geometry.Projective.Chordal.Probe

end
