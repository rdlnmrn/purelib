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

open Purelib.Data.Gaussian.Norm

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
    SquaredProbeSensitive chordalOmegaProbe 2 := by
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
  have probeDifference : chordalOmegaProbe left - chordalOmegaProbe right =
      (Basic.normSq first - Basic.normSq second) / denominator
        := by
    rw [chordalSq_omega_eq_weight, chordalSq_omega_eq_weight]
    change Basic.normSq left.q / leftWeight - Basic.normSq
      right.q / rightWeight =
      (Basic.normSq first - Basic.normSq second) / (leftWeight *
        rightWeight)
    calc
      Basic.normSq left.q / leftWeight - Basic.normSq right.q /
        rightWeight =
          (Basic.normSq left.q * rightWeight -
            Basic.normSq right.q * leftWeight) /
              (leftWeight * rightWeight) :=
        Fraction.Field.div_sub_div_direct
          (Basic.normSq left.q) leftWeight (Basic.normSq
            right.q) rightWeight
          leftWeightPositive.ne' rightWeightPositive.ne'
      _ = (Basic.normSq first - Basic.normSq second) /
          (leftWeight * rightWeight) := by
        apply congrArg (fun numerator =>
          numerator / (leftWeight * rightWeight))
        dsimp only [first, second, leftWeight, rightWeight,
          Proj.weight]
        rw [Basic.normSq_mul, Basic.normSq_mul]
        ring1
  have crossIdentity : first - second =
      -(Proj.cross left right) := by
    apply Data.Gaussian.Basic.ext <;>
      dsimp only [first, second, Proj.cross] <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re,
        Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;>
      ring1
  have numeratorBound :
      (Basic.normSq first - Basic.normSq second) ^ 2 ≤
        2 * Basic.normSq (Proj.cross left right) * denominator := by
    have differenceBound := Data.Gaussian.normSq_difference_sq_le_two_mul first second
    rw [crossIdentity, Basic.normSq_neg] at differenceBound
    calc
      (Basic.normSq first - Basic.normSq second) ^ 2 ≤
          2 * Basic.normSq (Proj.cross left right) *
            (Basic.normSq first + Basic.normSq second) :=
              differenceBound
      _ ≤ 2 * Basic.normSq (Proj.cross left right) *
          denominator :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (crossProductNorms_le_weightProduct left right)
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (Basic.normSq_nonneg (Proj.cross left right)))
  have quotientSquare :
      ((Basic.normSq first - Basic.normSq second) / denominator)
        ^ 2 =
        (Basic.normSq first - Basic.normSq second) ^ 2 /
          denominator ^ 2 := by
    calc
      ((Basic.normSq first - Basic.normSq second) / denominator)
        ^ 2 =
          ((Basic.normSq first - Basic.normSq second) /
            denominator) *
            ((Basic.normSq first - Basic.normSq second) /
              denominator) := by ring1
      _ = ((Basic.normSq first - Basic.normSq second) *
          (Basic.normSq first - Basic.normSq second)) /
            (denominator * denominator) :=
        Fraction.Field.div_mul_div_direct _ _ _ _
      _ = (Basic.normSq first - Basic.normSq second) ^ 2 /
          (denominator * denominator) := by
        apply congrArg (fun numerator =>
          numerator / (denominator * denominator))
        ring1
      _ = (Basic.normSq first - Basic.normSq second) ^ 2 /
          denominator ^ 2 := by
        apply congrArg (fun divisor =>
          (Basic.normSq first - Basic.normSq second) ^ 2 /
            divisor)
        ring1
  rw [NaturalLp.rationalSeparation_sq, probeDifference,
    quotientSquare, Basic.chordalSq_eq_cross]
  have denominatorSquarePositive : 0 < denominator ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct denominatorPositive 2
  apply (Fraction.Order.Field.div_le_iff_pos
    denominatorSquarePositive).2
  calc
    (Basic.normSq first - Basic.normSq second) ^ 2 ≤
        2 * Basic.normSq (Proj.cross left right) * denominator :=
      numeratorBound
    _ = (2 *
        (Basic.normSq (Proj.cross left right) / denominator)) *
          denominator ^ 2 := by
      rw [pow_two]
      have cancel := Fraction.Field.div_mul_cancel_of_ne
        (Basic.normSq (Proj.cross left right)) denominator
        denominatorPositive.ne'
      have replaceCancel := congrArg (fun value =>
        2 * value * denominator) cancel
      calc
        2 * Basic.normSq (Proj.cross left right) * denominator =
            2 * ((Basic.normSq (Proj.cross left right) /
              denominator) * denominator) * denominator :=
          replaceCancel.symm
        _ = (2 *
            (Basic.normSq (Proj.cross left right) / denominator)) *
              (denominator * denominator) := by ring1

end Purelib.Geometry.Projective.Chordal.Probe

end
