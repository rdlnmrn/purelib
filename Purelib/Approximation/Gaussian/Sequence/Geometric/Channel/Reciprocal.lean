module

import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Sequence.Geometric.Channel
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Data.Gaussian.Norm

open Purelib

open Purelib.Approximation.Gaussian.Sequence.Geometric

open Purelib.Approximation.Rational

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

namespace Purelib.Approximation.Gaussian.Sequence.Geometric.Channel
section Channel

/-- A displayed positive lower quadrance is precisely the finite evidence needed to transport a reciprocal channel. -/
def reciprocal {source : Nat →
  Data.Gaussian.Basic.Canonical} (channel : Channel source)
    (lower : Fraction.Rational) (lowerPositive : 0 < lower)
    (lowerBound : ∀ index, lower ≤ Basic.normSq (source index)) :
    Channel (fun index => Data.Gaussian.Field.inv (source index)) where
  errorScale := channel.errorScale * (lower⁻¹ * lower⁻¹)
  errorScale_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct channel.errorScale_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Field.inv_pos_direct lowerPositive).le
        (Fraction.Order.Field.inv_pos_direct lowerPositive).le)
  later_close := by
    intro earlier later order
    have laterNonzero : source later ≠ 0 := by
      intro zero
      have bound := lowerBound later
      rw [zero, Basic.normSq_zero] at bound
      exact (not_le_of_gt lowerPositive) bound
    have earlierNonzero : source earlier ≠ 0 := by
      intro zero
      have bound := lowerBound earlier
      rw [zero, Basic.normSq_zero] at bound
      exact (not_le_of_gt lowerPositive) bound
    have laterInverseBound : Basic.normSq (Data.Gaussian.Field.inv (source later))
      ≤ lower⁻¹ := by
      rw [Data.Gaussian.Field.normSq_inv _ laterNonzero]
      exact Fraction.Order.Field.inv_le_inv_of_pos_direct lowerPositive
        (lowerBound later)
    have earlierInverseBound : Basic.normSq (Data.Gaussian.Field.inv (source
      earlier)) ≤ lower⁻¹ := by
      rw [Data.Gaussian.Field.normSq_inv _ earlierNonzero]
      exact Fraction.Order.Field.inv_le_inv_of_pos_direct lowerPositive
        (lowerBound earlier)
    have reverseDistance :
        Basic.normSq (source earlier - source later) =
          Basic.normSq (source later - source earlier) := by
      have identity : source earlier - source later =
          -(source later - source earlier) := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
            Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;> ring1
      rw [identity, Basic.normSq_neg]
    change Basic.normSq (Data.Gaussian.Field.inv (source later) -
      Data.Gaussian.Field.inv (source earlier)) ≤ _
    rw [Data.Gaussian.Field.inverse_sub_inverse_direct
      laterNonzero earlierNonzero, Basic.normSq_mul, Basic.normSq_mul,
      Data.Gaussian.Field.normSq_inv _ laterNonzero, Data.Gaussian.Field.normSq_inv _ earlierNonzero,
      reverseDistance]
    have inverseProductBound :
        Basic.normSq (Data.Gaussian.Field.inv (source later)) *
          Basic.normSq (Data.Gaussian.Field.inv (source earlier)) ≤
          lower⁻¹ * lower⁻¹ :=
      Fraction.Order.Arithmetic.mul_le_mul_direct laterInverseBound
        earlierInverseBound (Basic.normSq_nonneg _)
        (Fraction.Order.Field.inv_pos_direct lowerPositive).le
    calc
      (Basic.normSq (source later))⁻¹ *
          Basic.normSq (source later - source earlier) *
            (Basic.normSq (source earlier))⁻¹ =
        Basic.normSq (source later - source earlier) *
          (Basic.normSq (Data.Gaussian.Field.inv (source later)) *
            Basic.normSq (Data.Gaussian.Field.inv (source earlier))) := by
            rw [Data.Gaussian.Field.normSq_inv _ laterNonzero, Data.Gaussian.Field.normSq_inv _ earlierNonzero]
            calc
              ((Basic.normSq (source later))⁻¹ *
                    Basic.normSq (source later - source earlier)) *
                  (Basic.normSq (source earlier))⁻¹ =
                (Basic.normSq (source later - source earlier) *
                    (Basic.normSq (source later))⁻¹) *
                  (Basic.normSq (source earlier))⁻¹ := by
                    rw [Fraction.Field.mul_comm
                      (Basic.normSq (source later))⁻¹
                      (Basic.normSq (source later - source earlier))]
              _ = Basic.normSq (source later - source earlier) *
                  ((Basic.normSq (source later))⁻¹ *
                    (Basic.normSq (source earlier))⁻¹) :=
                Fraction.Field.mul_assoc _ _ _
      _ ≤
        Geometric.Basic.quarterRadius
            channel.errorScale earlier * (lower⁻¹ * lower⁻¹) :=
          Fraction.Order.Arithmetic.mul_le_mul_direct
            (channel.later_close order) inverseProductBound
            (Fraction.Order.Arithmetic.mul_nonneg_direct (Basic.normSq_nonneg _)
              (Basic.normSq_nonneg _))
            (Geometric.Basic.quarterRadius_nonneg
              channel.errorScale_nonneg earlier)
      _ = Geometric.Basic.quarterRadius
          (channel.errorScale * (lower⁻¹ * lower⁻¹)) earlier := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        calc
          (channel.errorScale * (1 / 4 : Fraction.Rational) ^ earlier) *
                (lower⁻¹ * lower⁻¹) =
              channel.errorScale *
                ((1 / 4 : Fraction.Rational) ^ earlier *
                  (lower⁻¹ * lower⁻¹)) :=
            Fraction.Field.mul_assoc _ _ _
          _ = channel.errorScale *
                ((lower⁻¹ * lower⁻¹) *
                  (1 / 4 : Fraction.Rational) ^ earlier) := by
            rw [Fraction.Field.mul_comm
              ((1 / 4 : Fraction.Rational) ^ earlier) (lower⁻¹ * lower⁻¹)]
          _ = (channel.errorScale * (lower⁻¹ * lower⁻¹)) *
                (1 / 4 : Fraction.Rational) ^ earlier :=
            (Fraction.Field.mul_assoc _ _ _).symm
  centerBound := lower⁻¹
  centerBound_nonneg :=
    (Fraction.Order.Field.inv_pos_direct lowerPositive).le
  bounded := by
    intro index
    have nonzero : source index ≠ 0 := by
      intro zero
      have bound := lowerBound index
      rw [zero, Basic.normSq_zero] at bound
      exact (not_le_of_gt lowerPositive) bound
    change Basic.normSq (Data.Gaussian.Field.inv (source index)) ≤ lower⁻¹
    rw [Data.Gaussian.Field.normSq_inv _ nonzero]
    exact Fraction.Order.Field.inv_le_inv_of_pos_direct lowerPositive
      (lowerBound index)

end Channel

end Purelib.Approximation.Gaussian.Sequence.Geometric.Channel

end
