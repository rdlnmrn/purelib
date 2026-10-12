module

public import Purelib.Approximation.Gaussian.Sequence.Geometric.Channel
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Data.Gaussian.Basic (Canonical)

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

/-- Certify the constant Gaussian rational sequence with zero movement scale.

The retained uniform centre bound is the exact squared norm of the displayed constant. -/
def exact (value :
  Canonical) : Channel (fun _ => value) where
  errorScale := 0
  errorScale_nonneg := le_rfl
  later_close := by
    intro earlier later order
    rw [_root_.sub_self, Data.Gaussian.Norm.Basic.normSq_zero,
      Geometric.Basic.quarterRadius_eq_mul_pow,
      Fraction.Field.zero_mul_direct]
  centerBound := Data.Gaussian.Norm.Basic.normSq value
  centerBound_nonneg := Data.Gaussian.Norm.Basic.normSq_nonneg value
  bounded := fun _ => le_rfl

/-- Transport a geometric channel along supplied pointwise equalities.

The original movement scale, centre bound and their certificates are retained. -/
def map {source target : Nat →
  Canonical} (channel : Channel source)
    (same : ∀ index, target index = source index) : Channel target where
  errorScale := channel.errorScale
  errorScale_nonneg := channel.errorScale_nonneg
  later_close := by
    intro earlier later order
    rw [same later, same earlier]
    exact channel.later_close order
  centerBound := channel.centerBound
  centerBound_nonneg := channel.centerBound_nonneg
  bounded := by
    intro index
    rw [same index]
    exact channel.bounded index

/-- Certify the pointwise sum of two Gaussian rational channels.

Both the movement scale and the uniform centre bound are twice the sum of the original bounds. -/
def add {left right : Nat →
  Canonical}
    (leftChannel : Channel left) (rightChannel : Channel right) :
    Channel (fun index => left index + right index) where
  errorScale := 2 * (leftChannel.errorScale + rightChannel.errorScale)
  errorScale_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg leftChannel.errorScale_nonneg
        rightChannel.errorScale_nonneg)
  later_close := by
    intro earlier later order
    have identity :
        (left later + right later) - (left earlier + right earlier) =
          (left later - left earlier) + (right later - right earlier) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im,
          Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im] <;> ring1
    rw [identity]
    calc
      Data.Gaussian.Norm.Basic.normSq ((left later - left earlier) +
          (right later - right earlier)) ≤
          2 * (Data.Gaussian.Norm.Basic.normSq (left later - left earlier) +
            Data.Gaussian.Norm.Basic.normSq (right later - right earlier)) :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 *
          (Geometric.Basic.quarterRadius
              leftChannel.errorScale earlier +
            Geometric.Basic.quarterRadius
              rightChannel.errorScale earlier) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add (leftChannel.later_close order)
            (rightChannel.later_close order)) (by decide)
      _ = Geometric.Basic.quarterRadius
          (2 * (leftChannel.errorScale + rightChannel.errorScale)) earlier := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
  centerBound := 2 * (leftChannel.centerBound + rightChannel.centerBound)
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg leftChannel.centerBound_nonneg
        rightChannel.centerBound_nonneg)
  bounded := by
    intro index
    calc
      Data.Gaussian.Norm.Basic.normSq (left index + right index) ≤
          2 * (Data.Gaussian.Norm.Basic.normSq (left index) + Data.Gaussian.Norm.Basic.normSq (right
            index)) :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 * (leftChannel.centerBound + rightChannel.centerBound) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add (leftChannel.bounded index)
            (rightChannel.bounded index)) (by decide)

/-- Certify pointwise negation while retaining the original movement scale and centre bound. -/
def neg {source : Nat →
  Canonical} (channel : Channel source) :
    Channel (fun index => -source index) where
  errorScale := channel.errorScale
  errorScale_nonneg := channel.errorScale_nonneg
  later_close := by
    intro earlier later order
    have identity : -source later - -source earlier =
        -(source later - source earlier) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im,
          Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im] <;> ring1
    rw [identity, Data.Gaussian.Norm.Basic.normSq_neg]
    exact channel.later_close order
  centerBound := channel.centerBound
  centerBound_nonneg := channel.centerBound_nonneg
  bounded := by
    intro index
    rw [Data.Gaussian.Norm.Basic.normSq_neg]
    exact channel.bounded index

/-- Certify the pointwise difference using addition and negation of the original channels. -/
def sub {left right : Nat →
  Canonical}
    (leftChannel : Channel left) (rightChannel : Channel right) :
    Channel (fun index => left index - right index) :=
  (add leftChannel rightChannel.neg).map (by
    intro index
    apply Data.Gaussian.Basic.ext <;>
      simp only [Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im,
        Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im, Purelib.Data.Gaussian.Basic.neg_re,
        Purelib.Data.Gaussian.Basic.neg_im] <;> ring1)

/-- Certify the pointwise product of two Gaussian rational channels.

The movement scale pays both source-error and opposite-centre products; the centre bound is the product of the original
bounds. -/
def mul {left right : Nat →
  Canonical}
    (leftChannel : Channel left) (rightChannel : Channel right) :
    Channel (fun index => left index * right index) where
  errorScale := 2 *
    (leftChannel.errorScale * rightChannel.centerBound +
      leftChannel.centerBound * rightChannel.errorScale)
  errorScale_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          leftChannel.errorScale_nonneg rightChannel.centerBound_nonneg)
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          leftChannel.centerBound_nonneg rightChannel.errorScale_nonneg))
  later_close := by
    intro earlier later order
    have identity :
        left later * right later - left earlier * right earlier =
          (left later - left earlier) * right later +
            left earlier * (right later - right earlier) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im,
          Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im, Purelib.Data.Gaussian.Basic.mul_re,
          Purelib.Data.Gaussian.Basic.mul_im] <;> ring1
    rw [identity]
    have first :
        Data.Gaussian.Norm.Basic.normSq ((left later - left earlier) * right later) ≤
          Geometric.Basic.quarterRadius
              leftChannel.errorScale earlier * rightChannel.centerBound := by
      rw [Data.Gaussian.Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_direct
        (leftChannel.later_close order) (rightChannel.bounded later)
        (Data.Gaussian.Norm.Basic.normSq_nonneg _) (Geometric.Basic.quarterRadius_nonneg
          leftChannel.errorScale_nonneg earlier)
    have second :
        Data.Gaussian.Norm.Basic.normSq (left earlier * (right later - right earlier)) ≤
          leftChannel.centerBound *
            Geometric.Basic.quarterRadius
              rightChannel.errorScale earlier := by
      rw [Data.Gaussian.Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_direct
        (leftChannel.bounded earlier) (rightChannel.later_close order)
        (Data.Gaussian.Norm.Basic.normSq_nonneg _) leftChannel.centerBound_nonneg
    calc
      Data.Gaussian.Norm.Basic.normSq ((left later - left earlier) * right later +
          left earlier * (right later - right earlier)) ≤
          2 * (Data.Gaussian.Norm.Basic.normSq ((left later - left earlier) * right later) +
            Data.Gaussian.Norm.Basic.normSq (left earlier * (right later - right earlier))) :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 *
          (Geometric.Basic.quarterRadius
              leftChannel.errorScale earlier * rightChannel.centerBound +
            leftChannel.centerBound *
              Geometric.Basic.quarterRadius
                rightChannel.errorScale earlier) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add first second) (by decide)
      _ = Geometric.Basic.quarterRadius
          (2 * (leftChannel.errorScale * rightChannel.centerBound +
            leftChannel.centerBound * rightChannel.errorScale)) earlier := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
  centerBound := leftChannel.centerBound * rightChannel.centerBound
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      leftChannel.centerBound_nonneg rightChannel.centerBound_nonneg
  bounded := by
    intro index
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct
      (leftChannel.bounded index) (rightChannel.bounded index)
      (Data.Gaussian.Norm.Basic.normSq_nonneg _) leftChannel.centerBound_nonneg

/-- Certify multiplication of a Gaussian rational channel by one displayed Gaussian rational scalar. -/
def scale (scalar :
  Canonical) {source : Nat → Canonical}
    (channel : Channel source) :
    Channel (fun index => scalar * source index) :=
  (exact scalar).mul channel
end Channel

end Purelib.Approximation.Gaussian.Sequence.Geometric.Channel

end
