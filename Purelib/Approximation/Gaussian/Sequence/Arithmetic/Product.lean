module
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Gaussian.Name.Basic (Named)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

namespace Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product

/-- The equal-index product movement scale is eight times the sum of the original samplers' squared-norm bounds. -/
def sampledProductErrorScale (left right :
  Named) : Fraction.Rational :=
  8 *
    (Sampling.approximation left).centerBound +
  8 *
    (Sampling.approximation right).centerBound

/-- The retained equal-index product movement scale is nonnegative. -/
theorem sampledProductErrorScale_nonneg (left right :
  Named) :
    0 ≤ sampledProductErrorScale left right := by
  unfold sampledProductErrorScale
  exact add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Sampling.approximation left).centerBound_nonneg)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Sampling.approximation right).centerBound_nonneg)

/-- A canonical product approximation built from equal-index finite samples of two arbitrary CCL names. Its geometric
radius is explicit because the canonical source samplers both use the same quarter-power schedule. -/
def sampledProductApproximation (left right :
  Named) : ApproximationData where
  sample index :=
    (Sampling.approximation left).sample index *
      (Sampling.approximation right).sample index
  radiusSq := Geometric.Basic.quarterRadius
    (sampledProductErrorScale left right)
  radiusSq_nonneg :=
    Geometric.Basic.quarterRadius_nonneg
      (sampledProductErrorScale_nonneg left right)
  later_close := by
    intro earlier later order
    let leftSource := Sampling.approximation left
    let rightSource := Sampling.approximation right
    have leftMovement := leftSource.later_close order
    have rightMovement := rightSource.later_close order
    have firstTerm :
        Data.Gaussian.Norm.Basic.normSq
            ((leftSource.sample later - leftSource.sample earlier) *
              rightSource.sample later) ≤
          Geometric.Basic.quarterRadius 4 earlier *
            rightSource.centerBound := by
      rw [Data.Gaussian.Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_direct leftMovement
        (rightSource.sample_bounded later) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        (Geometric.Basic.quarterRadius_nonneg (by decide) _)
    have secondTerm :
        Data.Gaussian.Norm.Basic.normSq
            (leftSource.sample earlier *
              (rightSource.sample later - rightSource.sample earlier)) ≤
          leftSource.centerBound *
            Geometric.Basic.quarterRadius 4 earlier := by
      rw [Data.Gaussian.Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_direct
        (leftSource.sample_bounded earlier) rightMovement (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        leftSource.centerBound_nonneg
    have identity :
        leftSource.sample later * rightSource.sample later -
            leftSource.sample earlier * rightSource.sample earlier =
          (leftSource.sample later - leftSource.sample earlier) *
              rightSource.sample later +
            leftSource.sample earlier *
              (rightSource.sample later - rightSource.sample earlier) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
          Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im, Purelib.Data.Gaussian.Basic.mul_re,
          Purelib.Data.Gaussian.Basic.mul_im] <;> ring1
    change Data.Gaussian.Norm.Basic.normSq
        (leftSource.sample later * rightSource.sample later -
          leftSource.sample earlier * rightSource.sample earlier) ≤
      Geometric.Basic.quarterRadius
        (sampledProductErrorScale left right) earlier
    rw [identity]
    calc
      Data.Gaussian.Norm.Basic.normSq
          ((leftSource.sample later - leftSource.sample earlier) *
              rightSource.sample later +
            leftSource.sample earlier *
              (rightSource.sample later - rightSource.sample earlier)) ≤
        2 *
          (Data.Gaussian.Norm.Basic.normSq
              ((leftSource.sample later - leftSource.sample earlier) *
                rightSource.sample later) +
            Data.Gaussian.Norm.Basic.normSq
              (leftSource.sample earlier *
                (rightSource.sample later - rightSource.sample earlier))) :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 *
          (Geometric.Basic.quarterRadius 4 earlier *
              rightSource.centerBound +
            leftSource.centerBound *
              Geometric.Basic.quarterRadius 4 earlier) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTerm secondTerm) (by decide)
      _ = Geometric.Basic.quarterRadius
          (sampledProductErrorScale left right) earlier := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        dsimp only [leftSource, rightSource]
        unfold sampledProductErrorScale
        ring1
  refineIndex current target _ :=
    Search.firstQuarterBelow
      (sampledProductErrorScale left right) current target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge
      (sampledProductErrorScale left right) current target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate
      (sampledProductErrorScale left right)
      (sampledProductErrorScale_nonneg left right)
  centerBound :=
    (Sampling.approximation left).centerBound *
      (Sampling.approximation right).centerBound
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Sampling.approximation left).centerBound_nonneg
      (Sampling.approximation right).centerBound_nonneg
  sample_bounded := by
    intro index
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct
      ((Sampling.approximation left).sample_bounded
        index)
      ((Sampling.approximation right).sample_bounded
        index)
      (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (Sampling.approximation left).centerBound_nonneg

/-- The product approximation multiplies the two original canonical samples at the same index. -/
@[simp] theorem sampledProductApproximation_sample
    (left right : Named) (index : Nat) :
    (sampledProductApproximation left right).sample index =
      (Sampling.approximation left).sample index *
      (Sampling.approximation right).sample index :=
  rfl

/-- The equal-index triple-product movement scale combines the first product's allowance with the final sampler's
squared-norm bound. -/
def sampledTripleErrorScale (left middle right :
  Named) : Fraction.Rational :=
  2 *
    (sampledProductErrorScale left middle *
        (Sampling.approximation right).centerBound +
      ((Sampling.approximation left).centerBound *
          (Sampling.approximation middle).centerBound) *
        4)

/-- The retained equal-index triple-product movement scale is nonnegative. -/
theorem sampledTripleErrorScale_nonneg (left middle
  right : Named) :
    0 ≤ sampledTripleErrorScale left middle right := by
  unfold sampledTripleErrorScale
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (sampledProductErrorScale_nonneg left middle)
        (Sampling.approximation right).centerBound_nonneg)
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          (Sampling.approximation left).centerBound_nonneg
          (Sampling.approximation middle).centerBound_nonneg)
        (by decide)))

/-- A canonical equal-index approximation to the product of three arbitrary CCL names. It is deliberately parenthesized
on the left; Gaussian associativity lets either actual multiplication tree use the same target. -/
def sampledTripleApproximation (left middle right :
  Named) : ApproximationData where
  sample index :=
    ((Sampling.approximation left).sample index *
      (Sampling.approximation middle).sample index) *
        (Sampling.approximation right).sample index
  radiusSq := Geometric.Basic.quarterRadius
    (sampledTripleErrorScale left middle right)
  radiusSq_nonneg :=
    Geometric.Basic.quarterRadius_nonneg
      (sampledTripleErrorScale_nonneg left middle right)
  later_close := by
    intro earlier later order
    let leftMiddle := sampledProductApproximation left middle
    let rightSource := Sampling.approximation right
    have leftMiddleMovement := leftMiddle.later_close order
    have rightMovement := rightSource.later_close order
    have firstTerm :
        Data.Gaussian.Norm.Basic.normSq
            ((leftMiddle.sample later - leftMiddle.sample earlier) *
              rightSource.sample later) ≤
          Geometric.Basic.quarterRadius
              (sampledProductErrorScale left middle) earlier *
            rightSource.centerBound := by
      rw [Data.Gaussian.Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_direct leftMiddleMovement
        (rightSource.sample_bounded later) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        (Geometric.Basic.quarterRadius_nonneg
          (sampledProductErrorScale_nonneg left middle) _)
    have secondTerm :
        Data.Gaussian.Norm.Basic.normSq
            (leftMiddle.sample earlier *
              (rightSource.sample later - rightSource.sample earlier)) ≤
          leftMiddle.centerBound *
            Geometric.Basic.quarterRadius 4 earlier := by
      rw [Data.Gaussian.Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_direct
        (leftMiddle.sample_bounded earlier) rightMovement (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        leftMiddle.centerBound_nonneg
    have identity :
        leftMiddle.sample later * rightSource.sample later -
            leftMiddle.sample earlier * rightSource.sample earlier =
          (leftMiddle.sample later - leftMiddle.sample earlier) *
              rightSource.sample later +
            leftMiddle.sample earlier *
              (rightSource.sample later - rightSource.sample earlier) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
          Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im, Purelib.Data.Gaussian.Basic.mul_re,
          Purelib.Data.Gaussian.Basic.mul_im] <;> ring1
    change Data.Gaussian.Norm.Basic.normSq
        (leftMiddle.sample later * rightSource.sample later -
          leftMiddle.sample earlier * rightSource.sample earlier) ≤
      Geometric.Basic.quarterRadius
        (sampledTripleErrorScale left middle right) earlier
    rw [identity]
    calc
      Data.Gaussian.Norm.Basic.normSq
          ((leftMiddle.sample later - leftMiddle.sample earlier) *
              rightSource.sample later +
            leftMiddle.sample earlier *
              (rightSource.sample later - rightSource.sample earlier)) ≤
        2 *
          (Data.Gaussian.Norm.Basic.normSq
              ((leftMiddle.sample later - leftMiddle.sample earlier) *
                rightSource.sample later) +
            Data.Gaussian.Norm.Basic.normSq
              (leftMiddle.sample earlier *
                (rightSource.sample later - rightSource.sample earlier))) :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 *
          (Geometric.Basic.quarterRadius
                (sampledProductErrorScale left middle) earlier *
              rightSource.centerBound +
            leftMiddle.centerBound *
              Geometric.Basic.quarterRadius 4 earlier) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTerm secondTerm) (by decide)
      _ = Geometric.Basic.quarterRadius
          (sampledTripleErrorScale left middle right) earlier
            := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        dsimp only [leftMiddle, rightSource,
          sampledProductApproximation]
        unfold sampledTripleErrorScale
        ring1
  refineIndex current target _ :=
    Search.firstQuarterBelow
      (sampledTripleErrorScale left middle right) current
        target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge
      (sampledTripleErrorScale left middle right) current
        target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate
      (sampledTripleErrorScale left middle right)
      (sampledTripleErrorScale_nonneg left middle right)
  centerBound :=
    ((Sampling.approximation left).centerBound *
      (Sampling.approximation middle).centerBound) *
        (Sampling.approximation right).centerBound
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Sampling.approximation left).centerBound_nonneg
        (Sampling.approximation middle).centerBound_nonneg)
      (Sampling.approximation right).centerBound_nonneg
  sample_bounded := by
    intro index
    rw [Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct
      (Fraction.Order.Arithmetic.mul_le_mul_direct
        ((Sampling.approximation left).sample_bounded
          index)
        ((Sampling.approximation middle).sample_bounded
          index)
        (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        (Sampling.approximation left).centerBound_nonneg)
      ((Sampling.approximation right).sample_bounded
        index)
      (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Sampling.approximation left).centerBound_nonneg
        (Sampling.approximation middle).centerBound_nonneg)

/-- The triple-product approximation multiplies the three original canonical samples with left association at the same
index. -/
@[simp] theorem sampledTripleApproximation_sample
    (left middle right : Named) (index : Nat) :
    (sampledTripleApproximation left middle right).sample index =
      ((Sampling.approximation left).sample index *
        (Sampling.approximation middle).sample index) *
          (Sampling.approximation right).sample index :=
  rfl
end Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product

end
