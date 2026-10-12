module
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

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

namespace Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum

/-! ## Canonical two-input sums and products -/

/-- Equal-index addition of two canonical CCL samplers. -/
def sampledSumApproximation (left right :
  Gaussian.Name.Basic.Named) : ApproximationData where
  sample index :=
    (Sampling.approximation left).sample index +
      (Sampling.approximation right).sample index
  radiusSq := Geometric.Basic.quarterRadius 16
  radiusSq_nonneg :=
    Geometric.Basic.quarterRadius_nonneg (by decide)
  later_close := by
    intro earlier later order
    let leftSource := Sampling.approximation left
    let rightSource := Sampling.approximation right
    have leftMovement := leftSource.later_close order
    have rightMovement := rightSource.later_close order
    have identity :
        leftSource.sample later + rightSource.sample later -
            (leftSource.sample earlier + rightSource.sample earlier) =
          (leftSource.sample later - leftSource.sample earlier) +
            (rightSource.sample later - rightSource.sample earlier) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
          Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im] <;> ring1
    change Data.Gaussian.Norm.Basic.normSq
        (leftSource.sample later + rightSource.sample later -
          (leftSource.sample earlier + rightSource.sample earlier)) ≤
      Geometric.Basic.quarterRadius 16 earlier
    rw [identity]
    calc
      Data.Gaussian.Norm.Basic.normSq
          ((leftSource.sample later - leftSource.sample earlier) +
            (rightSource.sample later - rightSource.sample earlier)) ≤
        2 *
          (Data.Gaussian.Norm.Basic.normSq (leftSource.sample later - leftSource.sample earlier) +
            Data.Gaussian.Norm.Basic.normSq
              (rightSource.sample later - rightSource.sample earlier)) :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 *
          (Geometric.Basic.quarterRadius 4 earlier +
            Geometric.Basic.quarterRadius 4 earlier) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add leftMovement rightMovement) (by decide)
      _ = Geometric.Basic.quarterRadius 16 earlier := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
  refineIndex current target _ :=
    Search.firstQuarterBelow 16 current target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge 16 current target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate 16 (by decide)
  centerBound :=
    2 *
      ((Sampling.approximation left).centerBound +
        (Sampling.approximation right).centerBound)
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Sampling.approximation left).centerBound_nonneg
        (Sampling.approximation right).centerBound_nonneg)
  sample_bounded := by
    intro index
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add
          ((Sampling.approximation left).sample_bounded
            index)
          ((Sampling.approximation right).sample_bounded
            index))
        (by decide))

/-- The sum approximation adds the two original canonical samples at the same index. -/
@[simp] theorem sampledSumApproximation_sample
    (left right : Gaussian.Name.Basic.Named) (index : Nat) :
    (sampledSumApproximation left right).sample index =
      (Sampling.approximation left).sample index +
        (Sampling.approximation right).sample index :=
  rfl
end Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum

end
