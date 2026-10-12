module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Sample
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Sampling
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
public import Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
public import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Geometric.Quarter

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local

open Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial

open Purelib.Approximation.Gaussian.Name.Sampling

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Rat

open Purelib.Data.Rat.Geometric

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

namespace Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Diagonal

/-- The geometric squared-error scale combining exponential truncation with the dynamic local logarithm's input error.
-/
def dynamicLocalExpLogErrorScale :
  Fraction.Rational :=
  2 * (10 + 16 * Sample.errorScale)

/-- The diagonal exponential–logarithm error scale is nonnegative. -/
theorem
  dynamicLocalExpLogErrorScale_nonneg
  :
    0 ≤ Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (by decide)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        Sample.errorScale_nonneg))

/-- Diagonal finite program for exponentiating a progressive local complex logarithm: logarithm depth `n`, exponential
depth `2n+1`. -/
def dynamicLocalExpLogApproximation
  (input : Gaussian.Name.Basic.Named)
    (disk : Domain.Disk input) :
    ApproximationData where
  sample depth := Exponential.Horner.Sample.sample
    (Name.domainSample input disk depth)
    (2 * depth + 1)
  radiusSq := Geometric.Basic.quarterRadius
    Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale
  radiusSq_nonneg :=
    Geometric.Basic.quarterRadius_nonneg
      Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale_nonneg
  later_close := by
    intro earlier later order
    let earlierInput :=
      Name.domainSample input disk earlier
    let laterInput :=
      Name.domainSample input disk later
    have earlierUnit : Data.Gaussian.Norm.Basic.normSq earlierInput ≤ 1 :=
      Logarithm.Local.Horner.Sample.sample_bounded_one
        (Sampling.inputSample_bound disk earlier)
        earlier
    have laterUnit : Data.Gaussian.Norm.Basic.normSq laterInput ≤ 1 :=
      Logarithm.Local.Horner.Sample.sample_bounded_one
        (Sampling.inputSample_bound disk later)
        later
    have depthOrder : 2 * earlier + 1 ≤ 2 * later + 1 := by omega
    have truncationRaw := Exponential.Horner.Sample.sample_later_close
      laterInput laterUnit depthOrder
    have truncation :
        Data.Gaussian.Norm.Basic.normSq
            (Exponential.Horner.Sample.sample laterInput (2 * later + 1) -
              Exponential.Horner.Sample.sample laterInput
                (2 * earlier + 1)) ≤
          10 * (1 / 4 : Fraction.Rational) ^ earlier := by
      exact truncationRaw.trans (by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow]
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Quarter.quarterPower_antitone
            (show earlier ≤ 2 * earlier + 1 by omega)) (by decide))
    have inputMovement :=
      Name.domainSample_later_close disk order
    have inputEffectRaw := Exponential.Horner.Sample.sample_input_close
      laterInput earlierInput laterUnit earlierUnit (2 * earlier + 1)
    have inputEffect :
        Data.Gaussian.Norm.Basic.normSq
            (Exponential.Horner.Sample.sample laterInput (2 * earlier + 1) -
              Exponential.Horner.Sample.sample earlierInput
                (2 * earlier + 1)) ≤
          16 * Sample.errorScale *
            (1 / 4 : Fraction.Rational) ^ earlier := by
      calc
        Data.Gaussian.Norm.Basic.normSq
            (Exponential.Horner.Sample.sample laterInput (2 * earlier + 1) -
              Exponential.Horner.Sample.sample earlierInput
                (2 * earlier + 1)) ≤
          16 * Data.Gaussian.Norm.Basic.normSq (laterInput - earlierInput) := inputEffectRaw
        _ ≤ 16 * Geometric.Basic.quarterRadius
            Sample.errorScale earlier :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            inputMovement (by decide)
        _ = 16 * Sample.errorScale *
            (1 / 4 : Fraction.Rational) ^ earlier := by
          rw [Geometric.Basic.quarterRadius_eq_mul_pow]
          ring1
    change Data.Gaussian.Norm.Basic.normSq
        (Exponential.Horner.Sample.sample laterInput (2 * later + 1) -
          Exponential.Horner.Sample.sample earlierInput (2 * earlier + 1)) ≤
      Geometric.Basic.quarterRadius
        Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale
          earlier
    calc
      Data.Gaussian.Norm.Basic.normSq
          (Exponential.Horner.Sample.sample laterInput (2 * later + 1) -
            Exponential.Horner.Sample.sample earlierInput
              (2 * earlier + 1)) ≤
        2 *
          (Data.Gaussian.Norm.Basic.normSq
              (Exponential.Horner.Sample.sample laterInput (2 * later + 1) -
                Exponential.Horner.Sample.sample laterInput
                  (2 * earlier + 1)) +
            Data.Gaussian.Norm.Basic.normSq
              (Exponential.Horner.Sample.sample laterInput
                  (2 * earlier + 1) -
                Exponential.Horner.Sample.sample earlierInput
                  (2 * earlier + 1))) :=
        Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
      _ ≤ 2 *
          (10 * (1 / 4 : Fraction.Rational) ^ earlier +
            (16 * Sample.errorScale) *
              (1 / 4 : Fraction.Rational) ^ earlier) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add truncation inputEffect) (by decide)
      _ = Geometric.Basic.quarterRadius
          Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale
            earlier := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow]
        unfold
          Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale
        ring1
  refineIndex current target _ :=
    Search.firstQuarterBelow
      Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale current
        target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge
      Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale current
        target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate
      Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale
        Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogErrorScale_nonneg
  centerBound := 10
  centerBound_nonneg := by decide
  sample_bounded := by
    intro depth
    exact Exponential.Horner.Sample.sample_bounded _
      (Logarithm.Local.Horner.Sample.sample_bounded_one
        (Sampling.inputSample_bound disk depth)
        depth) (2 * depth + 1)

/-- The diagonal approximation sample equals the synchronized nested Horner sample at the original finite input reading.
-/
@[simp] theorem
  dynamicLocalExpLogApproximation_sample
    (input : Gaussian.Name.Basic.Named) (disk : Domain.Disk input)
    (depth : Nat) :
    (Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Diagonal.dynamicLocalExpLogApproximation input
      disk).sample depth =
      Error.localExpLogSample
        (ComplexLog.inputSample input depth)
        depth :=
  rfl
end Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Diagonal

end
