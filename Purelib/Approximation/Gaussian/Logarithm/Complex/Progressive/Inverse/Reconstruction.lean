module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Diagonal
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Sampling
import Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error
public import Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Sequence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Geometric.Quarter
public import Purelib.Geometry.Projective.Homography.Cayley.Bounds

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction.Order

section
public section

/-! Approximation Gaussian Logarithm Complex Progressive Inverse Reconstruction and its finite structural certificates.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Reconstruction

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse
open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local
open Purelib.Approximation.Gaussian.Logarithm.Local.Inverse
open Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial
open Purelib.Approximation.Gaussian.Name.Sampling
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Name
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat
open Purelib.Data.Rat.Geometric

/-- Apply rational Cayley reconstruction to the displayed finite reduced-input sample. -/
@[expose] public def dynamicLocalExpLogChartSample (input : Name.Basic.Named) (depth : Nat) :
  Data.Gaussian.Basic.Canonical :=
  let reduced :=
    ComplexLog.inputSample input depth
  (1 + reduced) / (1 - reduced)

/-- The diagonal exponential–logarithm sample approximates reconstruction of the same finite input reading with the
retained geometric squared-error bound. -/
theorem dynamicLocalExpLog_chart_error (input : Name.Basic.Named)
    (disk : Domain.Disk input)
    (depth : Nat) :
    Basic.normSq
        ((Diagonal.dynamicLocalExpLogApproximation input disk).sample depth -
          dynamicLocalExpLogChartSample
            input depth) ≤
      Error.expLogErrorScale *
        (1 / 4 : Fraction.Rational) ^ depth := by
  exact Error.localExpLogSample_chart_error
    (Sampling.inputSample_bound disk depth)
    depth

/-- The geometric movement scale combining reconstruction errors and diagonal exponential–logarithm movement. -/
@[expose] public def dynamicLocalExpLogChartApproximationScale : Fraction.Rational :=
  2 * (3 * Error.expLogErrorScale +
    2 * Diagonal.dynamicLocalExpLogErrorScale)

/-- The reconstructed-chart approximation error scale is nonnegative. -/
theorem dynamicLocalExpLogChartApproximationScale_nonneg :
    0 ≤
      dynamicLocalExpLogChartApproximationScale
      := by
  unfold dynamicLocalExpLogChartApproximationScale
  exact Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg
      (Arithmetic.mul_nonneg_direct (by decide)
        Error.expLogErrorScale_nonnegative)
      (Arithmetic.mul_nonneg_direct (by decide)
        Diagonal.dynamicLocalExpLogErrorScale_nonneg))

/-- The uniform rational squared-norm bound combining reconstruction error with the diagonal sample bound. -/
@[expose] public def dynamicLocalExpLogChartCenterBound : Fraction.Rational :=
  2 * (Error.expLogErrorScale + 5 * 10)

/-- The reconstructed-chart center bound is nonnegative. -/
theorem dynamicLocalExpLogChartCenterBound_nonneg :
    0 ≤
      dynamicLocalExpLogChartCenterBound
      := by
  unfold dynamicLocalExpLogChartCenterBound
  exact Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg
      Error.expLogErrorScale_nonnegative
      (by decide))

/-- The exact rational Möbius reconstruction of each finite reduced reading.

Its Cauchy certificate is obtained solely from the explicit finite exp-log error and the already proved dynamic-program
movement bound. -/
@[expose] public def dynamicLocalExpLogChartApproximation (input : Name.Basic.Named)
    (disk : Domain.Disk input) :
    ApproximationData where
  sample := dynamicLocalExpLogChartSample
    input
  radiusSq := Basic.quarterRadius

      dynamicLocalExpLogChartApproximationScale
  radiusSq_nonneg :=
    Basic.quarterRadius_nonneg

        dynamicLocalExpLogChartApproximationScale_nonneg
  later_close := by
    intro earlier later order
    let dynamic := Diagonal.dynamicLocalExpLogApproximation input disk
    have laterError :=
      dynamicLocalExpLog_chart_error input
      disk later
    have earlierError :=
      dynamicLocalExpLog_chart_error input
      disk earlier
    have laterScaled :
        Error.expLogErrorScale *
            (1 / 4 : Fraction.Rational) ^ later ≤
          Error.expLogErrorScale *
            (1 / 4 : Fraction.Rational) ^ earlier :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Quarter.quarterPower_antitone order)
        Error.expLogErrorScale_nonnegative
    have laterErrorScaled := laterError.trans laterScaled
    have laterErrorReverse :
        Basic.normSq
            (dynamicLocalExpLogChartSample
              input later -
              dynamic.sample later) ≤
          Error.expLogErrorScale *
            (1 / 4 : Fraction.Rational) ^ earlier := by
      have identity :
          dynamicLocalExpLogChartSample
            input later -
              dynamic.sample later =
            -(dynamic.sample later -
              dynamicLocalExpLogChartSample
                input later) := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
            Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;> ring1
      rw [identity, Basic.normSq_neg]
      exact laterErrorScaled
    have dynamicMovement := dynamic.later_close order
    have dynamicMovementScaled :
        Basic.normSq (dynamic.sample later - dynamic.sample earlier) ≤
          Diagonal.dynamicLocalExpLogErrorScale *
            (1 / 4 : Fraction.Rational) ^ earlier := by
      change Basic.normSq (dynamic.sample later - dynamic.sample earlier) ≤
        Basic.quarterRadius
          Diagonal.dynamicLocalExpLogErrorScale earlier at dynamicMovement
      simpa only [Basic.quarterRadius_eq_mul_pow]
        using dynamicMovement
    change Basic.normSq
        (dynamicLocalExpLogChartSample input
          later -
          dynamicLocalExpLogChartSample
            input earlier) ≤
      Basic.quarterRadius

          dynamicLocalExpLogChartApproximationScale
          earlier
    calc
      Basic.normSq
          (dynamicLocalExpLogChartSample
            input later -
            dynamicLocalExpLogChartSample
              input earlier) ≤
        2 *
          (Basic.normSq
              (dynamicLocalExpLogChartSample
                input later -
                dynamic.sample later) +
            Basic.normSq
              (dynamic.sample later -

                  dynamicLocalExpLogChartSample
                  input earlier)) :=
        Bounds.normSq_sub_le_via _ _ _
      _ ≤ 2 *
          (Error.expLogErrorScale *
              (1 / 4 : Fraction.Rational) ^ earlier +
            2 *
              (Diagonal.dynamicLocalExpLogErrorScale *
                  (1 / 4 : Fraction.Rational) ^ earlier +
                Error.expLogErrorScale *
                  (1 / 4 : Fraction.Rational) ^ earlier)) := by
        apply Arithmetic.mul_le_mul_of_nonneg_left_direct _
          (by decide)
        apply add_le_add laterErrorReverse
        calc
          Basic.normSq
              (dynamic.sample later -

                  dynamicLocalExpLogChartSample
                  input earlier) ≤
            2 *
              (Basic.normSq (dynamic.sample later - dynamic.sample earlier) +
                Basic.normSq
                  (dynamic.sample earlier -

                      dynamicLocalExpLogChartSample
                      input earlier)) :=
              Bounds.normSq_sub_le_via _ _ _
          _ ≤ 2 *
              (Diagonal.dynamicLocalExpLogErrorScale *
                  (1 / 4 : Fraction.Rational) ^ earlier +
                Error.expLogErrorScale *
                  (1 / 4 : Fraction.Rational) ^ earlier) :=
            Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add dynamicMovementScaled earlierError) (by decide)
      _ = Basic.quarterRadius

            dynamicLocalExpLogChartApproximationScale
            earlier := by
        rw [Basic.quarterRadius_eq_mul_pow]
        unfold
          dynamicLocalExpLogChartApproximationScale
        ring1
  refineIndex current target _ :=
    Search.firstQuarterBelow

        dynamicLocalExpLogChartApproximationScale
        current target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge

        dynamicLocalExpLogChartApproximationScale
        current target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate

        dynamicLocalExpLogChartApproximationScale

        dynamicLocalExpLogChartApproximationScale_nonneg
  centerBound :=
    dynamicLocalExpLogChartCenterBound
  centerBound_nonneg :=
    dynamicLocalExpLogChartCenterBound_nonneg
  sample_bounded := by
    intro depth
    let dynamic := Diagonal.dynamicLocalExpLogApproximation input disk
    have error :=
      dynamicLocalExpLog_chart_error input
      disk depth
    have errorLe :
        Error.expLogErrorScale *
            (1 / 4 : Fraction.Rational) ^ depth ≤
          Error.expLogErrorScale := by
      simpa only [pow_zero, Fraction.Field.mul_one_direct]
        using Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Quarter.quarterPower_antitone
            (show 0 ≤ depth by omega))
          Error.expLogErrorScale_nonnegative
    have reverseError :
        Basic.normSq
            (dynamicLocalExpLogChartSample
              input depth -
              dynamic.sample depth) ≤
          Error.expLogErrorScale := by
      have identity :
        dynamicLocalExpLogChartSample input
        depth -
            dynamic.sample depth =
          -(dynamic.sample depth -
            dynamicLocalExpLogChartSample
              input depth) := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
            Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;> ring1
      rw [identity, Basic.normSq_neg]
      exact error.trans errorLe
    have dynamicBound : Basic.normSq (dynamic.sample depth) ≤ 5 * 10 :=
      Sequence.localExpLogSample_bounded
        (Sampling.inputSample_bound disk depth)
        depth
    have identity :
      dynamicLocalExpLogChartSample input
      depth =
        (dynamicLocalExpLogChartSample input
          depth - dynamic.sample depth) +
          dynamic.sample depth := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
          Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im] <;> ring1
    rw [identity]
    exact (Bounds.normSq_add_le_two _ _).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add reverseError dynamicBound) (by decide))

/-- Exact finite Möbius reconstruction respects operational equality of two progressive reduced inputs. -/
@[expose] public def dynamicLocalExpLogChartApproximation_respects {left right : Name.Basic.Named}
    (leftDisk : Domain.Disk left)
    (rightDisk : Domain.Disk right)
    (equivalent : NamedEquivalent left right) :
    Equivalent
      (dynamicLocalExpLogChartApproximation
        left leftDisk)
      (dynamicLocalExpLogChartApproximation
        right rightDisk) where
  compare := by
    intro leftStart rightStart target positive
    let coefficient : Fraction.Rational := (9 * 9) / 4
    have coefficientPositive : 0 < coefficient := by
      dsimp only [coefficient]
      decide
    let inputTarget := target / coefficient
    have inputPositive : 0 < inputTarget :=
      Field.div_pos_direct positive coefficientPositive
    let comparison := equivalent.compare leftStart rightStart
      inputTarget inputPositive
    exact
      { leftIndex := comparison.leftIndex
        rightIndex := comparison.rightIndex
        left_ge := comparison.left_ge
        right_ge := comparison.right_ge
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have inputClose := comparison.close leftOrder rightOrder
          have chartClose :=
            Geometry.Projective.Homography.Cayley.Bounds.localChart_input_close
              (Sampling.inputSample_bound
                leftDisk leftLater)
              (Sampling.inputSample_bound
                rightDisk rightLater)
          calc
            Basic.normSq

                  ((dynamicLocalExpLogChartApproximation
                  left leftDisk).sample
                    leftLater -

                    (dynamicLocalExpLogChartApproximation
                    right rightDisk).sample
                    rightLater) ≤
              coefficient * Basic.normSq
                (ComplexLog.inputSample
                    left leftLater -
                  ComplexLog.inputSample
                    right rightLater) := chartClose
            _ < coefficient * inputTarget :=
              Arithmetic.mul_lt_mul_of_pos_left_direct
                coefficientPositive inputClose
            _ = target := by
              dsimp only [inputTarget]
              rw [Fraction.Field.mul_comm]
              exact Fraction.Field.div_mul_cancel_of_ne
                target coefficient coefficientPositive.ne' }

/-- Names generated by reconstructed-chart approximations preserve operational equivalence of the original certified
reduced inputs. -/
@[expose] public def dynamicLocalExpLogChartNamed_respects {left right : Name.Basic.Named}
    (leftDisk : Domain.Disk left)
    (rightDisk : Domain.Disk right)
    (equivalent : NamedEquivalent left right) :
    NamedEquivalent
      (dynamicLocalExpLogChartApproximation
        left leftDisk).toNamed
      (dynamicLocalExpLogChartApproximation
        right rightDisk).toNamed :=
  Equivalence.approximationEquivalent_toNamed

      (dynamicLocalExpLogChartApproximation_respects
      leftDisk rightDisk equivalent)
end Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Reconstruction

end
