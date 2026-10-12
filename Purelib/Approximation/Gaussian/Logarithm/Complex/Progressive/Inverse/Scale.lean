module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Reconstruction
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Constant
public import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

namespace Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Scale

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse
open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Name
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat

public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

/-- Multiply the reconstructed-chart movement scale by the squared norm of the displayed Gaussian factor. -/
@[expose] def scaledDynamicLocalExpLogChartErrorScale (factor : Data.Gaussian.Basic.Canonical) : Fraction.Rational :=
  Reconstruction.dynamicLocalExpLogChartApproximationScale * Data.Gaussian.Norm.Basic.normSq factor

/-- The scaled reconstructed-chart movement coefficient is nonnegative. -/
theorem scaledDynamicLocalExpLogChartErrorScale_nonneg (factor : Data.Gaussian.Basic.Canonical) :
    0 ≤ Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Scale.scaledDynamicLocalExpLogChartErrorScale
      factor :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    Reconstruction.dynamicLocalExpLogChartApproximationScale_nonneg (Data.Gaussian.Norm.Basic.normSq_nonneg factor)

/-- Pointwise multiplication of the reconstructed local exp-log chart by one displayed rational branch factor. -/
@[expose] def scaledDynamicLocalExpLogChartApproximation (input : Gaussian.Name.Basic.Named)
    (disk : Domain.Disk input)
    (factor : Data.Gaussian.Basic.Canonical) : ApproximationData where
  sample depth := Reconstruction.dynamicLocalExpLogChartSample input depth * factor
  radiusSq := Geometric.Basic.quarterRadius
    (Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Scale.scaledDynamicLocalExpLogChartErrorScale
      factor)
  radiusSq_nonneg :=
    Geometric.Basic.quarterRadius_nonneg
      (Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Scale.scaledDynamicLocalExpLogChartErrorScale_nonneg
        factor)
  later_close := by
    intro earlier later order
    have movement :=
      (Reconstruction.dynamicLocalExpLogChartApproximation input disk).later_close order
    have movementScaled :
        Data.Gaussian.Norm.Basic.normSq
            (Reconstruction.dynamicLocalExpLogChartSample input later -
              Reconstruction.dynamicLocalExpLogChartSample input earlier) ≤
          Reconstruction.dynamicLocalExpLogChartApproximationScale *
            (1 / 4 : Fraction.Rational) ^ earlier := by
      change Data.Gaussian.Norm.Basic.normSq
          (Reconstruction.dynamicLocalExpLogChartSample input later -
            Reconstruction.dynamicLocalExpLogChartSample input earlier) ≤
        Geometric.Basic.quarterRadius
          Reconstruction.dynamicLocalExpLogChartApproximationScale earlier at movement
      simpa only [Geometric.Basic.quarterRadius_eq_mul_pow]
        using movement
    have identity :
        Reconstruction.dynamicLocalExpLogChartSample input later * factor -
            Reconstruction.dynamicLocalExpLogChartSample input earlier * factor =
          (Reconstruction.dynamicLocalExpLogChartSample input later -
            Reconstruction.dynamicLocalExpLogChartSample input earlier) * factor := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
          Purelib.Data.Gaussian.Basic.mul_re, Purelib.Data.Gaussian.Basic.mul_im] <;> ring1
    change Data.Gaussian.Norm.Basic.normSq
        (Reconstruction.dynamicLocalExpLogChartSample input later * factor -
          Reconstruction.dynamicLocalExpLogChartSample input earlier * factor) ≤
      Geometric.Basic.quarterRadius

          (scaledDynamicLocalExpLogChartErrorScale
          factor) earlier
    rw [identity, Data.Gaussian.Norm.Basic.normSq_mul,
      Geometric.Basic.quarterRadius_eq_mul_pow]
    unfold
      Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Scale.scaledDynamicLocalExpLogChartErrorScale
    calc
      Data.Gaussian.Norm.Basic.normSq
          (Reconstruction.dynamicLocalExpLogChartSample input later -
            Reconstruction.dynamicLocalExpLogChartSample input earlier) * Data.Gaussian.Norm.Basic.normSq
              factor ≤
        (Reconstruction.dynamicLocalExpLogChartApproximationScale *
            (1 / 4 : Fraction.Rational) ^ earlier) * Data.Gaussian.Norm.Basic.normSq factor :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            movementScaled (Data.Gaussian.Norm.Basic.normSq_nonneg factor)
      _ = Reconstruction.dynamicLocalExpLogChartApproximationScale * Data.Gaussian.Norm.Basic.normSq factor *
          (1 / 4 : Fraction.Rational) ^ earlier := by ring1
  refineIndex current target _ :=
    Search.firstQuarterBelow

        (scaledDynamicLocalExpLogChartErrorScale
        factor) current target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge

        (scaledDynamicLocalExpLogChartErrorScale
        factor) current target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate

        (scaledDynamicLocalExpLogChartErrorScale
        factor)
      (Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Scale.scaledDynamicLocalExpLogChartErrorScale_nonneg
        factor)
  centerBound := Reconstruction.dynamicLocalExpLogChartCenterBound * Data.Gaussian.Norm.Basic.normSq factor
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      Reconstruction.dynamicLocalExpLogChartCenterBound_nonneg (Data.Gaussian.Norm.Basic.normSq_nonneg factor)
  sample_bounded := by
    intro depth
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      ((Reconstruction.dynamicLocalExpLogChartApproximation input disk).sample_bounded depth)
      (Data.Gaussian.Norm.Basic.normSq_nonneg factor)

/-- Sampling the scaled reconstruction multiplies the original chart sample by the constant factor at the same index. -/
@[simp] theorem scaledDynamicLocalExpLogChartApproximation_sample
    (input : Gaussian.Name.Basic.Named) (disk : Domain.Disk input)
    (factor : Data.Gaussian.Basic.Canonical) (depth : Nat) :
    (Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Scale.scaledDynamicLocalExpLogChartApproximation input
      disk factor).sample
        depth =
      (Reconstruction.dynamicLocalExpLogChartApproximation input disk).sample depth *
        (Constant.constantApproximation factor).sample
          depth :=
  rfl

/-- Rational branch scaling preserves the finite Möbius reconstruction congruence, with a direct zero-factor branch and
an explicit norm budget otherwise. -/
@[expose] def scaledDynamicLocalExpLogChartApproximation_respects {left right : Gaussian.Name.Basic.Named}
    (leftDisk : Domain.Disk left)
    (rightDisk : Domain.Disk right)
    (factor : Data.Gaussian.Basic.Canonical) (equivalent : Gaussian.Equivalence.NamedEquivalent left right) :
    Gaussian.Equivalence.Equivalent
      (Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Scale.scaledDynamicLocalExpLogChartApproximation
        left leftDisk factor)
      (Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Scale.scaledDynamicLocalExpLogChartApproximation
        right rightDisk factor) := by
  by_cases factorZero : factor = 0
  · subst factor
    exact Equivalence.approximationEquivalentOfSamplesEq _ _ (by
      intro index
      change Reconstruction.dynamicLocalExpLogChartSample left index * 0 =
        Reconstruction.dynamicLocalExpLogChartSample right index * 0
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.mul_re, Purelib.Data.Gaussian.Basic.mul_im,
          Purelib.Data.Gaussian.Basic.zero_re, Purelib.Data.Gaussian.Basic.zero_im] <;> ring1)
  · let sourceEquivalent :=
      Reconstruction.dynamicLocalExpLogChartApproximation_respects
        leftDisk rightDisk equivalent
    exact
      { compare := by
          intro leftStart rightStart target positive
          let factorNorm := Data.Gaussian.Norm.Basic.normSq factor
          have factorPositive : 0 < factorNorm := Data.Gaussian.Norm.Basic.normSq_pos factorZero
          let sourceTarget := target / factorNorm
          have sourcePositive : 0 < sourceTarget :=
            Fraction.Order.Field.div_pos_direct positive factorPositive
          let comparison := sourceEquivalent.compare leftStart rightStart
            sourceTarget sourcePositive
          exact
            { leftIndex := comparison.leftIndex
              rightIndex := comparison.rightIndex
              left_ge := comparison.left_ge
              right_ge := comparison.right_ge
              close := by
                intro leftLater rightLater leftOrder rightOrder
                have sourceClose := comparison.close leftOrder rightOrder
                have identity :
                    Reconstruction.dynamicLocalExpLogChartSample left leftLater * factor -
                        Reconstruction.dynamicLocalExpLogChartSample right rightLater * factor =
                      (Reconstruction.dynamicLocalExpLogChartSample left leftLater -
                        Reconstruction.dynamicLocalExpLogChartSample right rightLater) *
                          factor := by
                  apply Data.Gaussian.Basic.ext <;>
                    simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
                      Purelib.Data.Gaussian.Basic.mul_re, Purelib.Data.Gaussian.Basic.mul_im] <;> ring1
                change Data.Gaussian.Norm.Basic.normSq
                    (Reconstruction.dynamicLocalExpLogChartSample left leftLater * factor -
                      Reconstruction.dynamicLocalExpLogChartSample right rightLater * factor) <
                    target
                rw [identity, Data.Gaussian.Norm.Basic.normSq_mul]
                calc
                  Data.Gaussian.Norm.Basic.normSq
                        (Reconstruction.dynamicLocalExpLogChartSample left leftLater -
                          Reconstruction.dynamicLocalExpLogChartSample right rightLater) *
                      factorNorm < sourceTarget * factorNorm :=
                    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
                      sourceClose factorPositive
                  _ = target :=
                    Fraction.Field.div_mul_cancel_of_ne
                      target factorNorm factorPositive.ne' } }

/-- Productive names of equally scaled chart reconstructions preserve operational equivalence of the original reduced
inputs. -/
@[expose] def scaledDynamicLocalExpLogChartNamed_respects {left right : Gaussian.Name.Basic.Named}
    (leftDisk : Domain.Disk left)
    (rightDisk : Domain.Disk right)
    (factor : Data.Gaussian.Basic.Canonical) (equivalent : Gaussian.Equivalence.NamedEquivalent left right) :
    Gaussian.Equivalence.NamedEquivalent
      (Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Scale.scaledDynamicLocalExpLogChartApproximation
        left leftDisk factor).toNamed
      (Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Scale.scaledDynamicLocalExpLogChartApproximation
        right rightDisk factor).toNamed :=
  Equivalence.approximationEquivalent_toNamed

      (scaledDynamicLocalExpLogChartApproximation_respects
      leftDisk rightDisk factor equivalent)

end

end Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Scale
