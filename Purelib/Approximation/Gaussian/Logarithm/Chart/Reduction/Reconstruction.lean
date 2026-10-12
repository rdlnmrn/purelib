module
public import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Approximation.Gaussian.Equivalence.Coherence
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Branch
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison
import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Prepared
import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Synchronized
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Scale
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Homography.Cayley.Bounds
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Operational branch certificates for the complex logarithm

The geometric `Chart` data proves that its finite local recurrence is safe
and productive.  It intentionally permits any additive correction name.
This module records the additional semantic obligation needed to call that
correction a logarithm branch: exponentiating it must reproduce the inverse
of the chart's displayed scale, in finite operational equality.

Once the local inverse law and the exponential addition law are established,
this certificate is the missing branch datum in the calculation

`Exp(localLog(factor * input) + correction) = input`.

The exponentiation, equality, and inverse factor below are all CCL programs
or displayed Gaussian rationals.  No completed complex number or global
single-valued logarithm is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Reconstruction

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Logarithm
open Purelib.Approximation.Gaussian.Logarithm.Chart
open Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction
open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse
open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Sampling
open Purelib.CCL.Transcendental
open Purelib.Data.Rat

/-- Every possible value of the synchronized reduced chart name satisfies the retained local logarithm disk bound. -/
theorem synchronizedReducedDisk (input : Gaussian.Name.Basic.Named) (chart : Chart input)
    (certificate : Branch.BranchCertificate input chart) :
    Domain.Disk
      (Synchronized.synchronizedReducedNamed input chart certificate) where
  possible_normSq := by
    intro value possible
    rcases possible with ⟨later, _order, rfl⟩
    exact Synchronized.synchronizedReducedSample_disk input chart certificate later

/-- Exact finite reconstruction of every synchronized reduced sample. -/
theorem synchronizedReducedSample_reconstructs (input : Gaussian.Name.Basic.Named)
    (chart : Chart input) (certificate : Branch.BranchCertificate input chart)
    (index : Nat) :
    ((1 + Synchronized.synchronizedReducedSample input chart index) /
        (1 - Synchronized.synchronizedReducedSample input chart index)) *
          (1 / chart.factor) =
      ComplexLog.inputSample
        (Prepared.preparedChartInput input chart) index := by
  let value := ComplexLog.inputSample
    (Prepared.preparedChartInput input chart) index
  have possible :=
    ComplexLog.inputSample_possible_start
      (Prepared.preparedChartInput input chart) index
  have denominatorNonzero :=
    Prepared.preparedChartInput_denominator_ne_zero input chart certificate possible
  have reducedBound :=
    Synchronized.synchronizedReducedSample_disk input chart certificate index
  have chartIdentity := Geometry.Projective.Homography.Cayley.Bounds.scaledReduced_chart
    chart.factor value denominatorNonzero reducedBound
  change ((1 + Prepared.synchronizedReducedValue input chart value) /
      (1 - Prepared.synchronizedReducedValue input chart value)) *
        (1 / chart.factor) = value
  unfold Prepared.synchronizedReducedValue
  rw [chartIdentity, Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    chart.factor * value * (1 * chart.factor⁻¹) =
        value * (chart.factor * chart.factor⁻¹) := by
      rw [Data.Gaussian.Basic.one_mul,
        Data.Gaussian.Basic.mul_comm chart.factor value,
        Data.Gaussian.Basic.mul_assoc]
    _ = value * 1 := by
      rw [show chart.factor * chart.factor⁻¹ = 1 by
        simpa only [Data.Gaussian.Field.inv_eq] using
          Data.Gaussian.Field.mul_inv chart.factor
            certificate.factor_ne_zero]
    _ = value := Data.Gaussian.Basic.mul_one value

/-- Sampling the synchronized reduced name returns its original reduced sample at the computed emitted source index. -/
theorem synchronizedReducedNamed_inputSample (input : Gaussian.Name.Basic.Named)
    (chart : Chart input) (certificate : Branch.BranchCertificate input chart)
    (index : Nat) :
    ComplexLog.inputSample
        (Synchronized.synchronizedReducedNamed input chart certificate) index =
      Synchronized.synchronizedReducedSample input chart
        (Comparison.synchronizedReducedSourceIndex input chart certificate index) := by
  change
    (Sampling.approximation
      (Synchronized.synchronizedReducedApproximation input chart certificate).toNamed).sample
        index =
      (Synchronized.synchronizedReducedApproximation input chart certificate).sample
        (Sampling.emittedSampleIndex
          (Synchronized.synchronizedReducedApproximation input chart certificate) index)
  exact Sampling.emittedSample_eq
    (Synchronized.synchronizedReducedApproximation input chart certificate) index

/-- Every raw sample of the scaled reconstruction of the productive synchronized reference is exactly a finite
prepared-input sample. -/
theorem synchronizedScaledChartSample_reconstructs (input : Gaussian.Name.Basic.Named)
    (chart : Chart input) (certificate : Branch.BranchCertificate input chart)
    (index : Nat) :
    (Scale.scaledDynamicLocalExpLogChartApproximation
        (Synchronized.synchronizedReducedNamed input chart certificate)
        (Approximation.Gaussian.Logarithm.Chart.Reduction.Reconstruction.synchronizedReducedDisk input chart
          certificate)
        (1 / chart.factor)).sample index =
      ComplexLog.inputSample
        (Prepared.preparedChartInput input chart)
        (Comparison.synchronizedReducedSourceIndex input chart certificate index) := by
  change
    ((1 + ComplexLog.inputSample
        (Synchronized.synchronizedReducedNamed input chart certificate) index) /
      (1 - ComplexLog.inputSample
        (Synchronized.synchronizedReducedNamed input chart certificate) index)) *
        (1 / chart.factor) = _
  rw [Approximation.Gaussian.Logarithm.Chart.Reduction.Reconstruction.synchronizedReducedNamed_inputSample input chart
    certificate index]
  exact Approximation.Gaussian.Logarithm.Chart.Reduction.Reconstruction.synchronizedReducedSample_reconstructs input
    chart certificate
    (Comparison.synchronizedReducedSourceIndex input chart certificate index)

/-- The scaled chart reconstruction is operationally the canonical finite sampler of the prepared input state.

The comparison computes only finite indices and uses the explicit source-index reachability theorem above. -/
@[expose] public def synchronizedScaledChartEquivalentPreparedSampling (input : Gaussian.Name.Basic.Named)
    (chart : Chart input) (certificate : Branch.BranchCertificate input chart) :
    Gaussian.Equivalence.Equivalent
      (Scale.scaledDynamicLocalExpLogChartApproximation
        (Synchronized.synchronizedReducedNamed input chart certificate)
        (Approximation.Gaussian.Logarithm.Chart.Reduction.Reconstruction.synchronizedReducedDisk input chart
          certificate)
        (1 / chart.factor))
      (Sampling.approximation
        (Prepared.preparedChartInput input chart)) where
  compare := by
    intro leftStart rightStart target positive
    let right := Sampling.approximation
      (Prepared.preparedChartInput input chart)
    let smallTarget := target / 4
    have smallPositive : 0 < smallTarget :=
      Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive
    let base := right.refineIndex rightStart smallTarget smallPositive
    have baseGe : rightStart ≤ base :=
      right.refineIndex_ge rightStart smallTarget smallPositive
    have baseRadiusSmall : right.radiusSq base < smallTarget :=
      right.refineIndex_accurate rightStart smallTarget smallPositive
    let leftIndex := Comparison.synchronizedReducedOutputIndexForSource
      input chart leftStart base
    exact
      { leftIndex := leftIndex
        rightIndex := base
        left_ge := Comparison.synchronizedReducedOutputIndexForSource_ge
          input chart leftStart base
        right_ge := baseGe
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have baseToLeftSource :
              base ≤ Comparison.synchronizedReducedSourceIndex input chart certificate
                leftLater := by
            exact (Comparison.synchronizedReduced_reachesRequestedSourceIndex
              input chart certificate leftStart base).trans
                (Sampling.emittedSampleIndex_mono
                    (Synchronized.synchronizedReducedApproximation input chart certificate)
                    leftOrder)
          have leftClose := right.later_close baseToLeftSource
          have rightCloseForward := right.later_close rightOrder
          have rightClose :
              Data.Gaussian.Norm.Basic.normSq (right.sample base - right.sample rightLater) ≤
                right.radiusSq base := by
            have reverse :
                right.sample base - right.sample rightLater =
                  -(right.sample rightLater - right.sample base) := by
              apply Data.Gaussian.Basic.ext <;>
                simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
                  Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im] <;> ring1
            rw [reverse, Data.Gaussian.Norm.Basic.normSq_neg]
            exact rightCloseForward
          rw [Approximation.Gaussian.Logarithm.Chart.Reduction.Reconstruction.synchronizedScaledChartSample_reconstructs
            input chart certificate leftLater]
          change Data.Gaussian.Norm.Basic.normSq
              (right.sample
                  (Comparison.synchronizedReducedSourceIndex input chart certificate
                    leftLater) - right.sample rightLater) < target
          calc
            Data.Gaussian.Norm.Basic.normSq
                (right.sample
                    (Comparison.synchronizedReducedSourceIndex input chart certificate
                      leftLater) - right.sample rightLater) ≤
              2 *
                (Data.Gaussian.Norm.Basic.normSq
                    (right.sample
                        (Comparison.synchronizedReducedSourceIndex input chart certificate
                          leftLater) - right.sample base) +
                  Data.Gaussian.Norm.Basic.normSq (right.sample base - right.sample rightLater)) :=
              Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
            _ ≤ 2 * (right.radiusSq base + right.radiusSq base) :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (add_le_add leftClose rightClose) (by decide)
            _ < 2 * (smallTarget + smallTarget) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  baseRadiusSmall baseRadiusSmall)
            _ = target := Purelib.Data.Rat.Fraction.Compatibility.two_quarter_sums target }

/-- Lift the finite sample comparison through the productive wrapper. -/
@[expose] public def synchronizedScaledChart_toPreparedInput (input : Gaussian.Name.Basic.Named)
    (chart : Chart input) (certificate : Branch.BranchCertificate input chart) :
    Gaussian.Equivalence.NamedEquivalent
      (Scale.scaledDynamicLocalExpLogChartApproximation
        (Synchronized.synchronizedReducedNamed input chart certificate)
        (Approximation.Gaussian.Logarithm.Chart.Reduction.Reconstruction.synchronizedReducedDisk input chart
          certificate)
        (1 / chart.factor)).toNamed
      (Prepared.preparedChartInput input chart) :=
  Equivalent.trans
    (Equivalent.toNamed_sampling
      (Scale.scaledDynamicLocalExpLogChartApproximation
        (Synchronized.synchronizedReducedNamed input chart certificate)
        (Approximation.Gaussian.Logarithm.Chart.Reduction.Reconstruction.synchronizedReducedDisk input chart
          certificate)
        (1 / chart.factor)))
    (Approximation.Gaussian.Logarithm.Chart.Reduction.Reconstruction.synchronizedScaledChartEquivalentPreparedSampling
      input chart certificate)

/-- Finite coherence identifies the prepared input state with the original displayed starting state. -/
@[expose] public def preparedChartInput_equivalent (input : Gaussian.Name.Basic.Named) (chart : Chart input)
    (inputCoherent :
      Gaussian.Process.Coherence.Basic.Coherent input.process) :
    Gaussian.Equivalence.NamedEquivalent (Prepared.preparedChartInput input chart) input :=
  inputCoherent.namedEquivalent
    (Prepared.preparedChartInput input chart).state input.state

/-- Exact sample reconstruction plus finite state coherence identifies the scaled synchronized chart with the original
input name. -/
@[expose] public def synchronizedScaledChart_reconstructsInput (input : Gaussian.Name.Basic.Named)
    (chart : Chart input) (certificate : Branch.BranchCertificate input chart)
    (inputCoherent :
      Gaussian.Process.Coherence.Basic.Coherent input.process) :
    Gaussian.Equivalence.NamedEquivalent
      (Scale.scaledDynamicLocalExpLogChartApproximation
        (Synchronized.synchronizedReducedNamed input chart certificate)
        (Approximation.Gaussian.Logarithm.Chart.Reduction.Reconstruction.synchronizedReducedDisk input chart
          certificate)
        (1 / chart.factor)).toNamed
      input :=
  NamedEquivalent.trans
    (Approximation.Gaussian.Logarithm.Chart.Reduction.Reconstruction.synchronizedScaledChart_toPreparedInput input chart
      certificate)
    (Approximation.Gaussian.Logarithm.Chart.Reduction.Reconstruction.preparedChartInput_equivalent input chart
      inputCoherent)
end Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Reconstruction

end
