module
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Branch
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Exact.Reconstruction
import Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error
public import Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Sequence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Geometric.Quarter
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential.Progressive.Range
open Purelib.Approximation.Gaussian.Logarithm
open Purelib.Approximation.Gaussian.Logarithm.Chart
open Purelib.Approximation.Gaussian.Logarithm.Chart.Exact
open Purelib.Approximation.Gaussian.Logarithm.Local.Inverse
open Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat
open Purelib.Data.Rat.Geometric

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

/-- The scale-one geometric squared-error request at the displayed finite depth. -/
@[expose] def correctionTarget (depth : Nat) : Fraction.Rational :=
  Geometric.Basic.quarterRadius 1 depth

/-- Every displayed correction sample target is strictly positive. -/
theorem correctionTarget_pos (depth : Nat) : 0 <
  Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionTarget depth :=
  Geometric.Basic.quarterRadius_pos (by decide) depth

/-- Request the branch certificate's finite comparison between the correction exponential and the exact reciprocal chart
factor.

Both initial indices are zero and the requested squared tolerance is the retained depth's geometric target. -/
@[expose] def correctionComparison (input : Data.Gaussian.Basic.Canonical)
    (chart : Chart (Named.exact input))
    (certificate : Branch.BranchCertificate
      (Named.exact input) chart)
    (depth : Nat) :=
  certificate.correction_exponential.compare 0 0
    (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionTarget depth)
    (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionTarget_pos depth)

/-- A computably scheduled sample of the supplied correction's global CCL exponential.

Its index is obtained directly from the branch certificate. -/
@[expose] def correctionExponentialSample (input : Data.Gaussian.Basic.Canonical)
    (chart : Chart (Named.exact input))
    (certificate : Branch.BranchCertificate
      (Named.exact input) chart)
    (depth : Nat) : Data.Gaussian.Basic.Canonical :=
  (Sampling.approximation
      (Name.named chart.correction)).sample
    (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionComparison input chart certificate
      depth).leftIndex

/-- The certificate-scheduled correction exponential sample is within the depth's strict squared-error target of the
reciprocal chart factor. -/
theorem correctionExponentialSample_close (input : Data.Gaussian.Basic.Canonical)
    (chart : Chart (Named.exact input))
    (certificate : Branch.BranchCertificate
      (Named.exact input) chart)
    (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionExponentialSample input chart certificate
      depth -
      1 / chart.factor) < Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionTarget depth := by
  have close := (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionComparison input chart
    certificate depth).close
    (Nat.le_refl _) (Nat.le_refl _)
  exact close

/-- The canonical correction exponential sampler's retained uniform squared-norm bound. -/
@[expose] def correctionExponentialBound (input : Data.Gaussian.Basic.Canonical)
    (chart : Chart (Named.exact input)) :
    Fraction.Rational :=
  (Sampling.approximation
    (Name.named chart.correction)).centerBound

/-- The retained correction exponential bound is nonnegative. -/
theorem correctionExponentialBound_nonnegative (input : Data.Gaussian.Basic.Canonical)
    (chart : Chart (Named.exact input)) :
    0 ≤ Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionExponentialBound input chart :=
  (Sampling.approximation
    (Name.named chart.correction)).centerBound_nonneg

/-- Every certificate-scheduled correction exponential sample satisfies its retained uniform squared-norm bound. -/
theorem correctionExponentialSample_bounded (input : Data.Gaussian.Basic.Canonical)
    (chart : Chart (Named.exact input))
    (certificate : Branch.BranchCertificate
      (Named.exact input) chart)
    (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionExponentialSample input chart certificate
      depth) ≤
      Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionExponentialBound input chart :=
  (Sampling.approximation
    (Name.named chart.correction)).sample_bounded _

/-- The product normal form supplied by the exponential addition law for the exponential of the charted logarithm:
exponentiate the local logarithm and the branch correction, then multiply the two finite rational samples. -/
@[expose] def expChartedLogSample (input : Data.Gaussian.Basic.Canonical)
    (chart : Chart (Named.exact input))
    (certificate : Branch.BranchCertificate
      (Named.exact input) chart)
    (depth : Nat) : Data.Gaussian.Basic.Canonical :=
  Error.localExpLogSample
      (Reconstruction.exactReducedValue input chart) depth *
    Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionExponentialSample input chart certificate
      depth

/-- The rational error coefficient combining the finite local inverse estimate with correction sampling and the
reciprocal chart factor. -/
@[expose] def expChartedLogErrorScale (input : Data.Gaussian.Basic.Canonical)
    (chart : Chart (Named.exact input)) :
    Fraction.Rational :=
  2 * (5 * 10 +
    Error.expLogErrorScale *
      Data.Gaussian.Norm.Basic.normSq (1 / chart.factor))

/-- The charted exponential–logarithm error coefficient is nonnegative. -/
theorem expChartedLogErrorScale_nonnegative (input : Data.Gaussian.Basic.Canonical)
    (chart : Chart (Named.exact input)) :
    0 ≤ Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogErrorScale input chart :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (by decide))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        Error.expLogErrorScale_nonnegative
        (Data.Gaussian.Norm.Basic.normSq_nonneg _)))

/-- Each finite anchored charted exponential–logarithm sample approximates the exact original input with the displayed
geometric squared-error bound. -/
theorem expChartedLogSample_error (input : Data.Gaussian.Basic.Canonical)
    (chart : Chart (Named.exact input))
    (certificate : Branch.BranchCertificate
      (Named.exact input) chart)
    (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogSample input chart certificate depth -
      input) ≤
      Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogErrorScale input chart * (1 / 4) ^
        depth := by
  let reduced := Reconstruction.exactReducedValue input chart
  let localSample :=
    Error.localExpLogSample reduced depth
  let correction := Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionExponentialSample input
    chart certificate depth
  let chartValue := (1 + reduced) / (1 - reduced)
  let inverseFactor := 1 / chart.factor
  have reducedBound : Data.Gaussian.Norm.Basic.normSq reduced ≤ 1 / 9 :=
    Reconstruction.exactReducedValue_disk input chart
  have localError :
      Data.Gaussian.Norm.Basic.normSq (localSample - chartValue) ≤
        Error.expLogErrorScale *
          (1 / 4 : Fraction.Rational) ^ depth :=
    Error.localExpLogSample_chart_error
      reducedBound depth
  have localBound : Data.Gaussian.Norm.Basic.normSq localSample ≤ 5 * 10 :=
    Sequence.localExpLogSample_bounded
      reducedBound depth
  have correctionError :
      Data.Gaussian.Norm.Basic.normSq (correction - inverseFactor) ≤
        (1 / 4 : Fraction.Rational) ^ depth := by
    simpa only [Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionTarget,
      Geometric.Basic.quarterRadius_eq_mul_pow,
      Fraction.Field.one_mul] using
        (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionExponentialSample_close input chart
          certificate depth).le
  have targetIdentity : chartValue * inverseFactor = input :=
    Reconstruction.exactReducedValue_chart_times_inverse input chart certificate
  have split : localSample * correction - chartValue * inverseFactor =
      localSample * (correction - inverseFactor) +
        (localSample - chartValue) * inverseFactor := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.sub_re,
        Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;> ring1
  change Data.Gaussian.Norm.Basic.normSq (localSample * correction - input) ≤
    Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogErrorScale input chart * (1 / 4) ^ depth
  calc
    Data.Gaussian.Norm.Basic.normSq (localSample * correction - input) =
        Data.Gaussian.Norm.Basic.normSq (localSample * correction - chartValue * inverseFactor) := by
      exact congrArg Data.Gaussian.Norm.Basic.normSq
        (congrArg (fun value => localSample * correction - value)
          targetIdentity.symm)
    _ = Data.Gaussian.Norm.Basic.normSq (localSample * (correction - inverseFactor) +
        (localSample - chartValue) * inverseFactor) := by rw [split]
    _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (localSample * (correction - inverseFactor)) +
        Data.Gaussian.Norm.Basic.normSq ((localSample - chartValue) * inverseFactor)) :=
      Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ = 2 * (Data.Gaussian.Norm.Basic.normSq localSample * Data.Gaussian.Norm.Basic.normSq (correction
      - inverseFactor) +
        Data.Gaussian.Norm.Basic.normSq (localSample - chartValue) * Data.Gaussian.Norm.Basic.normSq
          inverseFactor) := by
      rw [Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul]
    _ ≤ 2 * ((5 * 10) * (1 / 4) ^ depth +
        (Error.expLogErrorScale *
          (1 / 4) ^ depth) * Data.Gaussian.Norm.Basic.normSq inverseFactor) := by
      apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
        (by decide)
      exact add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_direct localBound correctionError
          (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide))
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          localError (Data.Gaussian.Norm.Basic.normSq_nonneg _))
    _ = Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogErrorScale input chart * (1 / 4) ^
      depth := by
      dsimp only [Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogErrorScale, inverseFactor]
      ring1

/-- Four times the charted exponential–logarithm error coefficient, bounding movement between finite samples. -/
@[expose] def expChartedLogApproximationScale (input : Data.Gaussian.Basic.Canonical)
    (chart : Chart (Named.exact input)) :
    Fraction.Rational :=
  4 * Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogErrorScale input chart

/-- The charted exponential–logarithm movement scale is nonnegative. -/
theorem expChartedLogApproximationScale_nonnegative (input : Data.Gaussian.Basic.Canonical)
    (chart : Chart (Named.exact input)) :
    0 ≤ Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogApproximationScale input chart :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogErrorScale_nonnegative input chart)

/-- A limit-free approximation for the exponential of an anchored, charted logarithm.

Every sample is a finite Gaussian-rational calculation: the local logarithm recurrence, its finite exponential
recurrence, one requested sample of the correction's CCL exponential, and one Gaussian multiplication. -/
@[expose] def expChartedLogApproximation (input : Data.Gaussian.Basic.Canonical)
    (chart : Chart (Named.exact input))
    (certificate : Branch.BranchCertificate
      (Named.exact input) chart) :
    ApproximationData where
  sample := Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogSample input chart certificate
  radiusSq := fun depth =>
    Geometric.Basic.quarterRadius
      (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogApproximationScale input chart) depth
  radiusSq_nonneg := fun depth =>
    Geometric.Basic.quarterRadius_nonneg
      (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogApproximationScale_nonnegative input
        chart) depth
  later_close := by
    intro earlier later order
    have laterError := Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogSample_error input
      chart certificate later
    have earlierError := Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogSample_error input
      chart certificate earlier
    have laterScaled :
        Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogErrorScale input chart * (1 / 4) ^
          later ≤
          Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogErrorScale input chart * (1 / 4) ^
            earlier :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Quarter.quarterPower_antitone order)
        (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogErrorScale_nonnegative input chart)
    have earlierReverse :
        Data.Gaussian.Norm.Basic.normSq (input -
          Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogSample input chart certificate
          earlier) ≤
          Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogErrorScale input chart * (1 / 4) ^
            earlier := by
      have identity : input - Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogSample input
        chart certificate earlier =
          -(Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogSample input chart certificate
            earlier - input) := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
            Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im] <;> ring1
      rw [identity, Data.Gaussian.Norm.Basic.normSq_neg]
      exact earlierError
    calc
      Data.Gaussian.Norm.Basic.normSq
        (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogSample input chart certificate later
        -
          Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogSample input chart certificate
            earlier) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq
            (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogSample input chart certificate
              later - input) +
          Data.Gaussian.Norm.Basic.normSq
            (input - Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogSample input chart
              certificate earlier)) :=
        Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ input _
      _ ≤ 2 * (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogErrorScale input chart * (1 /
        4) ^ earlier +
          Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogErrorScale input chart * (1 / 4) ^
            earlier) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add (laterError.trans laterScaled) earlierReverse) (by decide)
      _ = Geometric.Basic.quarterRadius
          (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogApproximationScale input chart)
            earlier := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow]
        dsimp only [Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogApproximationScale]
        ring1
  refineIndex := fun current target positive =>
    Search.firstQuarterBelow
      (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogApproximationScale input chart)
        current target
  refineIndex_ge := by
    intro current target positive
    exact Search.firstQuarterBelow_ge
      (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogApproximationScale input chart)
        current target
  refineIndex_accurate := by
    intro current target positive
    exact Search.firstQuarterBelow_accurate
      (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogApproximationScale input chart)
      (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogApproximationScale_nonnegative input
        chart)
      current target positive
  centerBound := (5 * 10) * Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionExponentialBound
    input chart
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (by decide))
      (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionExponentialBound_nonnegative input chart)
  sample_bounded := by
    intro depth
    rw [Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogSample,
      Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct
      (Sequence.localExpLogSample_bounded
        (Reconstruction.exactReducedValue_disk input chart) depth)
      (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.correctionExponentialSample_bounded input chart
        certificate depth)
      (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (by decide))

/-- The operational inverse approximation exposed through the ordinary productive CCL controller. -/
@[expose] def expChartedLogNamed (input : Data.Gaussian.Basic.Canonical)
    (chart : Chart (Named.exact input))
    (certificate : Branch.BranchCertificate
      (Named.exact input) chart) : Gaussian.Name.Basic.Named :=
  (Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence.expChartedLogApproximation input chart
    certificate).toNamed

end

end Purelib.Approximation.Gaussian.Logarithm.Chart.Exact.Inverse.Sequence
