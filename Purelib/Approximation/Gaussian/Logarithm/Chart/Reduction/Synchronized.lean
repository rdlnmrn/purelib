module
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Branch
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Prepared
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Homography.Cayley.Bounds
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Gaussian.Logarithm (Chart)
open Purelib.Approximation.Gaussian.Name.Basic (Named)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Sampling

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Rat

section
@[expose] public section

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

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Synchronized

/-- The diagonal finite reduced-coordinate sampler. -/
def synchronizedReducedSample (input :
  Named) (chart : Chart input)
    (index : Nat) : Data.Gaussian.Basic.Canonical :=
  Prepared.synchronizedReducedValue input chart
    (ComplexLog.inputSample
      (Prepared.preparedChartInput input chart) index)

/-- Every synchronized prepared-input reduced sample satisfies the chart's one-ninth quadrance bound. -/
theorem synchronizedReducedSample_disk
  (input : Named)
    (chart : Chart input) (certificate : Branch.BranchCertificate input chart)
    (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (synchronizedReducedSample input chart index) ≤ 1 /
      9 := by
  apply chart.reducedDisk.possible_normSq
  apply Prepared.synchronizedReducedValue_possible input chart certificate
  exact ComplexLog.inputSample_possible_start
    (Prepared.preparedChartInput input chart) index

/-- The rational reduced-chart sensitivity coefficient determined by the chart factor and retained denominator lower
squared norm. -/
def synchronizedReducedSensitivity (input :
  Named) (chart : Chart input) :
    Fraction.Rational :=
  (4 * Data.Gaussian.Norm.Basic.normSq chart.factor) /
    (chart.denominatorApart.lowerSq * chart.denominatorApart.lowerSq)

/-- The synchronized reduced-chart sensitivity coefficient is nonnegative. -/
theorem
  synchronizedReducedSensitivity_nonneg
  (input : Named)
    (chart : Chart input) :
    0 ≤ synchronizedReducedSensitivity input chart := by
  apply Fraction.Order.Field.div_nonneg_direct
  · exact Fraction.Order.Arithmetic.mul_nonneg_direct
      (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg chart.factor)
  · exact Fraction.Order.Arithmetic.mul_nonneg_direct
      chart.denominatorApart.positive.le chart.denominatorApart.positive.le

/-- Four times the retained reduced-chart sensitivity, accounting for canonical input sample movement. -/
def synchronizedReducedErrorScale (input :
  Named) (chart : Chart input) :
    Fraction.Rational :=
  synchronizedReducedSensitivity input chart * 4

/-- The synchronized reduced-sample error scale is nonnegative. -/
theorem
  synchronizedReducedErrorScale_nonneg
  (input : Named)
    (chart : Chart input) :
    0 ≤ synchronizedReducedErrorScale input chart :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (synchronizedReducedSensitivity_nonneg input chart)
      (by decide)

/-- An anchored chart's nonzero factor makes the synchronized reduced-sample error scale strictly positive. -/
theorem synchronizedReducedErrorScale_pos
  (input : Named)
    (chart : Chart input) (certificate : Branch.BranchCertificate input chart) :
    0 < synchronizedReducedErrorScale input chart
      := by
  have factorPositive : 0 < Data.Gaussian.Norm.Basic.normSq chart.factor :=
    Data.Gaussian.Norm.Basic.normSq_pos certificate.factor_ne_zero
  have numeratorPositive : 0 < 4 * Data.Gaussian.Norm.Basic.normSq chart.factor :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) factorPositive
  have denominatorPositive :
      0 < chart.denominatorApart.lowerSq *
        chart.denominatorApart.lowerSq :=
    Fraction.Order.Arithmetic.mul_pos_direct
      chart.denominatorApart.positive chart.denominatorApart.positive
  unfold synchronizedReducedErrorScale
    synchronizedReducedSensitivity
  exact Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Field.div_pos_direct numeratorPositive
      denominatorPositive) (by decide)

/-- Later synchronized reduced samples remain within the earlier index's geometric squared-error radius. -/
theorem
  synchronizedReducedSample_later_close
  (input : Named)
    (chart : Chart input) (certificate : Branch.BranchCertificate input chart)
    {oldIndex newIndex : Nat} (order : oldIndex ≤ newIndex) :
    Data.Gaussian.Norm.Basic.normSq
        (synchronizedReducedSample input chart newIndex -
          synchronizedReducedSample input chart oldIndex)
            ≤
      Geometric.Basic.quarterRadius
        (synchronizedReducedErrorScale input
          chart) oldIndex := by
  let newValue := ComplexLog.inputSample
    (Prepared.preparedChartInput input chart) newIndex
  let oldValue := ComplexLog.inputSample
    (Prepared.preparedChartInput input chart) oldIndex
  have newPossible :=
    ComplexLog.inputSample_possible_start
      (Prepared.preparedChartInput input chart) newIndex
  have oldPossible :=
    ComplexLog.inputSample_possible_start
      (Prepared.preparedChartInput input chart) oldIndex
  have newLower := Prepared.preparedChartInput_denominator_lower input chart
    certificate newPossible
  have oldLower := Prepared.preparedChartInput_denominator_lower input chart
    certificate oldPossible
  have sensitivity :=
    Geometry.Projective.Homography.Cayley.Bounds.scaledReduced_input_close
      chart.factor newValue oldValue chart.denominatorApart.lowerSq
      chart.denominatorApart.positive newLower oldLower
  have movement :=
    Sampling.inputSample_later_close
      (Prepared.preparedChartInput input chart) order
  change Data.Gaussian.Norm.Basic.normSq
      (Prepared.synchronizedReducedValue input chart newValue -
        Prepared.synchronizedReducedValue input chart oldValue) ≤ _
  calc
    Data.Gaussian.Norm.Basic.normSq
        (Prepared.synchronizedReducedValue input chart newValue -
          Prepared.synchronizedReducedValue input chart oldValue) ≤
        synchronizedReducedSensitivity input chart *
          Data.Gaussian.Norm.Basic.normSq (newValue - oldValue) := by
      exact sensitivity
    _ ≤ synchronizedReducedSensitivity input chart *
        Geometric.Basic.quarterRadius 4 oldIndex :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movement
        (synchronizedReducedSensitivity_nonneg input
          chart)
    _ = Geometric.Basic.quarterRadius
          (synchronizedReducedErrorScale input chart)
            oldIndex := by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow,
        Geometric.Basic.quarterRadius_eq_mul_pow]
      unfold synchronizedReducedErrorScale
      ring1

/-- A limit-free synchronized reduced-coordinate reference. -/
def synchronizedReducedApproximation (input
  : Named) (chart : Chart input)
    (certificate : Branch.BranchCertificate input chart) : ApproximationData where
  sample := synchronizedReducedSample input chart
  radiusSq := Geometric.Basic.quarterRadius
    (synchronizedReducedErrorScale input chart)
  radiusSq_nonneg index :=
    Geometric.Basic.quarterRadius_nonneg
      (synchronizedReducedErrorScale_nonneg input chart)
        index
  later_close := synchronizedReducedSample_later_close
    input chart certificate
  refineIndex current target _ :=
    Search.firstQuarterBelow
      (synchronizedReducedErrorScale input chart) current
        target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge
      (synchronizedReducedErrorScale input chart) current
        target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate
      (synchronizedReducedErrorScale input chart)
      (synchronizedReducedErrorScale_nonneg input chart)
  centerBound := 1 / 9
  centerBound_nonneg := by decide
  sample_bounded := synchronizedReducedSample_disk input
    chart certificate

/-- Start the productive name generated from the synchronized reduced-coordinate approximation and the retained branch
certificate. -/
def synchronizedReducedNamed (input :
  Named) (chart : Chart input)
    (certificate : Branch.BranchCertificate input chart) : Named :=
  (synchronizedReducedApproximation input chart
    certificate).toNamed
end Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Synchronized

end
