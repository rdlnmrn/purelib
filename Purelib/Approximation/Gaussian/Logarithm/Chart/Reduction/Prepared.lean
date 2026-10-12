module
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Branch
import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Gaussian.Logarithm (Chart)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Process.Apart

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

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Prepared

/-! ## Synchronized finite chart input -/

/-- The input state reached as a component of the one finite denominator preparation performed by a complex-log chart.
Exposing this state lets the numerator and denominator of a reference quotient read the same finite input candidate. -/
def preparedChartInput (input :
  Named) (chart : Chart input) : Named :=
  { process := input.process
    state :=
      (Preparation.prepareApartState
        chart.denominatorApart
        (Reduction.denominator
          input chart.factor).state).source.1.2 }

/-- Every candidate at the input component selected during denominator preparation is still a candidate at the original
input state. -/
theorem preparedChartInput_possible_original
  (input : Named)
    (chart : Chart input) (certificate : Branch.BranchCertificate input chart)
    {value : Canonical}
    (possible : (preparedChartInput input
      chart).process.Possible
      (preparedChartInput input chart).state value) :
    input.process.Possible input.state value := by
  let prepared := Preparation.prepareApartState
    chart.denominatorApart
    (Reduction.denominator
      input chart.factor).state
  have preparedDenominatorPossible :
      (Reduction.denominator
        input chart.factor).process.Possible prepared.source
          (chart.factor * value + 1) := by
    exact ⟨chart.factor * value, 1,
      ⟨chart.factor, value, rfl, possible, rfl⟩, rfl, rfl⟩
  have originalDenominatorPossible :=
    Preparation.prepareApartState_persists
      chart.denominatorApart
      (Reduction.denominator
        input chart.factor).state preparedDenominatorPossible
  rcases Reduction.denominator_possible
      input chart.factor originalDenominatorPossible with
    ⟨source, sourcePossible, equality⟩
  have scaledEquality : chart.factor * source = chart.factor * value := by
    calc
      chart.factor * source =
          (chart.factor * source + 1) - 1 := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [Data.Gaussian.Basic.add_re,
            Data.Gaussian.Basic.add_im,
            Data.Gaussian.Basic.sub_re,
            Data.Gaussian.Basic.sub_im,
            Data.Gaussian.Basic.one_re,
            Data.Gaussian.Basic.one_im] <;> ring1
      _ = (chart.factor * value + 1) - 1 := by rw [equality]
      _ = chart.factor * value := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [Data.Gaussian.Basic.add_re,
            Data.Gaussian.Basic.add_im,
            Data.Gaussian.Basic.sub_re,
            Data.Gaussian.Basic.sub_im,
            Data.Gaussian.Basic.one_re,
            Data.Gaussian.Basic.one_im] <;> ring1
  have sourceEqual : source = value := by
    apply Data.Gaussian.Field.mul_right_cancel_of_ne
      certificate.factor_ne_zero
    calc
      source * chart.factor = chart.factor * source :=
        Data.Gaussian.Basic.mul_comm _ _
      _ = chart.factor * value := scaledEquality
      _ = value * chart.factor :=
        Data.Gaussian.Basic.mul_comm _ _
  change input.process.Possible input.state source at sourcePossible
  rw [← sourceEqual]
  exact sourcePossible

/-- The synchronized rational reduced coordinate read from one prepared input candidate. -/
def synchronizedReducedValue (input :
  Named) (chart : Chart input)
    (value : Canonical) : Canonical :=
  (chart.factor * value - 1) / (chart.factor * value + 1)

/-- Every candidate at the retained prepared input satisfies the original chart denominator's lower squared-norm bound.
-/
theorem preparedChartInput_denominator_lower
  (input : Named)
    (chart : Chart input) (certificate : Branch.BranchCertificate input chart)
    {value : Canonical}
    (possible : (preparedChartInput input
      chart).process.Possible
      (preparedChartInput input chart).state value) :
    chart.denominatorApart.lowerSq ≤ Data.Gaussian.Norm.Basic.normSq (chart.factor * value + 1) := by
  have originalPossible :=
    preparedChartInput_possible_original input chart
      certificate possible
  apply chart.denominatorApart.lower
    (Reduction.denominator input chart.factor).state
  exact ⟨chart.factor * value, 1,
    ⟨chart.factor, value, rfl, originalPossible, rfl⟩, rfl, rfl⟩

/-- The chart denominator is nonzero at every candidate in the retained prepared input state. -/
theorem preparedChartInput_denominator_ne_zero
  (input : Named)
    (chart : Chart input) (certificate : Branch.BranchCertificate input chart)
    {value : Canonical}
    (possible : (preparedChartInput input
      chart).process.Possible
      (preparedChartInput input chart).state value) :
    chart.factor * value + 1 ≠ 0 := by
  have lower :=
    preparedChartInput_denominator_lower input chart
      certificate possible
  intro equal
  rw [equal, Data.Gaussian.Norm.Basic.normSq_zero] at lower
  exact (not_le_of_gt chart.denominatorApart.positive) lower

/-- Using one prepared input candidate for both numerator and denominator is admitted by the original stateful quotient.
-/
theorem synchronizedReducedValue_possible
  (input : Named)
    (chart : Chart input) (certificate : Branch.BranchCertificate input chart)
    {value : Canonical}
    (possible : (preparedChartInput input
      chart).process.Possible
      (preparedChartInput input chart).state value) :
    (Reduction.reduced input chart.factor
      chart.denominatorApart).process.Possible
        (Reduction.reduced input chart.factor
          chart.denominatorApart).state
        (synchronizedReducedValue input chart value) := by
  have originalPossible :=
    preparedChartInput_possible_original input chart
      certificate possible
  have numeratorPossible :
      (Reduction.numerator
        input chart.factor).process.Possible
          (Reduction.numerator
            input chart.factor).state
          (chart.factor * value - 1) := by
    refine ⟨chart.factor * value, -1,
      ⟨chart.factor, value, rfl, originalPossible, rfl⟩,
      ⟨1, rfl, rfl⟩, ?_⟩
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im,
        Data.Gaussian.Basic.sub_re,
        Data.Gaussian.Basic.sub_im,
        Data.Gaussian.Basic.neg_re,
        Data.Gaussian.Basic.neg_im,
        Data.Gaussian.Basic.one_re,
        Data.Gaussian.Basic.one_im] <;> ring1
  have denominatorPossible :
      (Reduction.preparedDenominator
        input chart.factor chart.denominatorApart).process.Possible
          (Reduction.preparedDenominator
            input chart.factor chart.denominatorApart).state
          (chart.factor * value + 1) := by
    exact ⟨chart.factor * value, 1,
      ⟨chart.factor, value, rfl, possible, rfl⟩, rfl, rfl⟩
  exact ⟨chart.factor * value - 1, chart.factor * value + 1,
    numeratorPossible, denominatorPossible, rfl⟩
end Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Prepared

end
