module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
public import Purelib.Approximation.Gaussian.Process.Coherence.Division
public import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Request.Addition
import Purelib.Approximation.Gaussian.Request.Basic
import Purelib.Approximation.Gaussian.Request.Division
import Purelib.Approximation.Gaussian.Request.Multiplication
import Purelib.Approximation.Rational.Request.Common
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Process.Addition
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Process.Coherence.Basic

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

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Sampling

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Logarithm
open Purelib.Approximation.Gaussian.Logarithm.Chart
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Request.Basic
open Purelib.Approximation.Rational.Request
open Purelib.Data.Rat

/-- A sufficiently small positive reduced-chart refinement request makes both retained input coherence allowances
smaller than the displayed target.

The bound follows the actual numerator and prepared-denominator refinement schedules, preserving their distinct input
states. -/
private theorem reducedRefine_input_allowances_lt
    (input : Name.Basic.Named) (chart : Chart input)
    (inputCoherent :
      Coherent input.process)
    (state : (reduced input chart.factor
      chart.denominatorApart).process.State)
    (request : Fraction.Rational)
    (requestPositive : 0 < request)
    (target : Fraction.Rational)
    (targetPositive : 0 < target)
    (requestSmall :
      request <
        Coherent.divisionOuterTarget
          (Reduction.numerator input chart.factor).process
          (Reduction.preparedDenominator input
            chart.factor chart.denominatorApart).process
          (preparedDenominatorApart input
            chart.factor chart.denominatorApart).certificate.lowerSq
          (inputCoherent.accuracyRequest target)) :
    let refined :=
      (reduced input chart.factor
        chart.denominatorApart).process.refine state request requestPositive
    inputCoherent.allowance refined.1.1.2 < target ∧
      inputCoherent.allowance refined.2.source.1.2 < target := by
  let numerator :=
    Reduction.numerator input chart.factor
  let preparedDenominator :=
    Reduction.preparedDenominator input chart.factor
      chart.denominatorApart
  let denominatorApart :=
    (preparedDenominatorApart input
      chart.factor chart.denominatorApart).certificate
  let leftName := Name.centerOnly
    (numerator.process.ball state.1).center numerator.process.centerBound
      numerator.process.centerBound_nonneg
      (numerator.process.center_bounded state.1)
  let rightName := Name.centerOnly
    (preparedDenominator.process.ball state.2).center
      preparedDenominator.process.centerBound
      preparedDenominator.process.centerBound_nonneg
      (preparedDenominator.process.center_bounded state.2)
  let divisionInput :=
    Name.divisionInputTarget
      leftName rightName denominatorApart.lowerSq request
  have divisionInputPositive : 0 < divisionInput :=
    Name.divisionInputTarget_pos
      leftName rightName denominatorApart.lowerSq denominatorApart.positive
        requestPositive
  have divisionInputSmall :
      divisionInput < inputCoherent.accuracyRequest target :=
    Coherent.processDivisionInputTarget_lt
      leftName rightName rfl rfl denominatorApart.positive requestSmall
  let numeratorAddInput :=
    Name.additiveInputTarget divisionInput
  have numeratorAddPositive : 0 < numeratorAddInput :=
    Bounds.Quarter.quarter_pos
      divisionInputPositive
  have numeratorAddSmall : numeratorAddInput < divisionInput :=
    Coherent.additiveInputTarget_lt_target
      divisionInputPositive
  let numeratorFactorName :=
    Name.centerOnly
      ((Process.exact chart.factor).ball
        state.1.1.1).center
      (Process.exact
        chart.factor).centerBound
      (Process.exact
        chart.factor).centerBound_nonneg
      ((Process.exact
        chart.factor).center_bounded state.1.1.1)
  let numeratorInputName :=
    Name.centerOnly
      (input.process.ball state.1.1.2).center input.process.centerBound
      input.process.centerBound_nonneg
      (input.process.center_bounded state.1.1.2)
  let numeratorInput :=
    Name.multiplicativeInputTarget
      numeratorFactorName numeratorInputName numeratorAddInput
  have numeratorInputPositive : 0 < numeratorInput :=
    Name.multiplicativeInputTarget_pos
      numeratorFactorName numeratorInputName numeratorAddPositive
  have numeratorInputSmall :
      numeratorInput < inputCoherent.accuracyRequest target :=
    (Coherent.processMultiplicativeInputTarget_lt_target
      numeratorFactorName numeratorInputName numeratorAddPositive).trans
        (numeratorAddSmall.trans divisionInputSmall)
  let apartInput := Common.commonTarget
    divisionInput (chart.denominatorApart.lowerSq / 12)
  have apartInputPositive : 0 < apartInput :=
    Common.commonTarget_pos divisionInputPositive
      chart.denominatorApart.twelfth_pos
  have apartInputSmall : apartInput < divisionInput :=
    Common.commonTarget_lt_left
      divisionInputPositive chart.denominatorApart.twelfth_pos
  let denominatorAddInput :=
    Name.additiveInputTarget apartInput
  have denominatorAddPositive : 0 < denominatorAddInput :=
    Bounds.Quarter.quarter_pos apartInputPositive
  have denominatorAddSmall : denominatorAddInput < apartInput :=
    Coherent.additiveInputTarget_lt_target
      apartInputPositive
  let denominatorFactorName :=
    Name.centerOnly
      ((Process.exact chart.factor).ball
        state.2.source.1.1).center
      (Process.exact
        chart.factor).centerBound
      (Process.exact
        chart.factor).centerBound_nonneg
      ((Process.exact
        chart.factor).center_bounded state.2.source.1.1)
  let denominatorInputName :=
    Name.centerOnly
      (input.process.ball state.2.source.1.2).center input.process.centerBound
      input.process.centerBound_nonneg
      (input.process.center_bounded state.2.source.1.2)
  let denominatorInput :=
    Name.multiplicativeInputTarget
      denominatorFactorName denominatorInputName denominatorAddInput
  have denominatorInputPositive : 0 < denominatorInput :=
    Name.multiplicativeInputTarget_pos
      denominatorFactorName denominatorInputName denominatorAddPositive
  have denominatorInputSmall :
      denominatorInput < inputCoherent.accuracyRequest target :=
    (Coherent.processMultiplicativeInputTarget_lt_target
      denominatorFactorName denominatorInputName denominatorAddPositive).trans
        (denominatorAddSmall.trans (apartInputSmall.trans divisionInputSmall))
  change inputCoherent.allowance
      (input.process.refine state.1.1.2 numeratorInput
        numeratorInputPositive) < target ∧
    inputCoherent.allowance
      (input.process.refine state.2.source.1.2 denominatorInput
        denominatorInputPositive) < target
  exact ⟨inputCoherent.refine_accurate state.1.1.2 target targetPositive
      numeratorInput numeratorInputPositive numeratorInputSmall,
    inputCoherent.refine_accurate state.2.source.1.2 target targetPositive
      denominatorInput denominatorInputPositive denominatorInputSmall⟩

/-- At a canonical reduced-chart sample index satisfying the retained outer request bound, both original input
allowances are below the positive target. -/
public theorem reducedStateAt_input_allowances_lt
    (input : Name.Basic.Named) (chart : Chart input)
    (inputCoherent :
      Coherent input.process)
    (start : (reduced input chart.factor
      chart.denominatorApart).process.State)
    (index : Nat) (target : Fraction.Rational)
    (targetPositive : 0 < target)
    (requestSmall :
      Process.Sampling.refinementTarget index <
        Coherent.divisionOuterTarget
          (Reduction.numerator input chart.factor).process
          (Reduction.preparedDenominator input
            chart.factor chart.denominatorApart).process
          (preparedDenominatorApart input
            chart.factor chart.denominatorApart).certificate.lowerSq
          (inputCoherent.accuracyRequest target)) :
    let state := Process.Sampling.stateAt
      (reduced input chart.factor
        chart.denominatorApart).process start index
    inputCoherent.allowance state.1.1.2 < target ∧
      inputCoherent.allowance state.2.source.1.2 < target := by
  cases index with
  | zero =>
      exact reducedRefine_input_allowances_lt input chart
        inputCoherent start
        _ _ target targetPositive requestSmall
  | succ index =>
      exact reducedRefine_input_allowances_lt input chart
        inputCoherent
        (Process.Sampling.stateAt
          (reduced input chart.factor
            chart.denominatorApart).process start index)
        _ _ target targetPositive requestSmall

/-- Every finite candidate of the stateful reduced process exposes the two finite input candidates independently used by
its numerator and denominator. -/
theorem reducedPossible_sources (input : Name.Basic.Named) (chart : Chart input)
    {state : (reduced input chart.factor
      chart.denominatorApart).process.State}
    {value : Data.Gaussian.Basic.Canonical}
    (possible :
      (reduced input chart.factor
        chart.denominatorApart).process.Possible state value) :
    ∃ numeratorSource denominatorSource : Data.Gaussian.Basic.Canonical,
      input.process.Possible state.1.1.2 numeratorSource ∧
      input.process.Possible state.2.source.1.2 denominatorSource ∧
      value = (chart.factor * numeratorSource - 1) /
        (chart.factor * denominatorSource + 1) := by
  rcases possible with
    ⟨numeratorValue, denominatorValue, numeratorPossible,
      denominatorPossible, valueEqual⟩
  rcases numerator_possible
      input chart.factor numeratorPossible with
    ⟨numeratorSource, numeratorSourcePossible, numeratorEqual⟩
  rcases denominator_possible
      input chart.factor denominatorPossible with
    ⟨denominatorSource, denominatorSourcePossible, denominatorEqual⟩
  exact ⟨numeratorSource, denominatorSource, numeratorSourcePossible,
    denominatorSourcePossible, by
      rw [valueEqual, numeratorEqual, denominatorEqual]⟩
end Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Sampling

end
