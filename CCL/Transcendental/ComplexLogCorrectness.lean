import mathlib.Tactic.QuotientFreeRing
import CCL.Transcendental.ComplexLogChart
import CCL.Transcendental.FinitePolynomial
import CCL.Arithmetic.OperationalEquivalence
import CCL.Progressive.ExpRange
import CCL.Transcendental.Coherence

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

namespace CCL.ComplexLogCorrectness

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev Chart := CCL.ComplexLogChart.Chart
abbrev NamedEquivalent :=
  CCL.OperationalEquivalence.NamedEquivalent
abbrev Approximation :=
  CCL.ProgressiveApproximation.Approximation
abbrev Equivalent :=
  CCL.OperationalEquivalence.Equivalent

open RFAP.ConstructiveGaussian.Gaussian

/-- A supplied correction is semantically anchored when its CCL exponential
agrees operationally with the exact reciprocal of the displayed chart
factor.  Different anchored corrections may still encode different branches;
the exponential condition deliberately identifies their common logarithmic
meaning without choosing a global cut. -/
structure BranchCertificate (input : Named) (chart : Chart input) where
  factor_ne_zero : chart.factor ≠ 0
  correction_exponential :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named chart.correction)
      (CCL.ProgressiveTransducer.Named.exact
        (1 / chart.factor))

/-! ## Finite coherence of the stateful chart arithmetic -/

/-- Scaling a coherent input by the displayed rational chart factor remains
coherent. -/
def scaledCoherent (input : Named) (chart : Chart input)
    (inputCoherent :
      CCL.ProgressiveCoherence.Coherent input.process) :
    CCL.ProgressiveCoherence.Coherent
      (CCL.ComplexLogChart.scaled input chart.factor).process :=
  CCL.ProgressiveCoherence.Coherent.mul
    (CCL.ProgressiveCoherence.Coherent.exact chart.factor)
    inputCoherent

/-- The stateful chart numerator inherits finite coherence. -/
def numeratorCoherent (input : Named) (chart : Chart input)
    (inputCoherent :
      CCL.ProgressiveCoherence.Coherent input.process) :
    CCL.ProgressiveCoherence.Coherent
      (CCL.ComplexLogChart.numerator input chart.factor).process :=
  CCL.ProgressiveCoherence.Coherent.sub
    (scaledCoherent input chart inputCoherent)
    (CCL.ProgressiveCoherence.Coherent.exact 1)

/-- The unprepared stateful chart denominator inherits finite coherence. -/
def denominatorCoherent (input : Named) (chart : Chart input)
    (inputCoherent :
      CCL.ProgressiveCoherence.Coherent input.process) :
    CCL.ProgressiveCoherence.Coherent
      (CCL.ComplexLogChart.denominator input chart.factor).process :=
  CCL.ProgressiveCoherence.Coherent.add
    (scaledCoherent input chart inputCoherent)
    (CCL.ProgressiveCoherence.Coherent.exact 1)

/-- One finite whole-ball apartness preparation preserves denominator
coherence. -/
def preparedDenominatorCoherent (input : Named) (chart : Chart input)
    (inputCoherent :
      CCL.ProgressiveCoherence.Coherent input.process) :
    CCL.ProgressiveCoherence.Coherent
      (CCL.ComplexLogChart.preparedDenominator input chart.factor
        chart.denominatorApart).process :=
  CCL.ProgressiveCoherence.Coherent.apartify
    (denominatorCoherent input chart inputCoherent) chart.denominatorApart

/-- The actual independently sampled reduced quotient has a finite coherence
certificate obtained by arithmetic closure and its displayed denominator
apartness. -/
def reducedCoherent (input : Named) (chart : Chart input)
    (inputCoherent :
      CCL.ProgressiveCoherence.Coherent input.process) :
    CCL.ProgressiveCoherence.Coherent
      (CCL.ComplexLogChart.reduced input chart.factor
        chart.denominatorApart).process :=
  CCL.ProgressiveCoherence.Coherent.div
    (numeratorCoherent input chart inputCoherent)
    (preparedDenominatorCoherent input chart inputCoherent)
    (CCL.ComplexLogChart.preparedDenominatorApart
      input chart.factor chart.denominatorApart).certificate

private theorem reducedRefine_input_allowances_lt
    (input : Named) (chart : Chart input)
    (inputCoherent :
      CCL.ProgressiveCoherence.Coherent input.process)
    (state : (CCL.ComplexLogChart.reduced input chart.factor
      chart.denominatorApart).process.State)
    (request : RFAP.ConstructiveFraction.Rational)
    (requestPositive : 0 < request)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target)
    (requestSmall :
      request <
        CCL.ProgressiveCoherence.Coherent.divisionOuterTarget
          (CCL.ComplexLogChart.numerator input chart.factor).process
          (CCL.ComplexLogChart.preparedDenominator input
            chart.factor chart.denominatorApart).process
          (CCL.ComplexLogChart.preparedDenominatorApart input
            chart.factor chart.denominatorApart).certificate.lowerSq
          (inputCoherent.accuracyRequest target)) :
    let refined :=
      (CCL.ComplexLogChart.reduced input chart.factor
        chart.denominatorApart).process.refine state request requestPositive
    inputCoherent.allowance refined.1.1.2 < target ∧
      inputCoherent.allowance refined.2.source.1.2 < target := by
  let numerator :=
    CCL.ComplexLogChart.numerator input chart.factor
  let preparedDenominator :=
    CCL.ComplexLogChart.preparedDenominator input chart.factor
      chart.denominatorApart
  let denominatorApart :=
    (CCL.ComplexLogChart.preparedDenominatorApart input
      chart.factor chart.denominatorApart).certificate
  let leftName := CCL.ProgressiveEnclosures.Name.centerOnly
    (numerator.process.ball state.1).center numerator.process.centerBound
      numerator.process.centerBound_nonneg
      (numerator.process.center_bounded state.1)
  let rightName := CCL.ProgressiveEnclosures.Name.centerOnly
    (preparedDenominator.process.ball state.2).center
      preparedDenominator.process.centerBound
      preparedDenominator.process.centerBound_nonneg
      (preparedDenominator.process.center_bounded state.2)
  let divisionInput :=
    CCL.ProgressiveEnclosures.Name.divisionInputTarget
      leftName rightName denominatorApart.lowerSq request
  have divisionInputPositive : 0 < divisionInput :=
    CCL.ProgressiveEnclosures.Name.divisionInputTarget_pos
      leftName rightName denominatorApart.lowerSq denominatorApart.positive
        requestPositive
  have divisionInputSmall :
      divisionInput < inputCoherent.accuracyRequest target :=
    CCL.ProgressiveCoherence.Coherent.processDivisionInputTarget_lt
      leftName rightName rfl rfl denominatorApart.positive requestSmall
  let numeratorAddInput :=
    CCL.ProgressiveEnclosures.Name.additiveInputTarget divisionInput
  have numeratorAddPositive : 0 < numeratorAddInput :=
    CCL.ProgressiveEnclosures.Name.quarter_pos
      divisionInputPositive
  have numeratorAddSmall : numeratorAddInput < divisionInput :=
    CCL.ProgressiveCoherence.Coherent.additiveInputTarget_lt_target
      divisionInputPositive
  let numeratorFactorName :=
    CCL.ProgressiveEnclosures.Name.centerOnly
      ((CCL.ProgressiveEnclosures.Process.exact chart.factor).ball
        state.1.1.1).center
      (CCL.ProgressiveEnclosures.Process.exact
        chart.factor).centerBound
      (CCL.ProgressiveEnclosures.Process.exact
        chart.factor).centerBound_nonneg
      ((CCL.ProgressiveEnclosures.Process.exact
        chart.factor).center_bounded state.1.1.1)
  let numeratorInputName :=
    CCL.ProgressiveEnclosures.Name.centerOnly
      (input.process.ball state.1.1.2).center input.process.centerBound
      input.process.centerBound_nonneg
      (input.process.center_bounded state.1.1.2)
  let numeratorInput :=
    CCL.ProgressiveEnclosures.Name.multiplicativeInputTarget
      numeratorFactorName numeratorInputName numeratorAddInput
  have numeratorInputPositive : 0 < numeratorInput :=
    CCL.ProgressiveEnclosures.Name.multiplicativeInputTarget_pos
      numeratorFactorName numeratorInputName numeratorAddPositive
  have numeratorInputSmall :
      numeratorInput < inputCoherent.accuracyRequest target :=
    (CCL.ProgressiveCoherence.Coherent.processMultiplicativeInputTarget_lt_target
      numeratorFactorName numeratorInputName numeratorAddPositive).trans
        (numeratorAddSmall.trans divisionInputSmall)
  let apartInput := CCL.ProgressiveCharts.commonTarget
    divisionInput (chart.denominatorApart.lowerSq / 12)
  have apartInputPositive : 0 < apartInput :=
    CCL.ProgressiveCharts.commonTarget_pos divisionInputPositive
      chart.denominatorApart.twelfth_pos
  have apartInputSmall : apartInput < divisionInput :=
    CCL.ProgressiveCharts.commonTarget_lt_left
      divisionInputPositive chart.denominatorApart.twelfth_pos
  let denominatorAddInput :=
    CCL.ProgressiveEnclosures.Name.additiveInputTarget apartInput
  have denominatorAddPositive : 0 < denominatorAddInput :=
    CCL.ProgressiveEnclosures.Name.quarter_pos apartInputPositive
  have denominatorAddSmall : denominatorAddInput < apartInput :=
    CCL.ProgressiveCoherence.Coherent.additiveInputTarget_lt_target
      apartInputPositive
  let denominatorFactorName :=
    CCL.ProgressiveEnclosures.Name.centerOnly
      ((CCL.ProgressiveEnclosures.Process.exact chart.factor).ball
        state.2.source.1.1).center
      (CCL.ProgressiveEnclosures.Process.exact
        chart.factor).centerBound
      (CCL.ProgressiveEnclosures.Process.exact
        chart.factor).centerBound_nonneg
      ((CCL.ProgressiveEnclosures.Process.exact
        chart.factor).center_bounded state.2.source.1.1)
  let denominatorInputName :=
    CCL.ProgressiveEnclosures.Name.centerOnly
      (input.process.ball state.2.source.1.2).center input.process.centerBound
      input.process.centerBound_nonneg
      (input.process.center_bounded state.2.source.1.2)
  let denominatorInput :=
    CCL.ProgressiveEnclosures.Name.multiplicativeInputTarget
      denominatorFactorName denominatorInputName denominatorAddInput
  have denominatorInputPositive : 0 < denominatorInput :=
    CCL.ProgressiveEnclosures.Name.multiplicativeInputTarget_pos
      denominatorFactorName denominatorInputName denominatorAddPositive
  have denominatorInputSmall :
      denominatorInput < inputCoherent.accuracyRequest target :=
    (CCL.ProgressiveCoherence.Coherent.processMultiplicativeInputTarget_lt_target
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

private theorem reducedStateAt_input_allowances_lt
    (input : Named) (chart : Chart input)
    (inputCoherent :
      CCL.ProgressiveCoherence.Coherent input.process)
    (start : (CCL.ComplexLogChart.reduced input chart.factor
      chart.denominatorApart).process.State)
    (index : Nat) (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target)
    (requestSmall :
      CCL.ProgressiveSampling.refinementTarget index <
        CCL.ProgressiveCoherence.Coherent.divisionOuterTarget
          (CCL.ComplexLogChart.numerator input chart.factor).process
          (CCL.ComplexLogChart.preparedDenominator input
            chart.factor chart.denominatorApart).process
          (CCL.ComplexLogChart.preparedDenominatorApart input
            chart.factor chart.denominatorApart).certificate.lowerSq
          (inputCoherent.accuracyRequest target)) :
    let state := CCL.ProgressiveSampling.stateAt
      (CCL.ComplexLogChart.reduced input chart.factor
        chart.denominatorApart).process start index
    inputCoherent.allowance state.1.1.2 < target ∧
      inputCoherent.allowance state.2.source.1.2 < target := by
  cases index with
  | zero =>
      exact reducedRefine_input_allowances_lt input chart inputCoherent start
        _ _ target targetPositive requestSmall
  | succ index =>
      exact reducedRefine_input_allowances_lt input chart inputCoherent
        (CCL.ProgressiveSampling.stateAt
          (CCL.ComplexLogChart.reduced input chart.factor
            chart.denominatorApart).process start index)
        _ _ target targetPositive requestSmall

/-- Every finite candidate of the stateful reduced process exposes the two
finite input candidates independently used by its numerator and denominator. -/
theorem reducedPossible_sources (input : Named) (chart : Chart input)
    {state : (CCL.ComplexLogChart.reduced input chart.factor
      chart.denominatorApart).process.State}
    {value : Gaussian}
    (possible :
      (CCL.ComplexLogChart.reduced input chart.factor
        chart.denominatorApart).process.Possible state value) :
    ∃ numeratorSource denominatorSource : Gaussian,
      input.process.Possible state.1.1.2 numeratorSource ∧
      input.process.Possible state.2.source.1.2 denominatorSource ∧
      value = (chart.factor * numeratorSource - 1) /
        (chart.factor * denominatorSource + 1) := by
  rcases possible with
    ⟨numeratorValue, denominatorValue, numeratorPossible,
      denominatorPossible, valueEqual⟩
  rcases CCL.ComplexLogChart.numerator_possible
      input chart.factor numeratorPossible with
    ⟨numeratorSource, numeratorSourcePossible, numeratorEqual⟩
  rcases CCL.ComplexLogChart.denominator_possible
      input chart.factor denominatorPossible with
    ⟨denominatorSource, denominatorSourcePossible, denominatorEqual⟩
  exact ⟨numeratorSource, denominatorSource, numeratorSourcePossible,
    denominatorSourcePossible, by
      rw [valueEqual, numeratorEqual, denominatorEqual]⟩

/-! ## Synchronized finite chart input -/

/-- The input state reached as a component of the one finite denominator
preparation performed by a complex-log chart.  Exposing this state lets the
numerator and denominator of a reference quotient read the same finite input
candidate. -/
def preparedChartInput (input : Named) (chart : Chart input) : Named :=
  { process := input.process
    state :=
      (CCL.ProgressiveCharts.prepareApartState
        chart.denominatorApart
        (CCL.ComplexLogChart.denominator
          input chart.factor).state).source.1.2 }

/-- Every candidate at the input component selected during denominator
preparation is still a candidate at the original input state. -/
theorem preparedChartInput_possible_original (input : Named)
    (chart : Chart input) (certificate : BranchCertificate input chart)
    {value : Gaussian}
    (possible : (preparedChartInput input chart).process.Possible
      (preparedChartInput input chart).state value) :
    input.process.Possible input.state value := by
  let prepared := CCL.ProgressiveCharts.prepareApartState
    chart.denominatorApart
    (CCL.ComplexLogChart.denominator
      input chart.factor).state
  have preparedDenominatorPossible :
      (CCL.ComplexLogChart.denominator
        input chart.factor).process.Possible prepared.source
          (chart.factor * value + 1) := by
    exact ⟨chart.factor * value, 1,
      ⟨chart.factor, value, rfl, possible, rfl⟩, rfl, rfl⟩
  have originalDenominatorPossible :=
    CCL.ProgressiveCharts.prepareApartState_persists
      chart.denominatorApart
      (CCL.ComplexLogChart.denominator
        input chart.factor).state preparedDenominatorPossible
  rcases CCL.ComplexLogChart.denominator_possible
      input chart.factor originalDenominatorPossible with
    ⟨source, sourcePossible, equality⟩
  have scaledEquality : chart.factor * source = chart.factor * value := by
    calc
      chart.factor * source =
          (chart.factor * source + 1) - 1 := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.one_re,
            RFAP.ConstructiveGaussian.Gaussian.one_im] <;> ring1
      _ = (chart.factor * value + 1) - 1 := by rw [equality]
      _ = chart.factor * value := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.one_re,
            RFAP.ConstructiveGaussian.Gaussian.one_im] <;> ring1
  have sourceEqual : source = value := by
    apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
      certificate.factor_ne_zero
    calc
      source * chart.factor = chart.factor * source :=
        RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
      _ = chart.factor * value := scaledEquality
      _ = value * chart.factor :=
        RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
  change input.process.Possible input.state source at sourcePossible
  rw [← sourceEqual]
  exact sourcePossible

/-- The synchronized rational reduced coordinate read from one prepared input
candidate. -/
def synchronizedReducedValue (input : Named) (chart : Chart input)
    (value : Gaussian) : Gaussian :=
  (chart.factor * value - 1) / (chart.factor * value + 1)

theorem preparedChartInput_denominator_lower (input : Named)
    (chart : Chart input) (certificate : BranchCertificate input chart)
    {value : Gaussian}
    (possible : (preparedChartInput input chart).process.Possible
      (preparedChartInput input chart).state value) :
    chart.denominatorApart.lowerSq ≤ normSq (chart.factor * value + 1) := by
  have originalPossible :=
    preparedChartInput_possible_original input chart certificate possible
  apply chart.denominatorApart.lower
    (CCL.ComplexLogChart.denominator input chart.factor).state
  exact ⟨chart.factor * value, 1,
    ⟨chart.factor, value, rfl, originalPossible, rfl⟩, rfl, rfl⟩

theorem preparedChartInput_denominator_ne_zero (input : Named)
    (chart : Chart input) (certificate : BranchCertificate input chart)
    {value : Gaussian}
    (possible : (preparedChartInput input chart).process.Possible
      (preparedChartInput input chart).state value) :
    chart.factor * value + 1 ≠ 0 := by
  have lower :=
    preparedChartInput_denominator_lower input chart certificate possible
  intro equal
  rw [equal, normSq_zero] at lower
  exact (not_le_of_gt chart.denominatorApart.positive) lower

/-- Using one prepared input candidate for both numerator and denominator is
admitted by the original stateful quotient. -/
theorem synchronizedReducedValue_possible (input : Named)
    (chart : Chart input) (certificate : BranchCertificate input chart)
    {value : Gaussian}
    (possible : (preparedChartInput input chart).process.Possible
      (preparedChartInput input chart).state value) :
    (CCL.ComplexLogChart.reduced input chart.factor
      chart.denominatorApart).process.Possible
        (CCL.ComplexLogChart.reduced input chart.factor
          chart.denominatorApart).state
        (synchronizedReducedValue input chart value) := by
  have originalPossible :=
    preparedChartInput_possible_original input chart certificate possible
  have numeratorPossible :
      (CCL.ComplexLogChart.numerator
        input chart.factor).process.Possible
          (CCL.ComplexLogChart.numerator
            input chart.factor).state
          (chart.factor * value - 1) := by
    refine ⟨chart.factor * value, -1,
      ⟨chart.factor, value, rfl, originalPossible, rfl⟩,
      ⟨1, rfl, rfl⟩, ?_⟩
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.neg_re,
        RFAP.ConstructiveGaussian.Gaussian.neg_im,
        RFAP.ConstructiveGaussian.Gaussian.one_re,
        RFAP.ConstructiveGaussian.Gaussian.one_im] <;> ring1
  have denominatorPossible :
      (CCL.ComplexLogChart.preparedDenominator
        input chart.factor chart.denominatorApart).process.Possible
          (CCL.ComplexLogChart.preparedDenominator
            input chart.factor chart.denominatorApart).state
          (chart.factor * value + 1) := by
    exact ⟨chart.factor * value, 1,
      ⟨chart.factor, value, rfl, possible, rfl⟩, rfl, rfl⟩
  exact ⟨chart.factor * value - 1, chart.factor * value + 1,
    numeratorPossible, denominatorPossible, rfl⟩

/-- The diagonal finite reduced-coordinate sampler. -/
def synchronizedReducedSample (input : Named) (chart : Chart input)
    (index : Nat) : Gaussian :=
  synchronizedReducedValue input chart
    (CCL.ProgressiveComplexLog.inputSample
      (preparedChartInput input chart) index)

theorem synchronizedReducedSample_disk (input : Named)
    (chart : Chart input) (certificate : BranchCertificate input chart)
    (index : Nat) :
    normSq (synchronizedReducedSample input chart index) ≤ 1 / 9 := by
  apply chart.reducedDisk.possible_normSq
  apply synchronizedReducedValue_possible input chart certificate
  exact CCL.ProgressiveComplexLog.inputSample_possible_start
    (preparedChartInput input chart) index

def synchronizedReducedSensitivity (input : Named) (chart : Chart input) :
    RFAP.ConstructiveFraction.Rational :=
  (4 * normSq chart.factor) /
    (chart.denominatorApart.lowerSq * chart.denominatorApart.lowerSq)

theorem synchronizedReducedSensitivity_nonneg (input : Named)
    (chart : Chart input) :
    0 ≤ synchronizedReducedSensitivity input chart := by
  apply RFAP.ConstructiveFraction.div_nonneg_direct
  · exact RFAP.ConstructiveFraction.mul_nonneg_direct
      (by decide) (normSq_nonneg chart.factor)
  · exact RFAP.ConstructiveFraction.mul_nonneg_direct
      chart.denominatorApart.positive.le chart.denominatorApart.positive.le

def synchronizedReducedErrorScale (input : Named) (chart : Chart input) :
    RFAP.ConstructiveFraction.Rational :=
  synchronizedReducedSensitivity input chart * 4

theorem synchronizedReducedErrorScale_nonneg (input : Named)
    (chart : Chart input) :
    0 ≤ synchronizedReducedErrorScale input chart :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (synchronizedReducedSensitivity_nonneg input chart) (by decide)

theorem synchronizedReducedErrorScale_pos (input : Named)
    (chart : Chart input) (certificate : BranchCertificate input chart) :
    0 < synchronizedReducedErrorScale input chart := by
  have factorPositive : 0 < normSq chart.factor :=
    normSq_pos certificate.factor_ne_zero
  have numeratorPositive : 0 < 4 * normSq chart.factor :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) factorPositive
  have denominatorPositive :
      0 < chart.denominatorApart.lowerSq *
        chart.denominatorApart.lowerSq :=
    RFAP.ConstructiveFraction.mul_pos_direct
      chart.denominatorApart.positive chart.denominatorApart.positive
  unfold synchronizedReducedErrorScale synchronizedReducedSensitivity
  exact RFAP.ConstructiveFraction.mul_pos_direct
    (RFAP.ConstructiveFraction.div_pos_direct numeratorPositive
      denominatorPositive) (by decide)

theorem synchronizedReducedSample_later_close (input : Named)
    (chart : Chart input) (certificate : BranchCertificate input chart)
    {oldIndex newIndex : Nat} (order : oldIndex ≤ newIndex) :
    normSq
        (synchronizedReducedSample input chart newIndex -
          synchronizedReducedSample input chart oldIndex) ≤
      CCL.FiniteGeometric.quarterRadius
        (synchronizedReducedErrorScale input chart) oldIndex := by
  let newValue := CCL.ProgressiveComplexLog.inputSample
    (preparedChartInput input chart) newIndex
  let oldValue := CCL.ProgressiveComplexLog.inputSample
    (preparedChartInput input chart) oldIndex
  have newPossible :=
    CCL.ProgressiveComplexLog.inputSample_possible_start
      (preparedChartInput input chart) newIndex
  have oldPossible :=
    CCL.ProgressiveComplexLog.inputSample_possible_start
      (preparedChartInput input chart) oldIndex
  have newLower := preparedChartInput_denominator_lower input chart
    certificate newPossible
  have oldLower := preparedChartInput_denominator_lower input chart
    certificate oldPossible
  have sensitivity :=
    CCL.FinitePolynomial.scaledReduced_input_close
      chart.factor newValue oldValue chart.denominatorApart.lowerSq
      chart.denominatorApart.positive newLower oldLower
  have movement :=
    CCL.ProgressiveComplexLog.inputSample_later_close
      (preparedChartInput input chart) order
  change normSq
      (synchronizedReducedValue input chart newValue -
        synchronizedReducedValue input chart oldValue) ≤ _
  calc
    normSq
        (synchronizedReducedValue input chart newValue -
          synchronizedReducedValue input chart oldValue) ≤
        synchronizedReducedSensitivity input chart *
          normSq (newValue - oldValue) := by
      exact sensitivity
    _ ≤ synchronizedReducedSensitivity input chart *
        CCL.FiniteGeometric.quarterRadius 4 oldIndex :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct movement
        (synchronizedReducedSensitivity_nonneg input chart)
    _ = CCL.FiniteGeometric.quarterRadius
          (synchronizedReducedErrorScale input chart) oldIndex := by
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
      unfold synchronizedReducedErrorScale
      ring1

/-- A limit-free synchronized reduced-coordinate reference. -/
def synchronizedReducedApproximation (input : Named) (chart : Chart input)
    (certificate : BranchCertificate input chart) : Approximation where
  sample := synchronizedReducedSample input chart
  radiusSq := CCL.FiniteGeometric.quarterRadius
    (synchronizedReducedErrorScale input chart)
  radiusSq_nonneg index :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      (synchronizedReducedErrorScale_nonneg input chart) index
  later_close := synchronizedReducedSample_later_close input chart certificate
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow
      (synchronizedReducedErrorScale input chart) current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge
      (synchronizedReducedErrorScale input chart) current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate
      (synchronizedReducedErrorScale input chart)
      (synchronizedReducedErrorScale_nonneg input chart)
  centerBound := 1 / 9
  centerBound_nonneg := by decide
  sample_bounded := synchronizedReducedSample_disk input chart certificate

def synchronizedReducedNamed (input : Named) (chart : Chart input)
    (certificate : BranchCertificate input chart) : Named :=
  (synchronizedReducedApproximation input chart certificate).toNamed

/-- A fixed finite quadrance bound for a synchronized input witness once its
coherence allowance is below one. -/
def reducedBridgeSourceBound (input : Named) :
    RFAP.ConstructiveFraction.Rational :=
  2 * (1 + input.process.centerBound)

theorem reducedBridgeSourceBound_pos (input : Named) :
    0 < reducedBridgeSourceBound input :=
  RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (add_pos_of_pos_of_nonneg (by decide) input.process.centerBound_nonneg)

/-- The displayed coefficient in the asynchronous reduced-coordinate
sensitivity estimate, specialized to the fixed finite source bound above. -/
def reducedBridgeSensitivity (input : Named) (chart : Chart input) :
    RFAP.ConstructiveFraction.Rational :=
  (4 *
      (normSq chart.factor * normSq chart.factor *
          reducedBridgeSourceBound input + normSq chart.factor)) /
    (chart.denominatorApart.lowerSq * chart.denominatorApart.lowerSq)

theorem reducedBridgeSensitivity_pos (input : Named) (chart : Chart input)
    (certificate : BranchCertificate input chart) :
    0 < reducedBridgeSensitivity input chart := by
  have factorPositive : 0 < normSq chart.factor :=
    normSq_pos certificate.factor_ne_zero
  have squareSourceNonnegative :
      0 ≤ normSq chart.factor * normSq chart.factor *
        reducedBridgeSourceBound input :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (normSq_nonneg chart.factor) (normSq_nonneg chart.factor))
      (reducedBridgeSourceBound_pos input).le
  have sumPositive :
      0 < normSq chart.factor * normSq chart.factor *
          reducedBridgeSourceBound input + normSq chart.factor :=
    add_pos_of_nonneg_of_pos squareSourceNonnegative factorPositive
  unfold reducedBridgeSensitivity
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide) sumPositive)
    (RFAP.ConstructiveFraction.mul_pos_direct
      chart.denominatorApart.positive chart.denominatorApart.positive)

def reducedBridgeCoefficient (input : Named) (chart : Chart input) :
    RFAP.ConstructiveFraction.Rational :=
  16 * reducedBridgeSensitivity input chart

theorem reducedBridgeCoefficient_pos (input : Named) (chart : Chart input)
    (certificate : BranchCertificate input chart) :
    0 < reducedBridgeCoefficient input chart :=
  RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (reducedBridgeSensitivity_pos input chart certificate)

/-- A positive finite input-coherence budget whose displayed bridge
coefficient consumes strictly less than the requested final tolerance. -/
def reducedBridgeTarget (input : Named) (chart : Chart input)
    (target : RFAP.ConstructiveFraction.Rational) :
    RFAP.ConstructiveFraction.Rational :=
  target / (target + reducedBridgeCoefficient input chart)

theorem reducedBridgeTarget_pos (input : Named) (chart : Chart input)
    (certificate : BranchCertificate input chart)
    {target : RFAP.ConstructiveFraction.Rational} (positive : 0 < target) :
    0 < reducedBridgeTarget input chart target :=
  RFAP.ConstructiveFraction.div_pos_direct positive
    (add_pos positive
      (reducedBridgeCoefficient_pos input chart certificate))

theorem reducedBridgeTarget_lt_one (input : Named) (chart : Chart input)
    (certificate : BranchCertificate input chart)
    {target : RFAP.ConstructiveFraction.Rational} (positive : 0 < target) :
    reducedBridgeTarget input chart target < 1 := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (add_pos positive
      (reducedBridgeCoefficient_pos input chart certificate))).2
  calc
    target < target + reducedBridgeCoefficient input chart :=
      lt_add_of_pos_right target
        (reducedBridgeCoefficient_pos input chart certificate)
    _ = 1 * (target + reducedBridgeCoefficient input chart) := by ring1

theorem reducedBridgeTarget_budget_lt (input : Named) (chart : Chart input)
    (certificate : BranchCertificate input chart)
    {target : RFAP.ConstructiveFraction.Rational} (positive : 0 < target) :
    reducedBridgeTarget input chart target *
        reducedBridgeCoefficient input chart < target := by
  have denominatorPositive :
      0 < target + reducedBridgeCoefficient input chart :=
    add_pos positive (reducedBridgeCoefficient_pos input chart certificate)
  change target / (target + reducedBridgeCoefficient input chart) *
      reducedBridgeCoefficient input chart < target
  calc
    target / (target + reducedBridgeCoefficient input chart) *
        reducedBridgeCoefficient input chart =
      (target * reducedBridgeCoefficient input chart) /
        (target + reducedBridgeCoefficient input chart) := by
      change (target *
          (target + reducedBridgeCoefficient input chart)⁻¹) *
            reducedBridgeCoefficient input chart =
        (target * reducedBridgeCoefficient input chart) *
          (target + reducedBridgeCoefficient input chart)⁻¹
      calc
        (target * (target + reducedBridgeCoefficient input chart)⁻¹) *
            reducedBridgeCoefficient input chart =
          target * ((target + reducedBridgeCoefficient input chart)⁻¹ *
            reducedBridgeCoefficient input chart) :=
              RFAP.ConstructiveFraction.mul_assoc _ _ _
        _ = target * (reducedBridgeCoefficient input chart *
            (target + reducedBridgeCoefficient input chart)⁻¹) := by
          rw [RFAP.ConstructiveFraction.mul_comm
            (target + reducedBridgeCoefficient input chart)⁻¹]
        _ = (target * reducedBridgeCoefficient input chart) *
            (target + reducedBridgeCoefficient input chart)⁻¹ :=
          (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm
    _ < target := by
      apply (RFAP.ConstructiveFraction.div_lt_iff_pos
        denominatorPositive).2
      have coefficientLt : reducedBridgeCoefficient input chart <
          target + reducedBridgeCoefficient input chart := by
        calc
          reducedBridgeCoefficient input chart =
              0 + reducedBridgeCoefficient input chart :=
            by ring1
          _ < target + reducedBridgeCoefficient input chart :=
            RFAP.ConstructiveFraction.add_lt_add_right_direct positive _
      exact RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        positive coefficientLt

/-- The source-sample index selected by one finite sampling request to the
productive synchronized reference wrapper. -/
def synchronizedReducedSourceIndex (input : Named) (chart : Chart input)
    (certificate : BranchCertificate input chart) (outputIndex : Nat) : Nat :=
  CCL.OperationalEquivalence.emittedSampleIndex
    (synchronizedReducedApproximation input chart certificate) outputIndex

/-- One bounded scan computing an output index whose productive wrapper has
reached a requested finite source index. -/
def synchronizedReducedOutputIndexForSource (input : Named)
    (chart : Chart input) (current requestedSource : Nat) : Nat :=
  CCL.FiniteGeometric.firstQuarterBelow 1 current
    (CCL.FiniteGeometric.quarterRadius
      (synchronizedReducedErrorScale input chart) requestedSource)

theorem synchronizedReducedOutputIndexForSource_ge (input : Named)
    (chart : Chart input) (current requestedSource : Nat) :
    current ≤ synchronizedReducedOutputIndexForSource
      input chart current requestedSource :=
  CCL.FiniteGeometric.firstQuarterBelow_ge 1 current _

private theorem quarterRadius_index_antitone
    {scale : RFAP.ConstructiveFraction.Rational}
    (scaleNonnegative : 0 ≤ scale) {earlier later : Nat}
    (order : earlier ≤ later) :
    CCL.FiniteGeometric.quarterRadius scale later ≤
      CCL.FiniteGeometric.quarterRadius scale earlier := by
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    (CCL.FinitePolynomial.quarterPower_antitone order)
    scaleNonnegative

/-- The bounded scan really reaches the requested finite source index. -/
theorem synchronizedReduced_reachesRequestedSourceIndex (input : Named)
    (chart : Chart input) (certificate : BranchCertificate input chart)
    (current requestedSource : Nat) :
    requestedSource ≤ synchronizedReducedSourceIndex input chart certificate
      (synchronizedReducedOutputIndexForSource input chart
        current requestedSource) := by
  let approximation := synchronizedReducedApproximation input chart certificate
  let outputIndex := synchronizedReducedOutputIndexForSource
    input chart current requestedSource
  let sourceIndex := synchronizedReducedSourceIndex
    input chart certificate outputIndex
  have sourceRadius :
      CCL.FiniteGeometric.quarterRadius
          (synchronizedReducedErrorScale input chart) sourceIndex <
        CCL.ProgressiveSampling.refinementTarget outputIndex := by
    exact CCL.ProgressiveSampling.stateAt_accurate
      approximation.toProcess
        (show approximation.toProcess.State from (0 : Nat)) outputIndex
  have outputSmall :
      CCL.ProgressiveSampling.refinementTarget outputIndex <
        CCL.FiniteGeometric.quarterRadius
          (synchronizedReducedErrorScale input chart) requestedSource := by
    exact CCL.FiniteGeometric.firstQuarterBelow_accurate
      1 (by decide) current
      (CCL.FiniteGeometric.quarterRadius
        (synchronizedReducedErrorScale input chart) requestedSource)
      (CCL.FiniteGeometric.quarterRadius_pos
        (synchronizedReducedErrorScale_pos input chart certificate)
        requestedSource)
  have sourceSmall :
      CCL.FiniteGeometric.quarterRadius
          (synchronizedReducedErrorScale input chart) sourceIndex <
        CCL.FiniteGeometric.quarterRadius
          (synchronizedReducedErrorScale input chart) requestedSource :=
    sourceRadius.trans outputSmall
  by_contra notReached
  have sourceBefore : sourceIndex ≤ requestedSource :=
    Nat.le_of_lt (Nat.lt_of_not_ge notReached)
  have reverseBound := quarterRadius_index_antitone
    (synchronizedReducedErrorScale_nonneg input chart) sourceBefore
  exact (not_lt_of_ge reverseBound) sourceSmall

/-- The original stateful quotient, whose numerator and denominator may
refine the input independently, is operationally equal to the diagonal
synchronized quotient.  For each displayed tolerance this comparison
computes two finite indices and applies the explicit asynchronous rational
sensitivity estimate to three finite input witnesses. -/
def reduced_equivalent_synchronizedReduced (input : Named)
    (chart : Chart input) (certificate : BranchCertificate input chart)
    (inputCoherent :
      CCL.ProgressiveCoherence.Coherent input.process) :
    NamedEquivalent
      (CCL.ComplexLogChart.reduced input chart.factor
        chart.denominatorApart)
      (synchronizedReducedNamed input chart certificate) where
  compare := by
    intro leftStart rightStart target positive
    let semanticTarget := reducedBridgeTarget input chart target
    have semanticPositive : 0 < semanticTarget :=
      reducedBridgeTarget_pos input chart certificate positive
    have semanticLtOne : semanticTarget < 1 :=
      reducedBridgeTarget_lt_one input chart certificate positive
    let inputRequest := inputCoherent.accuracyRequest semanticTarget
    have inputRequestPositive : 0 < inputRequest :=
      inputCoherent.accuracyRequest_pos semanticPositive
    let numerator :=
      CCL.ComplexLogChart.numerator input chart.factor
    let preparedDenominator :=
      CCL.ComplexLogChart.preparedDenominator input chart.factor
        chart.denominatorApart
    let denominatorApart :=
      (CCL.ComplexLogChart.preparedDenominatorApart input
        chart.factor chart.denominatorApart).certificate
    let outerTarget :=
      CCL.ProgressiveCoherence.Coherent.divisionOuterTarget
        numerator.process preparedDenominator.process denominatorApart.lowerSq
          inputRequest
    have outerPositive : 0 < outerTarget :=
      CCL.ProgressiveCoherence.Coherent.divisionOuterTarget_pos
        numerator.process preparedDenominator.process denominatorApart.positive
          inputRequestPositive
    let leftIndex := CCL.FiniteGeometric.firstQuarterBelow
      1 leftStart outerTarget
    have leftIndexGe : leftStart ≤ leftIndex :=
      CCL.FiniteGeometric.firstQuarterBelow_ge
        1 leftStart outerTarget
    have leftRequestSmall :
        CCL.ProgressiveSampling.refinementTarget leftIndex <
          outerTarget :=
      CCL.FiniteGeometric.firstQuarterBelow_accurate
        1 (by decide) leftStart outerTarget outerPositive
    let requestedSource := CCL.FiniteGeometric.firstQuarterBelow
      1 0 inputRequest
    have requestedSourceRequestSmall :
        CCL.ProgressiveSampling.refinementTarget requestedSource <
          inputRequest :=
      CCL.FiniteGeometric.firstQuarterBelow_accurate
        1 (by decide) 0 inputRequest inputRequestPositive
    let rightIndex := synchronizedReducedOutputIndexForSource
      input chart rightStart requestedSource
    exact
      { leftIndex := leftIndex
        rightIndex := rightIndex
        left_ge := leftIndexGe
        right_ge := synchronizedReducedOutputIndexForSource_ge
          input chart rightStart requestedSource
        close := by
          intro leftLater rightLater leftOrder rightOrder
          let reduced := CCL.ComplexLogChart.reduced input
            chart.factor chart.denominatorApart
          let actualState := CCL.ProgressiveSampling.stateAt
            reduced.process reduced.state leftLater
          let actualValue := CCL.ProgressiveSampling.witnessAt
            reduced.process reduced.state leftLater
          have actualPossible : reduced.process.Possible actualState actualValue :=
            CCL.ProgressiveSampling.witnessAt_possible
              reduced.process reduced.state leftLater
          rcases reducedPossible_sources input chart actualPossible with
            ⟨x, y, xPossible, yPossible, actualEqual⟩
          have actualRequestSmall :
              CCL.ProgressiveSampling.refinementTarget leftLater <
                outerTarget :=
            (quarterRadius_index_antitone (by decide) leftOrder).trans_lt
              leftRequestSmall
          have actualAllowancesSmall :=
            reducedStateAt_input_allowances_lt input chart inputCoherent
              reduced.state leftLater semanticTarget semanticPositive
                actualRequestSmall
          let sourceIndex := synchronizedReducedSourceIndex input chart
            certificate rightLater
          have sourceOrder : requestedSource ≤ sourceIndex :=
            (synchronizedReduced_reachesRequestedSourceIndex input chart
              certificate rightStart requestedSource).trans
              (CCL.OperationalEquivalence.emittedSampleIndex_mono
                (synchronizedReducedApproximation input chart certificate)
                rightOrder)
          have sourceRequestSmall :
              CCL.ProgressiveSampling.refinementTarget sourceIndex <
                inputRequest :=
            (quarterRadius_index_antitone (by decide) sourceOrder).trans_lt
              requestedSourceRequestSmall
          let prepared := preparedChartInput input chart
          let z := CCL.ProgressiveComplexLog.inputSample
            prepared sourceIndex
          have zPossible : input.process.Possible
              (CCL.ProgressiveSampling.stateAt input.process
                prepared.state sourceIndex) z :=
            CCL.ProgressiveSampling.witnessAt_possible
              input.process prepared.state sourceIndex
          have zPossibleStart : input.process.Possible prepared.state z :=
            CCL.ProgressiveComplexLog.inputSample_possible_start
              prepared sourceIndex
          have zAllowanceSmall :
              inputCoherent.allowance
                  (CCL.ProgressiveSampling.stateAt input.process
                    prepared.state sourceIndex) < semanticTarget :=
            CCL.ProgressiveCoherence.Coherent.stateAt_allowance_lt
              inputCoherent prepared.state sourceIndex semanticTarget
                semanticPositive sourceRequestSmall
          have xClose := inputCoherent.possible_close xPossible zPossible
          have yClose := inputCoherent.possible_close yPossible zPossible
          have xDistanceSmall : normSq (x - z) < 8 * semanticTarget := by
            calc
              normSq (x - z) ≤
                  4 * (inputCoherent.allowance actualState.1.1.2 +
                    inputCoherent.allowance
                      (CCL.ProgressiveSampling.stateAt
                        input.process prepared.state sourceIndex)) := xClose
              _ < 4 * (semanticTarget + semanticTarget) :=
                RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                  (by decide)
                  (RFAP.ConstructiveFraction.add_lt_add_direct
                    actualAllowancesSmall.1 zAllowanceSmall)
              _ = 8 * semanticTarget := by ring1
          have yDistanceSmall : normSq (y - z) < 8 * semanticTarget := by
            calc
              normSq (y - z) ≤
                  4 * (inputCoherent.allowance actualState.2.source.1.2 +
                    inputCoherent.allowance
                      (CCL.ProgressiveSampling.stateAt
                        input.process prepared.state sourceIndex)) := yClose
              _ < 4 * (semanticTarget + semanticTarget) :=
                RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                  (by decide)
                  (RFAP.ConstructiveFraction.add_lt_add_direct
                    actualAllowancesSmall.2 zAllowanceSmall)
              _ = 8 * semanticTarget := by ring1
          have distanceSmall :
              normSq (x - z) + normSq (y - z) < 16 * semanticTarget := by
            calc
              normSq (x - z) + normSq (y - z) <
                  8 * semanticTarget + 8 * semanticTarget :=
                RFAP.ConstructiveFraction.add_lt_add_direct
                  xDistanceSmall yDistanceSmall
              _ = 16 * semanticTarget := by ring1
          have yDenominatorPossible :
              (CCL.ComplexLogChart.denominator input
                chart.factor).process.Possible actualState.2.source
                  (chart.factor * y + 1) :=
            ⟨chart.factor * y, 1,
              ⟨chart.factor, y, rfl, yPossible, rfl⟩, rfl, rfl⟩
          have yLower : chart.denominatorApart.lowerSq ≤
              normSq (chart.factor * y + 1) :=
            chart.denominatorApart.lower actualState.2.source
              yDenominatorPossible
          have zLower : chart.denominatorApart.lowerSq ≤
              normSq (chart.factor * z + 1) :=
            preparedChartInput_denominator_lower input chart certificate
              zPossibleStart
          have zAllowanceLtOne :
              inputCoherent.allowance
                  (CCL.ProgressiveSampling.stateAt input.process
                    prepared.state sourceIndex) < 1 :=
            zAllowanceSmall.trans semanticLtOne
          have allowancePlusBound :
              inputCoherent.allowance
                    (CCL.ProgressiveSampling.stateAt input.process
                      prepared.state sourceIndex) + input.process.centerBound <
                1 + input.process.centerBound :=
            RFAP.ConstructiveFraction.add_lt_add_right_direct
              zAllowanceLtOne input.process.centerBound
          have zBound : normSq z ≤ reducedBridgeSourceBound input := by
            have possibleBound :=
              CCL.ProgressiveCoherence.Coherent.possible_normSq_le
                inputCoherent zPossible
            exact (possibleBound.trans_lt
              (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide) allowancePlusBound)).le
          have asynchronous :=
            CCL.FinitePolynomial.asynchronousScaledReduced_input_close
              chart.factor x y z chart.denominatorApart.lowerSq
                (reducedBridgeSourceBound input)
                chart.denominatorApart.positive yLower zLower zBound
          have referenceSample :
              (CCL.ProgressiveSampling.approximation
                (synchronizedReducedNamed input chart certificate)).sample
                  rightLater =
                synchronizedReducedSample input chart sourceIndex := by
            change
              (CCL.ProgressiveSampling.approximation
                (synchronizedReducedApproximation input chart
                  certificate).toNamed).sample rightLater =
                (synchronizedReducedApproximation input chart
                  certificate).sample
                    (CCL.OperationalEquivalence.emittedSampleIndex
                      (synchronizedReducedApproximation input chart
                        certificate) rightLater)
            exact CCL.OperationalEquivalence.emittedSample_eq
              (synchronizedReducedApproximation input chart certificate)
                rightLater
          change normSq
              (actualValue -
                (CCL.ProgressiveSampling.approximation
                  (synchronizedReducedNamed input chart certificate)).sample
                    rightLater) < target
          rw [referenceSample]
          change normSq
              (actualValue -
                (chart.factor * z - 1) / (chart.factor * z + 1)) < target
          rw [actualEqual]
          calc
            normSq
                ((chart.factor * x - 1) / (chart.factor * y + 1) -
                  (chart.factor * z - 1) / (chart.factor * z + 1)) ≤
              reducedBridgeSensitivity input chart *
                (normSq (x - z) + normSq (y - z)) := by
              simpa only [reducedBridgeSensitivity] using asynchronous
            _ < reducedBridgeSensitivity input chart *
                (16 * semanticTarget) :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (reducedBridgeSensitivity_pos input chart certificate)
                distanceSmall
            _ = semanticTarget * reducedBridgeCoefficient input chart := by
              unfold reducedBridgeCoefficient
              ring1
            _ < target :=
              reducedBridgeTarget_budget_lt input chart certificate positive }

theorem synchronizedReducedDisk (input : Named) (chart : Chart input)
    (certificate : BranchCertificate input chart) :
    CCL.ProgressiveComplexLog.Disk
      (synchronizedReducedNamed input chart certificate) where
  possible_normSq := by
    intro value possible
    rcases possible with ⟨later, _order, rfl⟩
    exact synchronizedReducedSample_disk input chart certificate later

/-- Exact finite reconstruction of every synchronized reduced sample. -/
theorem synchronizedReducedSample_reconstructs (input : Named)
    (chart : Chart input) (certificate : BranchCertificate input chart)
    (index : Nat) :
    ((1 + synchronizedReducedSample input chart index) /
        (1 - synchronizedReducedSample input chart index)) *
          (1 / chart.factor) =
      CCL.ProgressiveComplexLog.inputSample
        (preparedChartInput input chart) index := by
  let value := CCL.ProgressiveComplexLog.inputSample
    (preparedChartInput input chart) index
  have possible :=
    CCL.ProgressiveComplexLog.inputSample_possible_start
      (preparedChartInput input chart) index
  have denominatorNonzero :=
    preparedChartInput_denominator_ne_zero input chart certificate possible
  have reducedBound :=
    synchronizedReducedSample_disk input chart certificate index
  have chartIdentity := CCL.FinitePolynomial.scaledReduced_chart
    chart.factor value denominatorNonzero reducedBound
  change ((1 + synchronizedReducedValue input chart value) /
      (1 - synchronizedReducedValue input chart value)) *
        (1 / chart.factor) = value
  unfold synchronizedReducedValue
  rw [chartIdentity, RFAP.ExplicitField.div_eq_mul_inv]
  calc
    chart.factor * value * (1 * chart.factor⁻¹) =
        value * (chart.factor * chart.factor⁻¹) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.one_mul,
        RFAP.ConstructiveGaussian.Gaussian.mul_comm chart.factor value,
        RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
    _ = value * 1 := by
      rw [show chart.factor * chart.factor⁻¹ = 1 by
        simpa only [RFAP.ConstructiveGaussian.Gaussian.inv_eq] using
          RFAP.ConstructiveGaussian.Gaussian.mul_inv chart.factor
            certificate.factor_ne_zero]
    _ = value := RFAP.ConstructiveGaussian.Gaussian.mul_one value

theorem synchronizedReducedNamed_inputSample (input : Named)
    (chart : Chart input) (certificate : BranchCertificate input chart)
    (index : Nat) :
    CCL.ProgressiveComplexLog.inputSample
        (synchronizedReducedNamed input chart certificate) index =
      synchronizedReducedSample input chart
        (synchronizedReducedSourceIndex input chart certificate index) := by
  change
    (CCL.ProgressiveSampling.approximation
      (synchronizedReducedApproximation input chart certificate).toNamed).sample
        index =
      (synchronizedReducedApproximation input chart certificate).sample
        (CCL.OperationalEquivalence.emittedSampleIndex
          (synchronizedReducedApproximation input chart certificate) index)
  exact CCL.OperationalEquivalence.emittedSample_eq
    (synchronizedReducedApproximation input chart certificate) index

/-- Every raw sample of the scaled reconstruction of the productive
synchronized reference is exactly a finite prepared-input sample. -/
theorem synchronizedScaledChartSample_reconstructs (input : Named)
    (chart : Chart input) (certificate : BranchCertificate input chart)
    (index : Nat) :
    (CCL.TranscendentalCoherence.scaledDynamicLocalExpLogChartApproximation
        (synchronizedReducedNamed input chart certificate)
        (synchronizedReducedDisk input chart certificate)
        (1 / chart.factor)).sample index =
      CCL.ProgressiveComplexLog.inputSample
        (preparedChartInput input chart)
        (synchronizedReducedSourceIndex input chart certificate index) := by
  change
    ((1 + CCL.ProgressiveComplexLog.inputSample
        (synchronizedReducedNamed input chart certificate) index) /
      (1 - CCL.ProgressiveComplexLog.inputSample
        (synchronizedReducedNamed input chart certificate) index)) *
        (1 / chart.factor) = _
  rw [synchronizedReducedNamed_inputSample input chart certificate index]
  exact synchronizedReducedSample_reconstructs input chart certificate
    (synchronizedReducedSourceIndex input chart certificate index)

private theorem two_quarter_sums
    (target : RFAP.ConstructiveFraction.Rational) :
    2 * (target / 4 + target / 4) = target := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (show (4 : RFAP.ConstructiveFraction.Rational) ≠ 0 by decide)
  calc
    (2 * (target / 4 + target / 4)) * 4 =
        2 * ((target / 4) * 4 + (target / 4) * 4) := by ring1
    _ = 2 * (target + target) := by
      rw [show target / 4 * 4 = target from
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 4 (by decide)]
    _ = target * 4 := by ring1

/-- The scaled chart reconstruction is operationally the canonical finite
sampler of the prepared input state.  The comparison computes only finite
indices and uses the explicit source-index reachability theorem above. -/
def synchronizedScaledChartEquivalentPreparedSampling (input : Named)
    (chart : Chart input) (certificate : BranchCertificate input chart) :
    Equivalent
      (CCL.TranscendentalCoherence.scaledDynamicLocalExpLogChartApproximation
        (synchronizedReducedNamed input chart certificate)
        (synchronizedReducedDisk input chart certificate)
        (1 / chart.factor))
      (CCL.ProgressiveSampling.approximation
        (preparedChartInput input chart)) where
  compare := by
    intro leftStart rightStart target positive
    let right := CCL.ProgressiveSampling.approximation
      (preparedChartInput input chart)
    let smallTarget := target / 4
    have smallPositive : 0 < smallTarget :=
      CCL.OperationalEquivalence.quarter_pos positive
    let base := right.refineIndex rightStart smallTarget smallPositive
    have baseGe : rightStart ≤ base :=
      right.refineIndex_ge rightStart smallTarget smallPositive
    have baseRadiusSmall : right.radiusSq base < smallTarget :=
      right.refineIndex_accurate rightStart smallTarget smallPositive
    let leftIndex := synchronizedReducedOutputIndexForSource
      input chart leftStart base
    exact
      { leftIndex := leftIndex
        rightIndex := base
        left_ge := synchronizedReducedOutputIndexForSource_ge
          input chart leftStart base
        right_ge := baseGe
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have baseToLeftSource :
              base ≤ synchronizedReducedSourceIndex input chart certificate
                leftLater := by
            exact (synchronizedReduced_reachesRequestedSourceIndex
              input chart certificate leftStart base).trans
                (CCL.OperationalEquivalence.emittedSampleIndex_mono
                    (synchronizedReducedApproximation input chart certificate)
                    leftOrder)
          have leftClose := right.later_close baseToLeftSource
          have rightCloseForward := right.later_close rightOrder
          have rightClose :
              normSq (right.sample base - right.sample rightLater) ≤
                right.radiusSq base := by
            have reverse :
                right.sample base - right.sample rightLater =
                  -(right.sample rightLater - right.sample base) := by
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
            rw [reverse, normSq_neg]
            exact rightCloseForward
          rw [synchronizedScaledChartSample_reconstructs
            input chart certificate leftLater]
          change normSq
              (right.sample
                  (synchronizedReducedSourceIndex input chart certificate
                    leftLater) - right.sample rightLater) < target
          calc
            normSq
                (right.sample
                    (synchronizedReducedSourceIndex input chart certificate
                      leftLater) - right.sample rightLater) ≤
              2 *
                (normSq
                    (right.sample
                        (synchronizedReducedSourceIndex input chart certificate
                          leftLater) - right.sample base) +
                  normSq (right.sample base - right.sample rightLater)) :=
              normSq_sub_le_via _ _ _
            _ ≤ 2 * (right.radiusSq base + right.radiusSq base) :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                (add_le_add leftClose rightClose) (by decide)
            _ < 2 * (smallTarget + smallTarget) :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct
                  baseRadiusSmall baseRadiusSmall)
            _ = target := two_quarter_sums target }

/-- Lift the finite sample comparison through the productive wrapper. -/
def synchronizedScaledChart_toPreparedInput (input : Named)
    (chart : Chart input) (certificate : BranchCertificate input chart) :
    NamedEquivalent
      (CCL.TranscendentalCoherence.scaledDynamicLocalExpLogChartApproximation
        (synchronizedReducedNamed input chart certificate)
        (synchronizedReducedDisk input chart certificate)
        (1 / chart.factor)).toNamed
      (preparedChartInput input chart) :=
  CCL.OperationalEquivalence.Equivalent.trans
    (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
      (CCL.TranscendentalCoherence.scaledDynamicLocalExpLogChartApproximation
        (synchronizedReducedNamed input chart certificate)
        (synchronizedReducedDisk input chart certificate)
        (1 / chart.factor)))
    (synchronizedScaledChartEquivalentPreparedSampling
      input chart certificate)

/-- Finite coherence identifies the prepared input state with the original
displayed starting state. -/
def preparedChartInput_equivalent (input : Named) (chart : Chart input)
    (inputCoherent :
      CCL.ProgressiveCoherence.Coherent input.process) :
    NamedEquivalent (preparedChartInput input chart) input :=
  inputCoherent.namedEquivalent
    (preparedChartInput input chart).state input.state

/-- Exact sample reconstruction plus finite state coherence identifies the
scaled synchronized chart with the original input name. -/
def synchronizedScaledChart_reconstructsInput (input : Named)
    (chart : Chart input) (certificate : BranchCertificate input chart)
    (inputCoherent :
      CCL.ProgressiveCoherence.Coherent input.process) :
    NamedEquivalent
      (CCL.TranscendentalCoherence.scaledDynamicLocalExpLogChartApproximation
        (synchronizedReducedNamed input chart certificate)
        (synchronizedReducedDisk input chart certificate)
        (1 / chart.factor)).toNamed
      input :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (synchronizedScaledChart_toPreparedInput input chart certificate)
    (preparedChartInput_equivalent input chart inputCoherent)

/-! ## Finite anchored inverse law for displayed rational inputs -/

/-- The rational reduced coordinate displayed by an exact chart input. -/
def exactReducedValue (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input)) :
    Gaussian :=
  (chart.factor * input - 1) / (chart.factor * input + 1)

theorem exactReducedValue_denominator_ne_zero (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input)) :
    chart.factor * input + 1 ≠ 0 := by
  let denominator := CCL.ComplexLogChart.denominator
    (CCL.ProgressiveTransducer.Named.exact input) chart.factor
  let state := denominator.state
  rcases denominator.process.witness state with ⟨value, possible⟩
  rcases CCL.ComplexLogChart.denominator_possible
      (CCL.ProgressiveTransducer.Named.exact input) chart.factor
      possible with ⟨source, sourcePossible, valueEqual⟩
  change source = input at sourcePossible
  subst source
  rw [valueEqual] at possible
  have lower := chart.denominatorApart.lower state possible
  intro denominatorZero
  rw [denominatorZero, normSq_zero] at lower
  exact (not_le_of_gt chart.denominatorApart.positive) lower

theorem reduced_inputSample_eq_exactReducedValue (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input))
    (index : Nat) :
    CCL.ProgressiveComplexLog.inputSample
        (CCL.ComplexLogChart.reduced
          (CCL.ProgressiveTransducer.Named.exact input)
          chart.factor chart.denominatorApart) index =
      exactReducedValue input chart := by
  let reduced := CCL.ComplexLogChart.reduced
    (CCL.ProgressiveTransducer.Named.exact input)
    chart.factor chart.denominatorApart
  have possible :=
    CCL.ProgressiveComplexLog.inputSample_possible_start
      reduced index
  rcases CCL.ComplexLogChart.reduced_possible
      (CCL.ProgressiveTransducer.Named.exact input)
      chart.factor chart.denominatorApart possible with
    ⟨numeratorSource, denominatorSource, numeratorPossible,
      denominatorPossible, valueEqual⟩
  change numeratorSource = input at numeratorPossible
  change denominatorSource = input at denominatorPossible
  subst numeratorSource
  subst denominatorSource
  exact valueEqual

theorem exactReducedValue_disk (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input)) :
    normSq (exactReducedValue input chart) ≤ 1 / 9 := by
  let reduced := CCL.ComplexLogChart.reduced
    (CCL.ProgressiveTransducer.Named.exact input)
    chart.factor chart.denominatorApart
  have possible :=
    CCL.ProgressiveComplexLog.inputSample_possible_start reduced 0
  have bound := chart.reducedDisk.possible_normSq possible
  rwa [reduced_inputSample_eq_exactReducedValue input chart 0] at bound

theorem exactReducedValue_chart (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input)) :
    (1 + exactReducedValue input chart) /
        (1 - exactReducedValue input chart) =
      chart.factor * input := by
  let scaled := chart.factor * input
  let reduced := exactReducedValue input chart
  have denominatorNonzero : scaled + 1 ≠ 0 := by
    exact exactReducedValue_denominator_ne_zero input chart
  have reducedIdentity : reduced * (scaled + 1) = scaled - 1 := by
    exact CCL.FinitePolynomial.gaussian_div_mul_cancel
      (scaled - 1) (scaled + 1) denominatorNonzero
  have reducedBound : normSq reduced ≤ 1 / 9 :=
    exactReducedValue_disk input chart
  have oneSubNonzero : 1 - reduced ≠ 0 :=
    CCL.FinitePolynomial.one_sub_ne_zero reducedBound
  have reducedCancellation :
      (1 - reduced) * (scaled + 1) = 1 + 1 := by
    calc
      (1 - reduced) * (scaled + 1) =
          (scaled + 1) - reduced * (scaled + 1) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im,
            one_re, one_im] <;> ring1
      _ = (scaled + 1) - (scaled - 1) := by rw [reducedIdentity]
      _ = 1 + 1 := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [add_re, add_im, sub_re, sub_im, one_re, one_im] <;> ring1
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    oneSubNonzero
  rw [CCL.FinitePolynomial.gaussian_div_mul_cancel
    (1 + reduced) (1 - reduced) oneSubNonzero]
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    denominatorNonzero
  calc
    (1 + reduced) * (scaled + 1) =
        (scaled + 1) + reduced * (scaled + 1) := by ring1
    _ = (scaled + 1) + (scaled - 1) := by rw [reducedIdentity]
    _ = scaled * (1 - reduced) * (scaled + 1) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc, reducedCancellation]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im,
          one_re, one_im] <;> ring1

theorem exactReducedValue_chart_times_inverse (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input))
    (certificate : BranchCertificate
      (CCL.ProgressiveTransducer.Named.exact input) chart) :
    ((1 + exactReducedValue input chart) /
        (1 - exactReducedValue input chart)) * (1 / chart.factor) = input := by
  rw [exactReducedValue_chart input chart, RFAP.ExplicitField.div_eq_mul_inv]
  calc
    chart.factor * input * (1 * chart.factor⁻¹) =
        input * (chart.factor * chart.factor⁻¹) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.one_mul,
        RFAP.ConstructiveGaussian.Gaussian.mul_comm chart.factor input,
        RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
    _ = input * 1 := by
      rw [show chart.factor * chart.factor⁻¹ = 1 by
        simpa only [RFAP.ConstructiveGaussian.Gaussian.inv_eq] using
          RFAP.ConstructiveGaussian.Gaussian.mul_inv chart.factor
            certificate.factor_ne_zero]
    _ = input := RFAP.ConstructiveGaussian.Gaussian.mul_one input

def correctionTarget (depth : Nat) : RFAP.ConstructiveFraction.Rational :=
  CCL.FiniteGeometric.quarterRadius 1 depth

theorem correctionTarget_pos (depth : Nat) : 0 < correctionTarget depth :=
  CCL.FiniteGeometric.quarterRadius_pos (by decide) depth

def correctionComparison (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input))
    (certificate : BranchCertificate
      (CCL.ProgressiveTransducer.Named.exact input) chart)
    (depth : Nat) :=
  certificate.correction_exponential.compare 0 0 (correctionTarget depth)
    (correctionTarget_pos depth)

/-- A computably scheduled sample of the supplied correction's global CCL
exponential.  Its index is obtained directly from the branch certificate. -/
def correctionExponentialSample (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input))
    (certificate : BranchCertificate
      (CCL.ProgressiveTransducer.Named.exact input) chart)
    (depth : Nat) : Gaussian :=
  (CCL.ProgressiveSampling.approximation
      (CCL.ProgressiveExpRange.named chart.correction)).sample
    (correctionComparison input chart certificate depth).leftIndex

theorem correctionExponentialSample_close (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input))
    (certificate : BranchCertificate
      (CCL.ProgressiveTransducer.Named.exact input) chart)
    (depth : Nat) :
    normSq (correctionExponentialSample input chart certificate depth -
      1 / chart.factor) < correctionTarget depth := by
  have close := (correctionComparison input chart certificate depth).close
    (Nat.le_refl _) (Nat.le_refl _)
  exact close

def correctionExponentialBound (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input)) :
    RFAP.ConstructiveFraction.Rational :=
  (CCL.ProgressiveSampling.approximation
    (CCL.ProgressiveExpRange.named chart.correction)).centerBound

theorem correctionExponentialBound_nonnegative (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input)) :
    0 ≤ correctionExponentialBound input chart :=
  (CCL.ProgressiveSampling.approximation
    (CCL.ProgressiveExpRange.named chart.correction)).centerBound_nonneg

theorem correctionExponentialSample_bounded (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input))
    (certificate : BranchCertificate
      (CCL.ProgressiveTransducer.Named.exact input) chart)
    (depth : Nat) :
    normSq (correctionExponentialSample input chart certificate depth) ≤
      correctionExponentialBound input chart :=
  (CCL.ProgressiveSampling.approximation
    (CCL.ProgressiveExpRange.named chart.correction)).sample_bounded _

/-- The product normal form supplied by the exponential addition law for the
exponential of the charted logarithm: exponentiate the local logarithm and
the branch correction, then multiply the two finite rational samples. -/
def expChartedLogSample (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input))
    (certificate : BranchCertificate
      (CCL.ProgressiveTransducer.Named.exact input) chart)
    (depth : Nat) : Gaussian :=
  CCL.FinitePolynomial.localExpLogSample
      (exactReducedValue input chart) depth *
    correctionExponentialSample input chart certificate depth

def expChartedLogErrorScale (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input)) :
    RFAP.ConstructiveFraction.Rational :=
  2 * (5 * 10 +
    CCL.FinitePolynomial.expLogErrorScale *
      normSq (1 / chart.factor))

theorem expChartedLogErrorScale_nonnegative (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input)) :
    0 ≤ expChartedLogErrorScale input chart :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        CCL.FinitePolynomial.expLogErrorScale_nonnegative
        (normSq_nonneg _)))

theorem expChartedLogSample_error (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input))
    (certificate : BranchCertificate
      (CCL.ProgressiveTransducer.Named.exact input) chart)
    (depth : Nat) :
    normSq (expChartedLogSample input chart certificate depth - input) ≤
      expChartedLogErrorScale input chart * (1 / 4) ^ depth := by
  let reduced := exactReducedValue input chart
  let localSample :=
    CCL.FinitePolynomial.localExpLogSample reduced depth
  let correction := correctionExponentialSample input chart certificate depth
  let chartValue := (1 + reduced) / (1 - reduced)
  let inverseFactor := 1 / chart.factor
  have reducedBound : normSq reduced ≤ 1 / 9 :=
    exactReducedValue_disk input chart
  have localError :
      normSq (localSample - chartValue) ≤
        CCL.FinitePolynomial.expLogErrorScale *
          (1 / 4 : RFAP.ConstructiveFraction.Rational) ^ depth :=
    CCL.FinitePolynomial.localExpLogSample_chart_error
      reducedBound depth
  have localBound : normSq localSample ≤ 5 * 10 :=
    CCL.FinitePolynomial.localExpLogSample_bounded
      reducedBound depth
  have correctionError :
      normSq (correction - inverseFactor) ≤
        (1 / 4 : RFAP.ConstructiveFraction.Rational) ^ depth := by
    simpa only [correctionTarget,
      CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
      RFAP.ConstructiveFraction.one_mul] using
        (correctionExponentialSample_close input chart certificate depth).le
  have targetIdentity : chartValue * inverseFactor = input :=
    exactReducedValue_chart_times_inverse input chart certificate
  have split : localSample * correction - chartValue * inverseFactor =
      localSample * (correction - inverseFactor) +
        (localSample - chartValue) * inverseFactor := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im] <;> ring1
  change normSq (localSample * correction - input) ≤
    expChartedLogErrorScale input chart * (1 / 4) ^ depth
  calc
    normSq (localSample * correction - input) =
        normSq (localSample * correction - chartValue * inverseFactor) := by
      exact congrArg normSq
        (congrArg (fun value => localSample * correction - value)
          targetIdentity.symm)
    _ = normSq (localSample * (correction - inverseFactor) +
        (localSample - chartValue) * inverseFactor) := by rw [split]
    _ ≤ 2 * (normSq (localSample * (correction - inverseFactor)) +
        normSq ((localSample - chartValue) * inverseFactor)) :=
      normSq_add_le_two _ _
    _ = 2 * (normSq localSample * normSq (correction - inverseFactor) +
        normSq (localSample - chartValue) * normSq inverseFactor) := by
      rw [normSq_mul, normSq_mul]
    _ ≤ 2 * ((5 * 10) * (1 / 4) ^ depth +
        (CCL.FinitePolynomial.expLogErrorScale *
          (1 / 4) ^ depth) * normSq inverseFactor) := by
      apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
        (by decide)
      exact add_le_add
        (RFAP.ConstructiveFraction.mul_le_mul_direct localBound correctionError
          (normSq_nonneg _) (by decide))
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          localError (normSq_nonneg _))
    _ = expChartedLogErrorScale input chart * (1 / 4) ^ depth := by
      dsimp only [expChartedLogErrorScale, inverseFactor]
      ring1

def expChartedLogApproximationScale (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input)) :
    RFAP.ConstructiveFraction.Rational :=
  4 * expChartedLogErrorScale input chart

theorem expChartedLogApproximationScale_nonnegative (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input)) :
    0 ≤ expChartedLogApproximationScale input chart :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (expChartedLogErrorScale_nonnegative input chart)

/-- A limit-free approximation for the exponential of an anchored, charted
logarithm.  Every sample is a finite Gaussian-rational calculation: the local
logarithm recurrence, its finite exponential recurrence, one requested sample
of the correction's CCL exponential, and one Gaussian multiplication. -/
def expChartedLogApproximation (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input))
    (certificate : BranchCertificate
      (CCL.ProgressiveTransducer.Named.exact input) chart) :
    Approximation where
  sample := expChartedLogSample input chart certificate
  radiusSq := fun depth =>
    CCL.FiniteGeometric.quarterRadius
      (expChartedLogApproximationScale input chart) depth
  radiusSq_nonneg := fun depth =>
    CCL.FiniteGeometric.quarterRadius_nonneg
      (expChartedLogApproximationScale_nonnegative input chart) depth
  later_close := by
    intro earlier later order
    have laterError := expChartedLogSample_error input chart certificate later
    have earlierError := expChartedLogSample_error input chart certificate earlier
    have laterScaled :
        expChartedLogErrorScale input chart * (1 / 4) ^ later ≤
          expChartedLogErrorScale input chart * (1 / 4) ^ earlier :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (CCL.FinitePolynomial.quarterPower_antitone order)
        (expChartedLogErrorScale_nonnegative input chart)
    have earlierReverse :
        normSq (input - expChartedLogSample input chart certificate earlier) ≤
          expChartedLogErrorScale input chart * (1 / 4) ^ earlier := by
      have identity : input - expChartedLogSample input chart certificate earlier =
          -(expChartedLogSample input chart certificate earlier - input) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
      rw [identity, normSq_neg]
      exact earlierError
    calc
      normSq (expChartedLogSample input chart certificate later -
          expChartedLogSample input chart certificate earlier) ≤
        2 * (normSq
            (expChartedLogSample input chart certificate later - input) +
          normSq
            (input - expChartedLogSample input chart certificate earlier)) :=
        normSq_sub_le_via _ input _
      _ ≤ 2 * (expChartedLogErrorScale input chart * (1 / 4) ^ earlier +
          expChartedLogErrorScale input chart * (1 / 4) ^ earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add (laterError.trans laterScaled) earlierReverse) (by decide)
      _ = CCL.FiniteGeometric.quarterRadius
          (expChartedLogApproximationScale input chart) earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        dsimp only [expChartedLogApproximationScale]
        ring1
  refineIndex := fun current target positive =>
    CCL.FiniteGeometric.firstQuarterBelow
      (expChartedLogApproximationScale input chart) current target
  refineIndex_ge := by
    intro current target positive
    exact CCL.FiniteGeometric.firstQuarterBelow_ge
      (expChartedLogApproximationScale input chart) current target
  refineIndex_accurate := by
    intro current target positive
    exact CCL.FiniteGeometric.firstQuarterBelow_accurate
      (expChartedLogApproximationScale input chart)
      (expChartedLogApproximationScale_nonnegative input chart)
      current target positive
  centerBound := (5 * 10) * correctionExponentialBound input chart
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide))
      (correctionExponentialBound_nonnegative input chart)
  sample_bounded := by
    intro depth
    rw [expChartedLogSample, normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      (CCL.FinitePolynomial.localExpLogSample_bounded
        (exactReducedValue_disk input chart) depth)
      (correctionExponentialSample_bounded input chart certificate depth)
      (normSq_nonneg _)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide))

def exactInputApproximation (input : Gaussian) : Approximation :=
  CCL.TranscendentalLaws.constantApproximation input

/-- The operational inverse approximation exposed through the ordinary
productive CCL controller. -/
def expChartedLogNamed (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input))
    (certificate : BranchCertificate
      (CCL.ProgressiveTransducer.Named.exact input) chart) : Named :=
  (expChartedLogApproximation input chart certificate).toNamed

theorem expChartedLogNamed_productive (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input))
    (certificate : BranchCertificate
      (CCL.ProgressiveTransducer.Named.exact input) chart)
    (count : Nat) :
    (expChartedLogNamed input chart certificate).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (expChartedLogNamed input chart certificate).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (expChartedLogNamed input chart certificate).machine count).emitted.length =
        count :=
  (expChartedLogApproximation input chart certificate).output_productive count

/-- Constructive finite-request inverse law for an anchored chart:
`exp(log(input; factor, correction))` is operationally equal to the exact
rational input.  For every positive rational squared tolerance the comparison
computes a depth after which all displayed samples satisfy that tolerance. -/
def exp_charted_log_equivalent (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input))
    (certificate : BranchCertificate
      (CCL.ProgressiveTransducer.Named.exact input) chart) :
    Equivalent (expChartedLogApproximation input chart certificate)
      (exactInputApproximation input) where
  compare := by
    intro leftStart rightStart target positive
    let leftIndex := CCL.FiniteGeometric.firstQuarterBelow
      (expChartedLogErrorScale input chart) leftStart target
    have leftSmall :
        expChartedLogErrorScale input chart * (1 / 4) ^ leftIndex < target := by
      simpa only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        using CCL.FiniteGeometric.firstQuarterBelow_accurate
          (expChartedLogErrorScale input chart)
          (expChartedLogErrorScale_nonnegative input chart)
          leftStart target positive
    exact
      { leftIndex := leftIndex
        rightIndex := rightStart
        left_ge := CCL.FiniteGeometric.firstQuarterBelow_ge
          (expChartedLogErrorScale input chart) leftStart target
        right_ge := Nat.le_refl _
        close := by
          intro leftLater rightLater leftOrder rightOrder
          change normSq
            (expChartedLogSample input chart certificate leftLater - input) <
              target
          exact (expChartedLogSample_error input chart certificate leftLater).trans_lt
            ((RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (CCL.FinitePolynomial.quarterPower_antitone leftOrder)
              (expChartedLogErrorScale_nonnegative input chart)).trans_lt
                leftSmall) }

theorem exactNamedSample (input : Gaussian) (index : Nat) :
    (CCL.ProgressiveSampling.approximation
      (CCL.ProgressiveTransducer.Named.exact input)).sample index =
        input := rfl

def exactInput_to_exactNamed_equivalent (input : Gaussian) :
    Equivalent (exactInputApproximation input)
      (CCL.ProgressiveSampling.approximation
        (CCL.ProgressiveTransducer.Named.exact input)) :=
  CCL.OperationalEquivalence.Equivalent.of_constant_samples
    (exactInputApproximation input)
    (CCL.ProgressiveSampling.approximation
      (CCL.ProgressiveTransducer.Named.exact input))
    input (fun _ => rfl) (exactNamedSample input)

/-- The productive CCL output of the anchored inverse calculation is itself
operationally equal, as a CCL name, to the exact displayed rational input. -/
def exp_charted_log_named_equivalent (input : Gaussian)
    (chart : Chart (CCL.ProgressiveTransducer.Named.exact input))
    (certificate : BranchCertificate
      (CCL.ProgressiveTransducer.Named.exact input) chart) :
    NamedEquivalent (expChartedLogNamed input chart certificate)
      (CCL.ProgressiveTransducer.Named.exact input) :=
  CCL.OperationalEquivalence.Equivalent.trans
    (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
      (expChartedLogApproximation input chart certificate))
    (CCL.OperationalEquivalence.Equivalent.trans
      (exp_charted_log_equivalent input chart certificate)
      (exactInput_to_exactNamed_equivalent input))

/-! ## Actual arbitrary-input exponential/logarithm composition -/

/-- The actual local-output and correction inputs of a chart, packaged with
their finite coherence certificates. -/
def localOutputCoherentNamed (input : Named) (chart : Chart input) :
    CCL.ProgressiveCoherence.CoherentNamed :=
  { name := CCL.ComplexLogChart.localOutput input chart
    coherent :=
      CCL.TranscendentalCoherence.localComplexLogCoherent
        (CCL.ComplexLogChart.reduced input chart.factor
          chart.denominatorApart) chart.reducedDisk }

def correctionCoherentNamed (input : Named) (chart : Chart input)
    (correctionCoherent :
      CCL.ProgressiveCoherence.Coherent
        chart.correction.process) :
    CCL.ProgressiveCoherence.CoherentNamed :=
  { name := chart.correction
    coherent := correctionCoherent }

/-- The new arbitrary-input global exponential addition theorem splits the
actual exponential of a charted logarithm into the actual exponentials of its
local output and its explicit correction. -/
def actualExp_chartedLog_split (input : Named) (chart : Chart input)
    (correctionCoherent :
      CCL.ProgressiveCoherence.Coherent
        chart.correction.process) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (CCL.ComplexLogChart.named input chart))
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveExpRange.named
          (CCL.ComplexLogChart.localOutput input chart))
        (CCL.ProgressiveExpRange.named chart.correction)) :=
  CCL.OperationalEquivalence.NamedEquivalent.symm
    (CCL.TranscendentalCoherence.automaticExp_add
      (localOutputCoherentNamed input chart)
      (correctionCoherentNamed input chart correctionCoherent))

/-- An anchored branch certificate replaces the correction exponential in the
actual product by the exact displayed reciprocal chart factor. -/
def actualExp_chartedLog_to_anchoredProduct (input : Named)
    (chart : Chart input)
    (certificate : BranchCertificate input chart)
    (correctionCoherent :
      CCL.ProgressiveCoherence.Coherent
        chart.correction.process) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (CCL.ComplexLogChart.named input chart))
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveExpRange.named
          (CCL.ComplexLogChart.localOutput input chart))
        (CCL.ProgressiveTransducer.Named.exact
          (1 / chart.factor))) := by
  let localOutput := localOutputCoherentNamed input chart
  let correction := correctionCoherentNamed input chart correctionCoherent
  let localExponential :=
    CCL.TranscendentalCoherence.exp localOutput.name
  let correctionExponential :=
    CCL.TranscendentalCoherence.exp correction.name
  let inverseFactor :=
    CCL.ProgressiveCoherence.CoherentNamed.exact
      (1 / chart.factor)
  have productEquivalent : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        localExponential.name correctionExponential.name)
      (CCL.ProgressiveTransducer.Named.mul
        localExponential.name inverseFactor.name) :=
    CCL.TranscendentalCoherence.coherentMul_respects
      localExponential localExponential correctionExponential inverseFactor
      (CCL.OperationalEquivalence.NamedEquivalent.refl
        localExponential.name)
      certificate.correction_exponential
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (actualExp_chartedLog_split input chart correctionCoherent)
    productEquivalent

/-- The anchored local product has no remaining transcendental content: it
is operationally the explicit finite Möbius reconstruction of the reduced
chart readings, scaled by the displayed reciprocal chart factor. -/
def anchoredLocalProduct_to_scaledChart (input : Named)
    (chart : Chart input) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveExpRange.named
          (CCL.ComplexLogChart.localOutput input chart))
        (CCL.ProgressiveTransducer.Named.exact
          (1 / chart.factor)))
      (CCL.TranscendentalCoherence.scaledDynamicLocalExpLogChartApproximation
          (CCL.ComplexLogChart.reduced input chart.factor
            chart.denominatorApart)
          chart.reducedDisk (1 / chart.factor)).toNamed :=
  CCL.TranscendentalCoherence.automaticExpLocalComplexLog_mulExact_toScaledChart
      (CCL.ComplexLogChart.reduced input chart.factor
        chart.denominatorApart)
      chart.reducedDisk (1 / chart.factor)

/-- The actual exponential of an anchored charted logarithm reaches a wholly
rational finite reconstruction program. -/
def actualExp_chartedLog_to_scaledChart (input : Named)
    (chart : Chart input)
    (certificate : BranchCertificate input chart)
    (correctionCoherent :
      CCL.ProgressiveCoherence.Coherent
        chart.correction.process) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (CCL.ComplexLogChart.named input chart))
      (CCL.TranscendentalCoherence.scaledDynamicLocalExpLogChartApproximation
          (CCL.ComplexLogChart.reduced input chart.factor
            chart.denominatorApart)
          chart.reducedDisk (1 / chart.factor)).toNamed :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (actualExp_chartedLog_to_anchoredProduct input chart certificate
      correctionCoherent)
    (anchoredLocalProduct_to_scaledChart input chart)

/-- Factored sufficiency interface: a finite operational proof of the rational
Möbius reconstruction completes the arbitrary-input global inverse.  The
unconditional construction below supplies this hypothesis. -/
def actualExp_chartedLog_named_equivalent_of_scaledChart
    (input : Named) (chart : Chart input)
    (certificate : BranchCertificate input chart)
    (correctionCoherent :
      CCL.ProgressiveCoherence.Coherent
        chart.correction.process)
    (scaledChartReconstructs : NamedEquivalent
      (CCL.TranscendentalCoherence.scaledDynamicLocalExpLogChartApproximation
          (CCL.ComplexLogChart.reduced input chart.factor
            chart.denominatorApart)
          chart.reducedDisk (1 / chart.factor)).toNamed
      input) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (CCL.ComplexLogChart.named input chart))
      input :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (actualExp_chartedLog_to_scaledChart input chart certificate
      correctionCoherent)
    scaledChartReconstructs

/-- A synchronized reduced reference may be used to discharge the last
rational resampling step.  Möbius sensitivity transports operational equality
from the actual stateful quotient to the reference before its scaled chart is
identified with the original input. -/
def actualExp_chartedLog_named_equivalent_of_reducedReference
    (input reference : Named) (chart : Chart input)
    (referenceDisk :
      CCL.ProgressiveComplexLog.Disk reference)
    (certificate : BranchCertificate input chart)
    (correctionCoherent :
      CCL.ProgressiveCoherence.Coherent
        chart.correction.process)
    (reducedEquivalent : NamedEquivalent
      (CCL.ComplexLogChart.reduced input chart.factor
        chart.denominatorApart)
      reference)
    (referenceReconstructs : NamedEquivalent
      (CCL.TranscendentalCoherence.scaledDynamicLocalExpLogChartApproximation
        reference referenceDisk (1 / chart.factor)).toNamed
      input) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (CCL.ComplexLogChart.named input chart))
      input := by
  have reconstructedEquivalent :=
    CCL.TranscendentalCoherence.scaledDynamicLocalExpLogChartNamed_respects
        chart.reducedDisk referenceDisk (1 / chart.factor) reducedEquivalent
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (actualExp_chartedLog_to_scaledChart input chart certificate
      correctionCoherent)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      reconstructedEquivalent referenceReconstructs)

/-- Factored synchronized-reference interface accepting the finite comparison
from the original independently sampled quotient as an explicit input.  The
comparison is constructed below. -/
def actualExp_chartedLog_named_equivalent_of_synchronizedReduced
    (input : Named) (chart : Chart input)
    (certificate : BranchCertificate input chart)
    (inputCoherent :
      CCL.ProgressiveCoherence.Coherent input.process)
    (correctionCoherent :
      CCL.ProgressiveCoherence.Coherent
        chart.correction.process)
    (reducedEquivalent : NamedEquivalent
      (CCL.ComplexLogChart.reduced input chart.factor
        chart.denominatorApart)
      (synchronizedReducedNamed input chart certificate)) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (CCL.ComplexLogChart.named input chart))
      input :=
  actualExp_chartedLog_named_equivalent_of_reducedReference
    input (synchronizedReducedNamed input chart certificate) chart
    (synchronizedReducedDisk input chart certificate) certificate
    correctionCoherent reducedEquivalent
    (synchronizedScaledChart_reconstructsInput
      input chart certificate inputCoherent)

/-- Full arbitrary-input anchored exponential--logarithm inverse.  Every
hypothesis is finite operational data: input and correction coherence, the
displayed chart, and its anchored branch certificate. -/
def actualExp_chartedLog_named_equivalent (input : Named)
    (chart : Chart input) (certificate : BranchCertificate input chart)
    (inputCoherent :
      CCL.ProgressiveCoherence.Coherent input.process)
    (correctionCoherent :
      CCL.ProgressiveCoherence.Coherent
        chart.correction.process) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (CCL.ComplexLogChart.named input chart))
      input :=
  actualExp_chartedLog_named_equivalent_of_synchronizedReduced
    input chart certificate inputCoherent correctionCoherent
      (reduced_equivalent_synchronizedReduced
        input chart certificate inputCoherent)

/-- Alternative factored sufficiency interface: once the anchored product is
related to the original input process, the actual global
exponential/logarithm round trip follows immediately. -/
def actualExp_chartedLog_named_equivalent_of_anchoredProduct
    (input : Named) (chart : Chart input)
    (certificate : BranchCertificate input chart)
    (correctionCoherent :
      CCL.ProgressiveCoherence.Coherent
        chart.correction.process)
    (anchoredLocalInverse : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveExpRange.named
          (CCL.ComplexLogChart.localOutput input chart))
        (CCL.ProgressiveTransducer.Named.exact
          (1 / chart.factor)))
      input) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (CCL.ComplexLogChart.named input chart))
      input :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (actualExp_chartedLog_to_anchoredProduct input chart certificate
      correctionCoherent)
    anchoredLocalInverse

end CCL.ComplexLogCorrectness
