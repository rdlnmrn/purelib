import mathlib.Tactic.QuotientFreeRing
import CCL.Progressive.ComplexLog

/-!
# One certified complex logarithm branch chart

A chart scales the input by one displayed Gaussian rational `factor`, forms
the exact progressive quotient

`(factor * input - 1) / (factor * input + 1)`,

and requires finite certificates that every possible denominator has a fixed
positive lower quadrance and that every possible quotient lies in the local
disk of the finite complex-log recurrence.  One finite preparation step turns
the first certificate into whole-ball apartness before division.  A separate
progressive correction name selects the desired additive branch normalization.

This is deliberately a one-chart interface.  It is not a total complex
logarithm and it does not hide a branch choice or a completed complex value.
-/

namespace CCL.ComplexLogChart

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev Disk := CCL.ProgressiveComplexLog.Disk
abbrev PossibleApart := CCL.ProgressiveCharts.PossibleApart

def exactOne : Named :=
  CCL.ProgressiveTransducer.Named.exact 1

def scaled (input : Named) (factor : Gaussian) : Named :=
  CCL.ProgressiveTransducer.Named.mul
    (CCL.ProgressiveTransducer.Named.exact factor) input

def numerator (input : Named) (factor : Gaussian) : Named :=
  CCL.ProgressiveTransducer.Named.sub
    (scaled input factor) exactOne

def denominator (input : Named) (factor : Gaussian) : Named :=
  CCL.ProgressiveTransducer.Named.add
    (scaled input factor) exactOne

theorem scaled_possible (input : Named) (factor : Gaussian)
    {state : (scaled input factor).process.State} {value : Gaussian}
    (possible : (scaled input factor).process.Possible state value) :
    ∃ source : Gaussian,
      input.process.Possible state.2 source ∧ value = factor * source := by
  rcases possible with
    ⟨exactFactor, source, factorPossible, sourcePossible, valueEqual⟩
  change exactFactor = factor at factorPossible
  subst exactFactor
  exact ⟨source, sourcePossible, valueEqual⟩

theorem numerator_possible (input : Named) (factor : Gaussian)
    {state : (numerator input factor).process.State} {value : Gaussian}
    (possible : (numerator input factor).process.Possible state value) :
    ∃ source : Gaussian,
      input.process.Possible state.1.2 source ∧
        value = factor * source - 1 := by
  rcases possible with
    ⟨scaledValue, negativeOne, scaledPossible,
      ⟨oneValue, onePossible, negativeEqual⟩, valueEqual⟩
  rcases scaled_possible input factor scaledPossible with
    ⟨source, sourcePossible, scaledEqual⟩
  change oneValue = (1 : Gaussian) at onePossible
  subst oneValue
  rw [negativeEqual, scaledEqual] at valueEqual
  refine ⟨source, sourcePossible, ?_⟩
  rw [valueEqual]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.neg_re,
      RFAP.ConstructiveGaussian.Gaussian.neg_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im] <;> ring1

theorem denominator_possible (input : Named) (factor : Gaussian)
    {state : (denominator input factor).process.State} {value : Gaussian}
    (possible : (denominator input factor).process.Possible state value) :
    ∃ source : Gaussian,
      input.process.Possible state.1.2 source ∧
        value = factor * source + 1 := by
  rcases possible with
    ⟨scaledValue, oneValue, scaledPossible, onePossible, valueEqual⟩
  rcases scaled_possible input factor scaledPossible with
    ⟨source, sourcePossible, scaledEqual⟩
  change oneValue = (1 : Gaussian) at onePossible
  subst oneValue
  rw [scaledEqual] at valueEqual
  exact ⟨source, sourcePossible, valueEqual⟩

/-- A lower bound stated only for genuine input candidates supplies the
possible-denominator apartness used by chart preparation. -/
def denominatorPossibleApart (input : Named) (factor : Gaussian)
    (lowerSq : RFAP.ConstructiveFraction.Rational) (positive : 0 < lowerSq)
    (lower : ∀ (state : input.process.State) {source : Gaussian},
      input.process.Possible state source →
        lowerSq ≤
          RFAP.ConstructiveGaussian.Gaussian.normSq (factor * source + 1)) :
    PossibleApart (denominator input factor).process where
  lowerSq := lowerSq
  positive := positive
  lower := by
    intro state value possible
    rcases denominator_possible input factor possible with
      ⟨source, sourcePossible, valueEqual⟩
    rw [valueEqual]
    exact lower state.1.2 sourcePossible

def preparedDenominator (input : Named) (factor : Gaussian)
    (apart : PossibleApart (denominator input factor).process) : Named :=
  { process := CCL.ProgressiveCharts.apartify apart
    state := CCL.ProgressiveCharts.prepareApartState apart
      (denominator input factor).state }

def preparedDenominatorApart (input : Named) (factor : Gaussian)
    (apart : PossibleApart (denominator input factor).process) :
    CCL.ProgressiveTransducer.Named.Apart
      (preparedDenominator input factor apart) where
  certificate := CCL.ProgressiveCharts.apartifyApart apart

def reduced (input : Named) (factor : Gaussian)
    (apart : PossibleApart (denominator input factor).process) : Named :=
  CCL.ProgressiveTransducer.Named.div
    (numerator input factor) (preparedDenominator input factor apart)
    (preparedDenominatorApart input factor apart)

theorem reduced_possible (input : Named) (factor : Gaussian)
    (apart : PossibleApart (denominator input factor).process)
    {value : Gaussian}
    (possible : (reduced input factor apart).process.Possible
      (reduced input factor apart).state value) :
    ∃ numeratorSource denominatorSource : Gaussian,
      input.process.Possible input.state numeratorSource ∧
      input.process.Possible input.state denominatorSource ∧
      value = (factor * numeratorSource - 1) /
        (factor * denominatorSource + 1) := by
  rcases possible with
    ⟨numeratorValue, denominatorValue, numeratorPossible,
      denominatorPossible, valueEqual⟩
  rcases numerator_possible input factor numeratorPossible with
    ⟨numeratorSource, numeratorSourcePossible, numeratorEqual⟩
  have originalDenominatorPossible :
      (denominator input factor).process.Possible
        (denominator input factor).state denominatorValue :=
    CCL.ProgressiveCharts.prepareApartState_persists apart
      (denominator input factor).state denominatorPossible
  rcases denominator_possible input factor originalDenominatorPossible with
    ⟨denominatorSource, denominatorSourcePossible, denominatorEqual⟩
  exact ⟨numeratorSource, denominatorSource,
    numeratorSourcePossible, denominatorSourcePossible, by
      rw [valueEqual, numeratorEqual, denominatorEqual]⟩

/-- A square-root-free bound on all independently admitted numerator and
denominator candidates constructs the local reduced-disk certificate.  The
two candidates may differ because enclosure arithmetic conservatively
duplicates a progressive input. -/
theorem reducedDiskOfBounds (input : Named) (factor : Gaussian)
    (apart : PossibleApart (denominator input factor).process)
    (bound : ∀ {numeratorSource denominatorSource : Gaussian},
      input.process.Possible input.state numeratorSource →
      input.process.Possible input.state denominatorSource →
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((factor * numeratorSource - 1) /
            (factor * denominatorSource + 1)) ≤ 1 / 9) :
    Disk (reduced input factor apart) where
  possible_normSq := by
    intro value possible
    rcases reduced_possible input factor apart possible with
      ⟨numeratorSource, denominatorSource, numeratorPossible,
        denominatorPossible, valueEqual⟩
    rw [valueEqual]
    exact bound numeratorPossible denominatorPossible

/-- Finite data selecting one branch-safe local chart.  The correction is a
name rather than a completed value, so non-rational branch normalizations can
still be refined on demand. -/
structure Chart (input : Named) where
  factor : Gaussian
  denominatorApart : PossibleApart (denominator input factor).process
  reducedDisk : Disk (reduced input factor denominatorApart)
  correction : Named

namespace Chart

/-- Package the operational chart from two checkable rational inequalities:
a positive denominator lower bound at every finite input state, and the local
disk bound for every pair of candidates admitted by the starting state. -/
def ofBounds (input : Named) (factor : Gaussian)
    (lowerSq : RFAP.ConstructiveFraction.Rational) (positive : 0 < lowerSq)
    (denominatorLower :
      ∀ (state : input.process.State) {source : Gaussian},
        input.process.Possible state source →
          lowerSq ≤
            RFAP.ConstructiveGaussian.Gaussian.normSq (factor * source + 1))
    (localBound : ∀ {numeratorSource denominatorSource : Gaussian},
      input.process.Possible input.state numeratorSource →
      input.process.Possible input.state denominatorSource →
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((factor * numeratorSource - 1) /
            (factor * denominatorSource + 1)) ≤ 1 / 9)
    (correction : Named) : Chart input := by
  let apart := denominatorPossibleApart input factor lowerSq positive
    denominatorLower
  exact
    { factor := factor
      denominatorApart := apart
      reducedDisk := reducedDiskOfBounds input factor apart localBound
      correction := correction }

end Chart

/-- A concrete inhabited chart: the exact rational input `1` uses factor
`1`, reduced argument `0`, and zero correction. -/
def unitChart : Chart
    (CCL.ProgressiveTransducer.Named.exact 1) :=
  Chart.ofBounds
    (CCL.ProgressiveTransducer.Named.exact 1)
    1 1 (by decide)
    (by
      intro state source possible
      change source = (1 : Gaussian) at possible
      subst source
      change (1 : RFAP.ConstructiveFraction.Rational) ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq (1 * 1 + 1)
      decide)
    (by
      intro numeratorSource denominatorSource numeratorPossible
        denominatorPossible
      change numeratorSource = (1 : Gaussian) at numeratorPossible
      change denominatorSource = (1 : Gaussian) at denominatorPossible
      subst numeratorSource
      subst denominatorSource
      change RFAP.ConstructiveGaussian.Gaussian.normSq
          (((1 : Gaussian) * 1 - 1) / ((1 : Gaussian) * 1 + 1)) ≤ 1 / 9
      decide)
    (CCL.ProgressiveTransducer.Named.exact 0)

def localOutput (input : Named) (chart : Chart input) : Named :=
  CCL.ProgressiveComplexLog.named
    (reduced input chart.factor chart.denominatorApart) chart.reducedDisk

/-- The selected complex-log branch: local Horner output plus the explicitly
supplied additive branch correction. -/
def named (input : Named) (chart : Chart input) : Named :=
  CCL.ProgressiveTransducer.Named.add
    (localOutput input chart) chart.correction

theorem local_productive (input : Named) (chart : Chart input) (count : Nat) :
    (localOutput input chart).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (localOutput input chart).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (localOutput input chart).machine count).emitted.length = count :=
  CCL.ProgressiveComplexLog.productive
    (reduced input chart.factor chart.denominatorApart)
    chart.reducedDisk count

theorem productive (input : Named) (chart : Chart input) (count : Nat) :
    (named input chart).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (named input chart).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (named input chart).machine count).emitted.length = count :=
  (named input chart).productive count

end CCL.ComplexLogChart
