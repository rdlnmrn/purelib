import mathlib.Tactic.QuotientFreeRing
import CCL.Transcendental.FiniteLogSensitivity
import CCL.Progressive.Sampling

/-!
# Local logarithm as a CCL computation

This is the local core of logarithm as a CCL-to-CCL computation.  The input is
an arithmetic CCL name carrying an explicit overlapping chart certificate.
Every candidate is a displayed real Gaussian rational whose coordinate lies
in `[1/2,2]`.  The output synchronizes later finite input witnesses with later
finite Horner depths, packages the result as an accuracy sidechannel, and
starts the unchanged productive CCL controller on it.  It does not assert a
completed positive real input or a completed logarithm.
-/

namespace CCL.ProgressiveLog

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev Approximation :=
  CCL.ProgressiveApproximation.Approximation

open RFAP.ConstructiveGaussian.Gaussian

/-- One redundant local chart for the real logarithm. -/
structure Chart (input : Named) : Prop where
  possible_real_chart : ∀ {value : Gaussian},
    input.process.Possible input.state value →
      value.im = 0 ∧ 1 / 2 ≤ value.re ∧ value.re ≤ 2

namespace Chart

theorem exact (value : Coordinate) (halfLe : 1 / 2 ≤ value)
    (leTwo : value ≤ 2) :
    Chart (CCL.ProgressiveTransducer.Named.exact
      (CCL.FiniteLog.real value)) where
  possible_real_chart := by
    intro candidate possible
    change candidate = CCL.FiniteLog.real value at possible
    rw [possible]
    exact ⟨rfl, halfLe, leTwo⟩

end Chart

def inputWitness (input : Named) (index : Nat) : Gaussian :=
  CCL.ProgressiveSampling.witnessAt
    input.process input.state index

theorem inputWitness_possible_start (input : Named) (index : Nat) :
    input.process.Possible input.state (inputWitness input index) :=
  CCL.ProgressiveSampling.witnessAt_possible_start
    input.process input.state index

theorem inputWitness_chart {input : Named} (chart : Chart input) (index : Nat) :
    (inputWitness input index).im = 0 ∧
      1 / 2 ≤ (inputWitness input index).re ∧
      (inputWitness input index).re ≤ 2 :=
  chart.possible_real_chart (inputWitness_possible_start input index)

def inputSample (input : Named) (index : Nat) : Coordinate :=
  (inputWitness input index).re

theorem inputSample_half {input : Named} (chart : Chart input) (index : Nat) :
    1 / 2 ≤ inputSample input index :=
  (inputWitness_chart chart index).2.1

theorem inputSample_two {input : Named} (chart : Chart input) (index : Nat) :
    inputSample input index ≤ 2 :=
  (inputWitness_chart chart index).2.2

theorem inputSample_later_close {input : Named} (chart : Chart input)
    {oldIndex newIndex : Nat} (indexOrder : oldIndex ≤ newIndex) :
    (inputSample input newIndex - inputSample input oldIndex) ^ 2 ≤
      CCL.FiniteGeometric.quarterRadius 4 oldIndex := by
  have movement := CCL.ProgressiveSampling.witnessAt_later_close
    input.process input.state indexOrder
  have newImaginary := (inputWitness_chart chart newIndex).1
  have oldImaginary := (inputWitness_chart chart oldIndex).1
  have equality :
      normSq (inputWitness input newIndex - inputWitness input oldIndex) =
        (inputSample input newIndex - inputSample input oldIndex) ^ 2 := by
    rw [normSq]
    simp only [sub_re, sub_im, inputSample, newImaginary, oldImaginary]
    ring1
  rw [← equality]
  exact movement

structure ChartSamples where
  value : Nat → Coordinate
  half : ∀ index, 1 / 2 ≤ value index
  two : ∀ index, value index ≤ 2
  close : ∀ {oldIndex newIndex : Nat}, oldIndex ≤ newIndex →
    (value newIndex - value oldIndex) ^ 2 ≤
      CCL.FiniteGeometric.quarterRadius 4 oldIndex

def chartSamples (input : Named) (chart : Chart input) : ChartSamples :=
  { value := inputSample input
    half := inputSample_half chart
    two := inputSample_two chart
    close := inputSample_later_close chart }

def sampleFrom (source : ChartSamples) (index : Nat) : Gaussian :=
  CCL.FiniteLog.sample (source.value index) index

/-- Input movement contribution at one fixed finite logarithm depth. -/
theorem sampleFrom_input_effect (source : ChartSamples)
    {oldIndex newIndex : Nat} (indexOrder : oldIndex ≤ newIndex) :
    normSq
        (CCL.FiniteLog.sample (source.value newIndex) oldIndex -
          CCL.FiniteLog.sample (source.value oldIndex) oldIndex) ≤
      (CCL.FiniteLog.sampleInputScale * 4) *
        (1 / 4 : Coordinate) ^ oldIndex := by
  have sensitivity := CCL.FiniteLog.sample_input_close
    (source.half newIndex) (source.two newIndex)
    (source.half oldIndex) (source.two oldIndex) oldIndex
  have movement := source.close indexOrder
  calc
    normSq
        (CCL.FiniteLog.sample (source.value newIndex) oldIndex -
          CCL.FiniteLog.sample (source.value oldIndex) oldIndex) ≤
        CCL.FiniteLog.sampleInputScale *
          (source.value newIndex - source.value oldIndex) ^ 2 := sensitivity
    _ ≤ CCL.FiniteLog.sampleInputScale *
        CCL.FiniteGeometric.quarterRadius 4 oldIndex :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct movement
        (by
          rw [CCL.FiniteLog.sampleInputScale]
          exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (add_nonneg (by decide) (by decide)))
    _ = (CCL.FiniteLog.sampleInputScale * 4) *
        (1 / 4 : Coordinate) ^ oldIndex := by
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
      ring1

def inputEffectScale : Coordinate :=
  CCL.FiniteLog.sampleInputScale * 4

def errorScale : Coordinate := 2 * (1 + inputEffectScale)

theorem errorScale_nonneg : 0 ≤ errorScale := by
  rw [errorScale, inputEffectScale,
    CCL.FiniteLog.sampleInputScale]
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg (by decide)
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (add_nonneg (by decide) (by decide))) (by decide)))

/-- Combined finite input and truncation movement. -/
theorem sampleFrom_later_close (source : ChartSamples)
    {oldIndex newIndex : Nat} (indexOrder : oldIndex ≤ newIndex) :
    normSq (sampleFrom source newIndex - sampleFrom source oldIndex) ≤
      CCL.FiniteGeometric.quarterRadius errorScale oldIndex := by
  have truncation := CCL.FiniteLog.sample_later_close
    (source.half newIndex) (source.two newIndex) indexOrder
  have inputEffect := sampleFrom_input_effect source indexOrder
  calc
    normSq (sampleFrom source newIndex - sampleFrom source oldIndex) ≤
        2 * (normSq
          (CCL.FiniteLog.sample (source.value newIndex) newIndex -
            CCL.FiniteLog.sample (source.value newIndex) oldIndex) +
          normSq
          (CCL.FiniteLog.sample (source.value newIndex) oldIndex -
            CCL.FiniteLog.sample (source.value oldIndex) oldIndex)) :=
      normSq_sub_le_via _ _ _
    _ ≤ 2 * (CCL.FiniteGeometric.quarterRadius 1 oldIndex +
        inputEffectScale * (1 / 4 : Coordinate) ^ oldIndex) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add truncation (by
          simpa only [inputEffectScale] using inputEffect)) (by decide)
    _ = CCL.FiniteGeometric.quarterRadius errorScale oldIndex := by
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow, errorScale]
      ring1

def domainSample (input : Named) (chart : Chart input) (index : Nat) : Gaussian :=
  sampleFrom (chartSamples input chart) index

theorem domainSample_later_close {input : Named} (chart : Chart input)
    {oldIndex newIndex : Nat} (indexOrder : oldIndex ≤ newIndex) :
    normSq
      (sampleFrom (chartSamples input chart) newIndex -
        sampleFrom (chartSamples input chart) oldIndex) ≤
      CCL.FiniteGeometric.quarterRadius errorScale oldIndex :=
  sampleFrom_later_close (chartSamples input chart) indexOrder

theorem domainSample_bounded {input : Named} (chart : Chart input)
    (index : Nat) :
    normSq (domainSample input chart index) ≤ 4 :=
  CCL.FiniteLog.sample_bounded
    (inputSample_half chart index) (inputSample_two chart index) index

def approximation (input : Named) (chart : Chart input) : Approximation where
  sample := domainSample input chart
  radiusSq := CCL.FiniteGeometric.quarterRadius errorScale
  radiusSq_nonneg index :=
    CCL.FiniteGeometric.quarterRadius_nonneg errorScale_nonneg index
  later_close := domainSample_later_close chart
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow errorScale current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge errorScale current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate errorScale
      errorScale_nonneg
  centerBound := 4
  centerBound_nonneg := by decide
  sample_bounded := domainSample_bounded chart

def named (input : Named) (chart : Chart input) : Named :=
  (approximation input chart).toNamed

theorem productive (input : Named) (chart : Chart input) (count : Nat) :
    (named input chart).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (named input chart).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (named input chart).machine count).emitted.length = count :=
  (approximation input chart).output_productive count

end CCL.ProgressiveLog
