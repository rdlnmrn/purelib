import mathlib.Tactic.QuotientFreeRing
import CCL.Transcendental.FiniteComplexLog
import CCL.Progressive.Sampling

/-!
# Local complex logarithm as a CCL computation

The input to this module is a progressive name for the reduced argument
`z = (u - 1) / (u + 1)`, together with the finite chart certificate that every
currently possible Gaussian-rational candidate has quadrance at most `1/9`.
Finite input refinement and finite Horner depth advance together.  No
completed complex value, infinite series, or global branch is introduced.
The resulting approximation is used as the accuracy sidechannel of a
productive CCL output name; a separate explicit chart supplies the global
branch correction.
-/

namespace CCL.ProgressiveComplexLog

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev Approximation :=
  CCL.ProgressiveApproximation.Approximation

open RFAP.ConstructiveGaussian.Gaussian

attribute [local irreducible] CCL.FiniteComplexLog.sample

/-- The closed reduced-argument disk used by the finite complex Horner
program. -/
structure Disk (input : Named) : Prop where
  possible_normSq : ∀ {value : Gaussian},
    input.process.Possible input.state value → normSq value ≤ 1 / 9

namespace Disk

theorem exact (value : Gaussian) (bound : normSq value ≤ 1 / 9) :
    Disk (CCL.ProgressiveTransducer.Named.exact value) where
  possible_normSq := by
    intro candidate possible
    change candidate = value at possible
    rw [possible]
    exact bound

end Disk

def inputSample (input : Named) (index : Nat) : Gaussian :=
  CCL.ProgressiveSampling.witnessAt
    input.process input.state index

theorem inputSample_possible_start (input : Named) (index : Nat) :
    input.process.Possible input.state (inputSample input index) :=
  CCL.ProgressiveSampling.witnessAt_possible_start
    input.process input.state index

theorem inputSample_bound {input : Named} (disk : Disk input) (index : Nat) :
    normSq (inputSample input index) ≤ 1 / 9 :=
  disk.possible_normSq (inputSample_possible_start input index)

theorem inputSample_later_close (input : Named)
    {oldIndex newIndex : Nat} (order : oldIndex ≤ newIndex) :
    normSq (inputSample input newIndex - inputSample input oldIndex) ≤
      CCL.FiniteGeometric.quarterRadius 4 oldIndex :=
  CCL.ProgressiveSampling.witnessAt_later_close
    input.process input.state order

structure DiskSamples where
  value : Nat → Gaussian
  bound : ∀ index, normSq (value index) ≤ 1 / 9
  close : ∀ {oldIndex newIndex : Nat}, oldIndex ≤ newIndex →
    normSq (value newIndex - value oldIndex) ≤
      CCL.FiniteGeometric.quarterRadius 4 oldIndex

def diskSamples (input : Named) (disk : Disk input) : DiskSamples where
  value := inputSample input
  bound := inputSample_bound disk
  close := inputSample_later_close input

def sampleFrom (source : DiskSamples) (index : Nat) : Gaussian :=
  CCL.FiniteComplexLog.sample (source.value index) index

def inputEffectScale : Coordinate :=
  CCL.FiniteComplexLog.sampleInputScale * 4

theorem inputEffectScale_nonneg : 0 ≤ inputEffectScale :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    CCL.FiniteComplexLog.sampleInputScale_nonneg (by decide)

theorem sampleFrom_input_effect (source : DiskSamples)
    {oldIndex newIndex : Nat} (order : oldIndex ≤ newIndex) :
    normSq
        (CCL.FiniteComplexLog.sample
            (source.value newIndex) oldIndex -
          CCL.FiniteComplexLog.sample
            (source.value oldIndex) oldIndex) ≤
      inputEffectScale * (1 / 4 : Coordinate) ^ oldIndex := by
  have sensitivity :
      normSq
          (CCL.FiniteComplexLog.sample
              (source.value newIndex) oldIndex -
            CCL.FiniteComplexLog.sample
              (source.value oldIndex) oldIndex) ≤
        CCL.FiniteComplexLog.sampleInputScale *
          normSq (source.value newIndex - source.value oldIndex) :=
    @CCL.FiniteComplexLog.sample_input_close
      (source.value newIndex) (source.value oldIndex)
      (source.bound newIndex) (source.bound oldIndex) oldIndex
  have movement :
      normSq (source.value newIndex - source.value oldIndex) ≤
        CCL.FiniteGeometric.quarterRadius 4 oldIndex :=
    source.close order
  calc
    normSq
        (CCL.FiniteComplexLog.sample
            (source.value newIndex) oldIndex -
          CCL.FiniteComplexLog.sample
            (source.value oldIndex) oldIndex) ≤
        CCL.FiniteComplexLog.sampleInputScale *
          normSq (source.value newIndex - source.value oldIndex) := sensitivity
    _ ≤ CCL.FiniteComplexLog.sampleInputScale *
        CCL.FiniteGeometric.quarterRadius 4 oldIndex :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct movement
        (by rw [CCL.FiniteComplexLog.sampleInputScale]; decide)
    _ = inputEffectScale * (1 / 4 : Coordinate) ^ oldIndex := by
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        inputEffectScale, CCL.FiniteComplexLog.sampleInputScale]
      ring1

def truncationScale : Coordinate := 5

def errorScale : Coordinate := 2 * (truncationScale + inputEffectScale)

theorem errorScale_nonneg : 0 ≤ errorScale := by
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg (by rw [truncationScale]; decide)
      inputEffectScale_nonneg)

theorem sampleFrom_later_close (source : DiskSamples)
    {oldIndex newIndex : Nat} (order : oldIndex ≤ newIndex) :
    normSq (sampleFrom source newIndex - sampleFrom source oldIndex) ≤
      CCL.FiniteGeometric.quarterRadius errorScale oldIndex := by
  have truncation :
      normSq
          (CCL.FiniteComplexLog.sample
              (source.value newIndex) newIndex -
            CCL.FiniteComplexLog.sample
              (source.value newIndex) oldIndex) ≤
        5 * (1 / 4 : Coordinate) ^ oldIndex :=
    @CCL.FiniteComplexLog.sample_later_close
      (source.value newIndex) (source.bound newIndex) oldIndex newIndex order
  have inputEffect :
      normSq
          (CCL.FiniteComplexLog.sample
              (source.value newIndex) oldIndex -
            CCL.FiniteComplexLog.sample
              (source.value oldIndex) oldIndex) ≤
        inputEffectScale * (1 / 4 : Coordinate) ^ oldIndex :=
    @sampleFrom_input_effect source oldIndex newIndex order
  calc
    normSq (sampleFrom source newIndex - sampleFrom source oldIndex) ≤
        2 * (normSq
          (CCL.FiniteComplexLog.sample
              (source.value newIndex) newIndex -
            CCL.FiniteComplexLog.sample
              (source.value newIndex) oldIndex) +
          normSq
          (CCL.FiniteComplexLog.sample
              (source.value newIndex) oldIndex -
            CCL.FiniteComplexLog.sample
              (source.value oldIndex) oldIndex)) :=
      normSq_sub_le_via _ _ _
    _ ≤ 2 * (truncationScale * (1 / 4 : Coordinate) ^ oldIndex +
        inputEffectScale * (1 / 4 : Coordinate) ^ oldIndex) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add (by simpa only [truncationScale] using truncation)
          inputEffect) (by decide)
    _ = CCL.FiniteGeometric.quarterRadius errorScale oldIndex := by
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow, errorScale,
        truncationScale]
      ring1

def domainSample (input : Named) (disk : Disk input) (index : Nat) : Gaussian :=
  sampleFrom (diskSamples input disk) index

theorem domainSample_later_close {input : Named} (disk : Disk input)
    {oldIndex newIndex : Nat} (order : oldIndex ≤ newIndex) :
    normSq (domainSample input disk newIndex - domainSample input disk oldIndex) ≤
      CCL.FiniteGeometric.quarterRadius errorScale oldIndex :=
  by
    change normSq
        (sampleFrom (diskSamples input disk) newIndex -
          sampleFrom (diskSamples input disk) oldIndex) ≤
      CCL.FiniteGeometric.quarterRadius errorScale oldIndex
    exact @sampleFrom_later_close (diskSamples input disk)
      oldIndex newIndex order

theorem domainSample_bounded {input : Named} (disk : Disk input)
    (index : Nat) : normSq (domainSample input disk index) ≤ 4 :=
  @CCL.FiniteComplexLog.sample_bounded
    (inputSample input index) (inputSample_bound disk index) index

def approximation (input : Named) (disk : Disk input) : Approximation where
  sample := domainSample input disk
  radiusSq := CCL.FiniteGeometric.quarterRadius errorScale
  radiusSq_nonneg index :=
    CCL.FiniteGeometric.quarterRadius_nonneg errorScale_nonneg index
  later_close := domainSample_later_close disk
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow errorScale current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge errorScale current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate errorScale
      errorScale_nonneg
  centerBound := 4
  centerBound_nonneg := by decide
  sample_bounded := domainSample_bounded disk

def named (input : Named) (disk : Disk input) : Named :=
  (approximation input disk).toNamed

theorem productive (input : Named) (disk : Disk input) (count : Nat) :
    (named input disk).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (named input disk).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (named input disk).machine count).emitted.length = count :=
  (approximation input disk).output_productive count

end CCL.ProgressiveComplexLog
