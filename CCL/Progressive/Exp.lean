import mathlib.Tactic.QuotientFreeRing
import CCL.Transcendental.FiniteExp
import CCL.Progressive.Sampling

/-!
# Progressive finite exponential

This is the local core of exponential as a CCL-to-CCL computation.  The input
is an existing arithmetic CCL name together with a finite domain certificate
for its candidates.  At natural index `n`, the output evaluates the depth-`n`
Horner program at the input's depth-`n` displayed rational witness, packages
those samples as a progressive enclosure process, and starts the unchanged
productive raw CCL controller on that process.  Thus neither side names a
completed point, while every requested finite output prefix is genuinely a
CCL prefix for the calculated exponential enclosure.
-/

namespace CCL.ProgressiveExp

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev Approximation :=
  CCL.ProgressiveApproximation.Approximation

open RFAP.ConstructiveGaussian.Gaussian

/-- The input-sensitivity coefficient `16 * 4`. -/
def inputErrorScale : Coordinate := 16 * 4

/-- `2 * (10 + 16 * 4)`, kept as a small arithmetic expression so neither
the kernel nor executable fraction arithmetic expands a large unary numeral. -/
def errorScale : Coordinate := 2 * (10 + inputErrorScale)

theorem errorScale_nonneg : 0 ≤ errorScale :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg (by decide) (by decide))

/-- Every explicitly possible input at the supplied finite starting state is
inside the rational closed unit disk.  Persistence transfers this certificate
to every later sampled witness. -/
structure UnitDisk (input : Named) : Prop where
  possible_unit : ∀ {value : Gaussian},
    input.process.Possible input.state value → normSq value ≤ 1

namespace UnitDisk

theorem exact (value : Gaussian) (unit : normSq value ≤ 1) :
    UnitDisk (CCL.ProgressiveTransducer.Named.exact value) where
  possible_unit := by
    intro candidate possible
    change candidate = value at possible
    rw [possible]
    exact unit

end UnitDisk

def inputSample (input : Named) (index : Nat) : Gaussian :=
  CCL.ProgressiveSampling.witnessAt
    input.process input.state index

theorem inputSample_possible_start (input : Named) (index : Nat) :
    input.process.Possible input.state (inputSample input index) :=
  CCL.ProgressiveSampling.witnessAt_possible_start
    input.process input.state index

theorem inputSample_unit {input : Named} (domain : UnitDisk input)
    (index : Nat) :
    normSq (inputSample input index) ≤ 1 :=
  domain.possible_unit (inputSample_possible_start input index)

/-- The depth and the displayed input witness advance together. -/
def sample (input : Named) (index : Nat) : Gaussian :=
  CCL.FiniteExp.sample (inputSample input index) index

def sampleFrom (samples : Nat → Gaussian) (index : Nat) : Gaussian :=
  CCL.FiniteExp.sample (samples index) index

structure UnitDiskSamples where
  value : Nat → Gaussian
  unit : ∀ index, normSq (value index) ≤ 1
  close : ∀ {oldIndex newIndex : Nat}, oldIndex ≤ newIndex →
    normSq (value newIndex - value oldIndex) ≤
      CCL.FiniteGeometric.quarterRadius 4 oldIndex

/-- Input movement at one fixed finite Horner depth. -/
theorem sampleFrom_input_effect (source : UnitDiskSamples)
    {oldIndex newIndex : Nat} (indexOrder : oldIndex ≤ newIndex) :
    normSq
        (CCL.FiniteExp.sample (source.value newIndex) oldIndex -
          CCL.FiniteExp.sample (source.value oldIndex) oldIndex) ≤
      inputErrorScale * (1 / 4 : Coordinate) ^ oldIndex := by
  have sensitivity := CCL.FiniteExp.sample_input_close
    (source.value newIndex) (source.value oldIndex)
    (source.unit newIndex) (source.unit oldIndex) oldIndex
  have movement := source.close indexOrder
  calc
    normSq
        (CCL.FiniteExp.sample (source.value newIndex) oldIndex -
          CCL.FiniteExp.sample (source.value oldIndex) oldIndex) ≤
        16 * normSq (source.value newIndex - source.value oldIndex) := sensitivity
    _ ≤ 16 * CCL.FiniteGeometric.quarterRadius 4 oldIndex :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct movement
        (by decide)
    _ = inputErrorScale * (1 / 4 : Coordinate) ^ oldIndex := by
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        inputErrorScale]
      ring1

/-- Quantitative core for simultaneous input and Horner-depth refinement. -/
theorem sampleFrom_later_close (source : UnitDiskSamples)
    {oldIndex newIndex : Nat} (indexOrder : oldIndex ≤ newIndex) :
    normSq (sampleFrom source.value newIndex -
      sampleFrom source.value oldIndex) ≤
      CCL.FiniteGeometric.quarterRadius errorScale oldIndex := by
  have truncation := CCL.FiniteExp.sample_later_close
    (source.value newIndex) (source.unit newIndex) indexOrder
  have inputEffect := sampleFrom_input_effect source indexOrder
  calc
    normSq (sampleFrom source.value newIndex -
        sampleFrom source.value oldIndex) ≤
        2 * (normSq
          (CCL.FiniteExp.sample (source.value newIndex) newIndex -
            CCL.FiniteExp.sample (source.value newIndex) oldIndex) +
          normSq
          (CCL.FiniteExp.sample (source.value newIndex) oldIndex -
            CCL.FiniteExp.sample (source.value oldIndex) oldIndex)) :=
      normSq_sub_le_via _ _ _
    _ ≤ 2 * (CCL.FiniteGeometric.quarterRadius 10 oldIndex +
        inputErrorScale * (1 / 4 : Coordinate) ^ oldIndex) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add truncation inputEffect) (by decide)
    _ = CCL.FiniteGeometric.quarterRadius errorScale oldIndex := by
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow, errorScale]
      ring1

def unitDiskSamples (input : Named) (domain : UnitDisk input) : UnitDiskSamples :=
  { value := inputSample input
    unit := inputSample_unit domain
    close := fun move =>
      CCL.ProgressiveSampling.witnessAt_later_close
        input.process input.state move }

def domainSample (input : Named) (domain : UnitDisk input) (index : Nat) :
    Gaussian :=
  sampleFrom (unitDiskSamples input domain).value index

/-- Simultaneous input refinement and Horner-depth refinement have one
explicit quarter-power squared-error bound. -/
theorem sample_later_close {input : Named} (domain : UnitDisk input)
    {earlier later : Nat} (order : earlier ≤ later) :
    normSq
      (sampleFrom (unitDiskSamples input domain).value later -
        sampleFrom (unitDiskSamples input domain).value earlier) ≤
      CCL.FiniteGeometric.quarterRadius errorScale earlier := by
  exact sampleFrom_later_close (unitDiskSamples input domain) order

theorem sample_bounded {input : Named} (domain : UnitDisk input)
    (index : Nat) :
    normSq (domainSample input domain index) ≤ 10 :=
  CCL.FiniteExp.sample_bounded _ (inputSample_unit domain index) index

/-- The accuracy sidechannel for the local CCL exponential transform.  Its
`Possible` predicate contains only later displayed output samples. -/
def approximation (input : Named) (domain : UnitDisk input) : Approximation where
  sample := domainSample input domain
  radiusSq := CCL.FiniteGeometric.quarterRadius errorScale
  radiusSq_nonneg index :=
    CCL.FiniteGeometric.quarterRadius_nonneg errorScale_nonneg index
  later_close := sample_later_close domain
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow errorScale current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge errorScale current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate errorScale
      errorScale_nonneg
  centerBound := 10
  centerBound_nonneg := by decide
  sample_bounded := sample_bounded domain

/-- Convert a unit-disk arithmetic CCL name into the corresponding productive
local exponential CCL name. -/
def named (input : Named) (domain : UnitDisk input) : Named :=
  (approximation input domain).toNamed

theorem productive (input : Named) (domain : UnitDisk input) (count : Nat) :
    (named input domain).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (named input domain).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (named input domain).machine count).emitted.length = count :=
  (approximation input domain).output_productive count

end CCL.ProgressiveExp
