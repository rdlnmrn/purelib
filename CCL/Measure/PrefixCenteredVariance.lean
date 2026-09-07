import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixDeviation
import CCL.Measure.PrefixStability
import FiniteMeasure.VarianceLp

/-!
# Witness-centred variance enclosures from finite CCL prefixes

The displayed prefix witnesses have an exact rational probe expectation.
Variance around that computable centre differs from the true finite variance
by exactly the square of the mean error.  A powered-deviation enclosure and
the explicit prefix mean radius therefore give a direct rational variance
enclosure without squaring a signed mean interval.
-/

namespace CCL.FiniteMeasure

/-- Enclosure `[0, R²]` for the squared difference between an admitted probe
expectation and the displayed witness expectation. -/
def prefixFamilyProbeMeanSquareErrorBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (factor : Coordinate) : _root_.FiniteMeasure.Bound where
  lower := 0
  upper := prefixFamilyProbeRadius distribution factor ^ 2
  valid := RFAP.ConstructiveFraction.sq_nonneg_direct _

/-- The exact squared mean error of every admitted realization family lies
in the explicit prefix-radius square enclosure. -/
theorem prefixFamilyProbeMeanSquareErrorBound_contains
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (prefixFamilyProbeMeanSquareErrorBound distribution factor).Contains
      (((distribution.expectation fun certificate => probe (points certificate)) -
        prefixFamilyProbeWitnessExpectation distribution probe) ^ 2) := by
  have separationLe :=
    prefixFamilyProbe_expectation_separation_witness_le distribution probe
      factor factorNonnegative sensitive points pointsRealize
  have powered := RFAP.ConstructiveFraction.pow_le_pow_direct
    (_root_.FiniteMeasure.rationalSeparation_nonneg _ _) separationLe 2
  rw [_root_.FiniteMeasure.rationalSeparation_sq] at powered
  exact ⟨RFAP.ConstructiveFraction.sq_nonneg_direct _, powered⟩

/-- Variance enclosure obtained from deviation about the computable witness
mean minus the explicit squared mean-error enclosure. -/
def prefixFamilyProbeCenteredVarianceBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate)
    (meanFactor : Coordinate)
    (deviationFactor : Coordinate)
    (deviationFactorNonnegative : 0 ≤ deviationFactor)
    (deviationSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe
            (prefixFamilyProbeWitnessExpectation distribution probe) 2 left)
          (poweredDeviationProbe probe
            (prefixFamilyProbeWitnessExpectation distribution probe) 2 right) ≤
        deviationFactor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound :=
  (prefixFamilyProbePoweredDeviationBound distribution probe
    (prefixFamilyProbeWitnessExpectation distribution probe) 2
    deviationFactor deviationFactorNonnegative deviationSensitive).sub
  (prefixFamilyProbeMeanSquareErrorBound distribution meanFactor)

/-- Every admitted realization family has its exact finite variance inside
the witness-centred CCL enclosure. -/
theorem prefixFamilyProbeCenteredVarianceBound_contains
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        meanFactor * CCL.Chordal.chordalSq left right)
    (deviationFactor : Coordinate)
    (deviationFactorNonnegative : 0 ≤ deviationFactor)
    (deviationSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe
            (prefixFamilyProbeWitnessExpectation distribution probe) 2 left)
          (poweredDeviationProbe probe
            (prefixFamilyProbeWitnessExpectation distribution probe) 2 right) ≤
        deviationFactor * CCL.Chordal.chordalSq left right)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (prefixFamilyProbeCenteredVarianceBound distribution probe meanFactor
      deviationFactor deviationFactorNonnegative
      deviationSensitive).Contains
      (distribution.variance fun certificate => probe (points certificate)) := by
  let center := prefixFamilyProbeWitnessExpectation distribution probe
  let value := fun certificate => probe (points certificate)
  have deviationInside :=
    prefixFamilyProbePoweredDeviationBound_contains distribution probe center 2
      deviationFactor deviationFactorNonnegative deviationSensitive points
      pointsRealize
  have varianceAroundInside :
      (prefixFamilyProbePoweredDeviationBound distribution probe center 2
        deviationFactor deviationFactorNonnegative deviationSensitive).Contains
        (distribution.varianceAround value center) := by
    rw [distribution.varianceAround_eq_poweredL2Distance_constant,
      ← distribution.poweredLpDistance_two]
    exact deviationInside
  have meanErrorInside :=
    prefixFamilyProbeMeanSquareErrorBound_contains distribution probe
      meanFactor meanFactorNonnegative meanSensitive points pointsRealize
  have differenceInside := _root_.FiniteMeasure.Bound.sub_contains
    varianceAroundInside meanErrorInside
  have varianceIdentity :
      distribution.varianceAround value center -
          (distribution.expectation value - center) ^ 2 =
        distribution.variance value := by
    rw [distribution.varianceAround_eq_variance_add_mean_sub_sq]
    ring1
  rw [varianceIdentity] at differenceInside
  exact differenceInside

/-- The centered variance-enclosure width is the deviation-enclosure width
plus the square of the explicit mean radius. -/
theorem prefixFamilyProbeCenteredVarianceBound_width
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate)
    (meanFactor : Coordinate)
    (deviationFactor : Coordinate)
    (deviationFactorNonnegative : 0 ≤ deviationFactor)
    (deviationSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe
            (prefixFamilyProbeWitnessExpectation distribution probe) 2 left)
          (poweredDeviationProbe probe
            (prefixFamilyProbeWitnessExpectation distribution probe) 2 right) ≤
        deviationFactor * CCL.Chordal.chordalSq left right) :
    (prefixFamilyProbeCenteredVarianceBound distribution probe meanFactor
      deviationFactor deviationFactorNonnegative
      deviationSensitive).width =
      (prefixFamilyProbePoweredDeviationBound distribution probe
        (prefixFamilyProbeWitnessExpectation distribution probe) 2
        deviationFactor deviationFactorNonnegative deviationSensitive).width +
      prefixFamilyProbeRadius distribution meanFactor ^ 2 := by
  unfold prefixFamilyProbeCenteredVarianceBound
  rw [_root_.FiniteMeasure.Bound.sub_width]
  change _ + (prefixFamilyProbeRadius distribution meanFactor ^ 2 - 0) = _
  ring1

/-- Two directly checkable rational half-budgets certify the requested
variance-enclosure width. -/
theorem prefixFamilyProbeCenteredVarianceBound_width_lt_of_budgets
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate)
    (meanFactor deviationFactor : Coordinate)
    (deviationFactorNonnegative : 0 ≤ deviationFactor)
    (deviationSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe
            (prefixFamilyProbeWitnessExpectation distribution probe) 2 left)
          (poweredDeviationProbe probe
            (prefixFamilyProbeWitnessExpectation distribution probe) 2 right) ≤
        deviationFactor * CCL.Chordal.chordalSq left right)
    (target : Coordinate)
    (deviationBudget :
      (prefixFamilyProbePoweredDeviationBound distribution probe
        (prefixFamilyProbeWitnessExpectation distribution probe) 2
        deviationFactor deviationFactorNonnegative deviationSensitive).width <
          target / 2)
    (meanBudget : prefixFamilyProbeRadius distribution meanFactor ^ 2 <
      target / 2) :
    (prefixFamilyProbeCenteredVarianceBound distribution probe meanFactor
      deviationFactor deviationFactorNonnegative deviationSensitive).width <
      target := by
  rw [prefixFamilyProbeCenteredVarianceBound_width]
  calc
    _ < target / 2 + target / 2 :=
      RFAP.ConstructiveFraction.add_lt_add_direct deviationBudget meanBudget
    _ = (target / 2) * 2 := by ring1
    _ = target :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 2 (by decide)

/-- Expected mean radius after appending one displayed finite suffix to every
prefix row. -/
def extendedPrefixFamilyProbeRadius
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (factor : Coordinate) : Coordinate :=
  distribution.expectation fun certificate =>
    factor * cylinderSpread (certificate.blocks ++ suffix certificate)

theorem extendedPrefixFamilyProbeRadius_nonnegative
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor) :
    0 ≤ extendedPrefixFamilyProbeRadius distribution suffix factor := by
  apply distribution.expectation_nonneg
  intro atom member
  exact RFAP.ConstructiveFraction.mul_nonneg_direct factorNonnegative
    (cylinderSpread_nonneg (atom.item.blocks ++ suffix atom.item))

/-- Appending finite suffixes cannot increase the expected mean radius. -/
theorem extendedPrefixFamilyProbeRadius_le
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor) :
    extendedPrefixFamilyProbeRadius distribution suffix factor ≤
      prefixFamilyProbeRadius distribution factor := by
  apply distribution.expectation_mono
  intro atom member
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    (cylinderSpread_le_of_append atom.item.blocks (suffix atom.item))
    factorNonnegative

/-- Squared mean-error enclosure after appending the displayed suffixes. -/
def extendedPrefixFamilyProbeMeanSquareErrorBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (factor : Coordinate) : _root_.FiniteMeasure.Bound where
  lower := 0
  upper := extendedPrefixFamilyProbeRadius distribution suffix factor ^ 2
  valid := RFAP.ConstructiveFraction.sq_nonneg_direct _

/-- The refined squared mean-error enclosure contains every realization
family of the appended prefixes. -/
theorem extendedPrefixFamilyProbeMeanSquareErrorBound_contains
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (atom.item.blocks ++ suffix atom.item) (points atom.item)) :
    (extendedPrefixFamilyProbeMeanSquareErrorBound distribution suffix factor)
      |>.Contains
        (((distribution.expectation fun certificate => probe (points certificate)) -
          prefixFamilyProbeWitnessExpectation distribution probe) ^ 2) := by
  have l1Bound : distribution.l1Distance
      (fun certificate => probe (points certificate))
      (fun certificate => probe certificate.witness) ≤
      extendedPrefixFamilyProbeRadius distribution suffix factor := by
    change distribution.expectation (fun certificate =>
        _root_.FiniteMeasure.rationalSeparation
          (probe (points certificate)) (probe certificate.witness)) ≤
      distribution.expectation fun certificate =>
        factor * cylinderSpread (certificate.blocks ++ suffix certificate)
    apply distribution.expectation_mono
    intro atom member
    exact realized_probe_separation_le (pointsRealize atom member)
      (extendedRealizes atom.item) probe factor factorNonnegative sensitive
  have separationLe :=
    (distribution.expectation_separation_le_l1Distance
      (fun certificate => probe (points certificate))
      (fun certificate => probe certificate.witness)).trans l1Bound
  have powered := RFAP.ConstructiveFraction.pow_le_pow_direct
    (_root_.FiniteMeasure.rationalSeparation_nonneg _ _) separationLe 2
  rw [_root_.FiniteMeasure.rationalSeparation_sq] at powered
  exact ⟨RFAP.ConstructiveFraction.sq_nonneg_direct _, powered⟩

/-- Appending finite suffixes narrows the squared mean-error enclosure. -/
theorem extendedPrefixFamilyProbeMeanSquareErrorBound_refines
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor) :
    _root_.FiniteMeasure.Bound.Refines
      (extendedPrefixFamilyProbeMeanSquareErrorBound distribution suffix factor)
      (prefixFamilyProbeMeanSquareErrorBound distribution factor) := by
  constructor
  · exact le_rfl
  · exact RFAP.ConstructiveFraction.pow_le_pow_direct
      (extendedPrefixFamilyProbeRadius_nonnegative distribution suffix factor
        factorNonnegative)
      (extendedPrefixFamilyProbeRadius_le distribution suffix factor
        factorNonnegative)
      2

/-- Witness-centred variance enclosure after appending one displayed suffix
to every prefix row. -/
def extendedPrefixFamilyProbeCenteredVarianceBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Proj → Coordinate) (meanFactor deviationFactor : Coordinate)
    (deviationFactorNonnegative : 0 ≤ deviationFactor)
    (deviationSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe
            (prefixFamilyProbeWitnessExpectation distribution probe) 2 left)
          (poweredDeviationProbe probe
            (prefixFamilyProbeWitnessExpectation distribution probe) 2 right) ≤
        deviationFactor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound :=
  (extendedPrefixFamilyProbeExpectationBound distribution suffix
    extendedRealizes
    (poweredDeviationProbe probe
      (prefixFamilyProbeWitnessExpectation distribution probe) 2)
    deviationFactor deviationFactorNonnegative deviationSensitive).sub
  (extendedPrefixFamilyProbeMeanSquareErrorBound distribution suffix meanFactor)

/-- Every realization family of the appended prefixes has its exact finite
variance inside the refined witness-centred enclosure. -/
theorem extendedPrefixFamilyProbeCenteredVarianceBound_contains
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        meanFactor * CCL.Chordal.chordalSq left right)
    (deviationFactor : Coordinate)
    (deviationFactorNonnegative : 0 ≤ deviationFactor)
    (deviationSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe
            (prefixFamilyProbeWitnessExpectation distribution probe) 2 left)
          (poweredDeviationProbe probe
            (prefixFamilyProbeWitnessExpectation distribution probe) 2 right) ≤
        deviationFactor * CCL.Chordal.chordalSq left right)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (atom.item.blocks ++ suffix atom.item) (points atom.item)) :
    (extendedPrefixFamilyProbeCenteredVarianceBound distribution suffix
      extendedRealizes probe meanFactor deviationFactor
      deviationFactorNonnegative deviationSensitive).Contains
      (distribution.variance fun certificate => probe (points certificate)) := by
  let center := prefixFamilyProbeWitnessExpectation distribution probe
  let value := fun certificate => probe (points certificate)
  have deviationInside :=
    extendedPrefixFamilyProbeExpectationBound_contains distribution suffix
      extendedRealizes (poweredDeviationProbe probe center 2) deviationFactor
      deviationFactorNonnegative deviationSensitive points pointsRealize
  have varianceAroundInside :
      (extendedPrefixFamilyProbeExpectationBound distribution suffix
        extendedRealizes (poweredDeviationProbe probe center 2)
        deviationFactor deviationFactorNonnegative deviationSensitive).Contains
        (distribution.varianceAround value center) := by
    rw [distribution.varianceAround_eq_poweredL2Distance_constant,
      ← distribution.poweredLpDistance_two]
    exact deviationInside
  have meanErrorInside :=
    extendedPrefixFamilyProbeMeanSquareErrorBound_contains distribution suffix
      extendedRealizes probe meanFactor meanFactorNonnegative meanSensitive
      points pointsRealize
  have differenceInside := _root_.FiniteMeasure.Bound.sub_contains
    varianceAroundInside meanErrorInside
  have varianceIdentity :
      distribution.varianceAround value center -
          (distribution.expectation value - center) ^ 2 =
        distribution.variance value := by
    rw [distribution.varianceAround_eq_variance_add_mean_sub_sq]
    ring1
  rw [varianceIdentity] at differenceInside
  exact differenceInside

/-- Appending finite suffixes narrows the complete witness-centred variance
enclosure. -/
theorem extendedPrefixFamilyProbeCenteredVarianceBound_refines
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorNonnegative : 0 ≤ meanFactor)
    (deviationFactor : Coordinate)
    (deviationFactorNonnegative : 0 ≤ deviationFactor)
    (deviationSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe
            (prefixFamilyProbeWitnessExpectation distribution probe) 2 left)
          (poweredDeviationProbe probe
            (prefixFamilyProbeWitnessExpectation distribution probe) 2 right) ≤
        deviationFactor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound.Refines
      (extendedPrefixFamilyProbeCenteredVarianceBound distribution suffix
        extendedRealizes probe meanFactor deviationFactor
        deviationFactorNonnegative deviationSensitive)
      (prefixFamilyProbeCenteredVarianceBound distribution probe meanFactor
        deviationFactor deviationFactorNonnegative deviationSensitive) := by
  apply _root_.FiniteMeasure.Bound.Refines.sub
  · exact extendedPrefixFamilyProbeExpectationBound_refines distribution
      suffix extendedRealizes
      (poweredDeviationProbe probe
        (prefixFamilyProbeWitnessExpectation distribution probe) 2)
      deviationFactor deviationFactorNonnegative deviationSensitive
  · exact extendedPrefixFamilyProbeMeanSquareErrorBound_refines distribution
      suffix meanFactor meanFactorNonnegative

end CCL.FiniteMeasure
