module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Power
import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic

import Purelib.Approximation.CCL.Prefix.Sensitivity
import Purelib.CCL.Measure.Basic
import Purelib.Data.Function.Rat.Distance
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.CCL.Prefix.Deviation.Enclosure
import Purelib.Measure.CCL.Prefix.Enclosure
import Purelib.Measure.CCL.Prefix.Stability
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Moments.Lp
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.CCL.Encoding (Block)
open Purelib.Data.CCL.Encoding.Cylinder.Basic (Realizes)

section
@[expose] public section

/-!
# Witness-centred variance enclosures from finite CCL prefixes

The displayed prefix witnesses have an exact rational probe expectation.
Variance around that computable centre differs from the true finite variance
by exactly the square of the mean error.  A powered-deviation enclosure and
the explicit prefix mean radius therefore give a direct rational variance
enclosure without squaring a signed mean interval.
-/

namespace Purelib.Measure.CCL.Prefix

section
open Purelib
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- Enclose squared mean error between zero and the original expected probe radius squared. -/
def prefixFamilyProbeMeanSquareErrorBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (factor : Fraction.Rational) : Data.Rat.Interval where
  lower := 0
  upper := CCL.Prefix.prefixFamilyProbeRadius distribution factor ^ 2
  valid := Fraction.Order.Arithmetic.sq_nonneg_direct _

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The squared mean-error enclosure contains the squared difference from the retained witness expectation. -/
theorem prefixFamilyProbeMeanSquareErrorBound_contains
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (points atom.item)) :
    (prefixFamilyProbeMeanSquareErrorBound distribution factor).Contains
      (((distribution.expectation fun certificate => probe (points certificate)) -
        CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) ^ 2) := by
  have separationLe :=
    CCL.Prefix.prefixFamilyProbe_expectation_separation_witness_le distribution probe
      factor factorNonnegative sensitive points pointsRealize
  have powered := Fraction.Order.Arithmetic.pow_le_pow_direct
    (Distance.rationalSeparation_nonneg _ _) separationLe 2
  rw [Distance.NaturalLp.rationalSeparation_sq] at powered
  exact ⟨Fraction.Order.Arithmetic.sq_nonneg_direct _, powered⟩

section
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Enclose variance using squared deviation about the retained witness mean minus squared mean error.

The same original certificate distribution supplies both terms, with separate mean and centered-deviation sensitivity
factors. -/
def prefixFamilyProbeCenteredVarianceBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational)
    (meanFactor : Fraction.Rational)
    (deviationFactor : Fraction.Rational)
    (deviationFactorNonnegative : 0 ≤ deviationFactor)
    (deviationSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe
            (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2 left)
          (Function.Rat.poweredDeviationProbe probe
            (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2 right) ≤
        deviationFactor * Chordal.Basic.chordalSq left right) :
    Data.Rat.Interval :=
  (CCL.Prefix.prefixFamilyProbePoweredDeviationBound distribution probe
    (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2
    deviationFactor deviationFactorNonnegative deviationSensitive).sub
  (prefixFamilyProbeMeanSquareErrorBound distribution meanFactor)

/-- The centered variance enclosure contains every probe variance realized by the retained prefixes. -/
theorem prefixFamilyProbeCenteredVarianceBound_contains
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        meanFactor * Chordal.Basic.chordalSq left right)
    (deviationFactor : Fraction.Rational)
    (deviationFactorNonnegative : 0 ≤ deviationFactor)
    (deviationSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe
            (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2 left)
          (Function.Rat.poweredDeviationProbe probe
            (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2 right) ≤
        deviationFactor * Chordal.Basic.chordalSq left right)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (points atom.item)) :
    (prefixFamilyProbeCenteredVarianceBound distribution probe meanFactor
      deviationFactor deviationFactorNonnegative
      deviationSensitive).Contains
      (distribution.variance fun certificate => probe (points certificate)) := by
  let center := CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe
  let value := fun certificate => probe (points certificate)
  have deviationInside :=
    CCL.Prefix.prefixFamilyProbePoweredDeviationBound_contains distribution probe center 2
      deviationFactor deviationFactorNonnegative deviationSensitive points
      pointsRealize
  have varianceAroundInside :
      (CCL.Prefix.prefixFamilyProbePoweredDeviationBound distribution probe center 2
        deviationFactor deviationFactorNonnegative deviationSensitive).Contains
        (distribution.varianceAround value center) := by
    rw [distribution.varianceAround_eq_poweredL2Distance_constant,
      ← distribution.poweredLpDistance_two]
    exact deviationInside
  have meanErrorInside :=
    prefixFamilyProbeMeanSquareErrorBound_contains distribution probe
      meanFactor meanFactorNonnegative meanSensitive points pointsRealize
  have differenceInside := Interval.sub_contains
    varianceAroundInside meanErrorInside
  have varianceIdentity :
      distribution.varianceAround value center -
          (distribution.expectation value - center) ^ 2 =
        distribution.variance value := by
    rw [distribution.varianceAround_eq_variance_add_mean_sub_sq]
    ring1
  rw [varianceIdentity] at differenceInside
  exact differenceInside

/-- Centered variance width equals the deviation enclosure's width plus the expected mean radius squared. -/
theorem prefixFamilyProbeCenteredVarianceBound_width
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational)
    (meanFactor : Fraction.Rational)
    (deviationFactor : Fraction.Rational)
    (deviationFactorNonnegative : 0 ≤ deviationFactor)
    (deviationSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe
            (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2 left)
          (Function.Rat.poweredDeviationProbe probe
            (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2 right) ≤
        deviationFactor * Chordal.Basic.chordalSq left right) :
    (prefixFamilyProbeCenteredVarianceBound distribution probe meanFactor
      deviationFactor deviationFactorNonnegative
      deviationSensitive).width =
      (CCL.Prefix.prefixFamilyProbePoweredDeviationBound distribution probe
        (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2
        deviationFactor deviationFactorNonnegative deviationSensitive).width +
      CCL.Prefix.prefixFamilyProbeRadius distribution meanFactor ^ 2 := by
  unfold prefixFamilyProbeCenteredVarianceBound
  rw [Interval.sub_width]
  change _ + (CCL.Prefix.prefixFamilyProbeRadius distribution meanFactor ^ 2 - 0) = _
  ring1

/-- Separate strict half-target deviation and squared-mean budgets make the variance enclosure narrower than the target.
-/
theorem prefixFamilyProbeCenteredVarianceBound_width_lt_of_budgets
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational)
    (meanFactor deviationFactor : Fraction.Rational)
    (deviationFactorNonnegative : 0 ≤ deviationFactor)
    (deviationSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe
            (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2 left)
          (Function.Rat.poweredDeviationProbe probe
            (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2 right) ≤
        deviationFactor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational)
    (deviationBudget :
      (CCL.Prefix.prefixFamilyProbePoweredDeviationBound distribution probe
        (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2
        deviationFactor deviationFactorNonnegative deviationSensitive).width <
          target / 2)
    (meanBudget : CCL.Prefix.prefixFamilyProbeRadius distribution meanFactor ^ 2 <
      target / 2) :
    (prefixFamilyProbeCenteredVarianceBound distribution probe meanFactor
      deviationFactor deviationFactorNonnegative deviationSensitive).width <
      target := by
  rw [prefixFamilyProbeCenteredVarianceBound_width]
  calc
    _ < target / 2 + target / 2 :=
      Fraction.Order.Arithmetic.add_lt_add_direct deviationBudget meanBudget
    _ = (target / 2) * 2 := by ring1
    _ = target :=
      Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- Enclose squared mean error using the expected radius after the retained suffix extensions. -/
def extendedPrefixFamilyProbeMeanSquareErrorBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (factor : Fraction.Rational) : Data.Rat.Interval where
  lower := 0
  upper := CCL.Prefix.extendedPrefixFamilyProbeRadius distribution suffix factor ^ 2
  valid := Fraction.Order.Arithmetic.sq_nonneg_direct _

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The extended squared mean-error enclosure contains the squared expectation difference for every extended-prefix
realization. -/
theorem extendedPrefixFamilyProbeMeanSquareErrorBound_contains
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes
        (atom.item.blocks ++ suffix atom.item) (points atom.item)) :
    (extendedPrefixFamilyProbeMeanSquareErrorBound distribution suffix factor)
      |>.Contains
        (((distribution.expectation fun certificate => probe (points certificate)) -
          CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) ^ 2) := by
  have l1Bound : distribution.l1Distance
      (fun certificate => probe (points certificate))
      (fun certificate => probe certificate.witness) ≤
      CCL.Prefix.extendedPrefixFamilyProbeRadius distribution suffix factor := by
    change distribution.expectation (fun certificate =>
        Distance.rationalSeparation
          (probe (points certificate)) (probe certificate.witness)) ≤
      distribution.expectation fun certificate =>
        factor * Approximation.CCL.Cylinder.cylinderSpread (certificate.blocks ++ suffix certificate)
    apply distribution.expectation_mono
    intro atom member
    exact Approximation.CCL.Prefix.realized_probe_separation_le (pointsRealize atom member)
      (extendedRealizes atom.item) probe factor factorNonnegative sensitive
  have separationLe :=
    (distribution.expectation_separation_le_l1Distance
      (fun certificate => probe (points certificate))
      (fun certificate => probe certificate.witness)).trans l1Bound
  have powered := Fraction.Order.Arithmetic.pow_le_pow_direct
    (Distance.rationalSeparation_nonneg _ _) separationLe 2
  rw [Distance.NaturalLp.rationalSeparation_sq] at powered
  exact ⟨Fraction.Order.Arithmetic.sq_nonneg_direct _, powered⟩

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- Suffix extension refines the squared mean-error enclosure for a nonnegative sensitivity factor. -/
theorem extendedPrefixFamilyProbeMeanSquareErrorBound_refines
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor) :
    Interval.Refines
      (extendedPrefixFamilyProbeMeanSquareErrorBound distribution suffix factor)
      (prefixFamilyProbeMeanSquareErrorBound distribution factor) := by
  constructor
  · exact le_rfl
  · exact Fraction.Order.Arithmetic.pow_le_pow_direct
      (CCL.Prefix.extendedPrefixFamilyProbeRadius_nonnegative distribution suffix factor
        factorNonnegative)
      (CCL.Prefix.extendedPrefixFamilyProbeRadius_le distribution suffix factor
        factorNonnegative)
      2

open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Construct the centered variance enclosure after suffix extension while retaining the original witness mean. -/
def extendedPrefixFamilyProbeCenteredVarianceBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine → Fraction.Rational) (meanFactor deviationFactor :
      Fraction.Rational)
    (deviationFactorNonnegative : 0 ≤ deviationFactor)
    (deviationSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe
            (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2 left)
          (Function.Rat.poweredDeviationProbe probe
            (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2 right) ≤
        deviationFactor * Chordal.Basic.chordalSq left right) :
    Data.Rat.Interval :=
  (CCL.Prefix.extendedPrefixFamilyProbeExpectationBound distribution suffix
    extendedRealizes
    (Function.Rat.poweredDeviationProbe probe
      (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2)
    deviationFactor deviationFactorNonnegative deviationSensitive).sub
  (extendedPrefixFamilyProbeMeanSquareErrorBound distribution suffix meanFactor)

/-- The extended centered enclosure contains the variance of every realization of the exact extended blocks. -/
theorem extendedPrefixFamilyProbeCenteredVarianceBound_contains
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine → Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        meanFactor * Chordal.Basic.chordalSq left right)
    (deviationFactor : Fraction.Rational)
    (deviationFactorNonnegative : 0 ≤ deviationFactor)
    (deviationSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe
            (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2 left)
          (Function.Rat.poweredDeviationProbe probe
            (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2 right) ≤
        deviationFactor * Chordal.Basic.chordalSq left right)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes
        (atom.item.blocks ++ suffix atom.item) (points atom.item)) :
    (extendedPrefixFamilyProbeCenteredVarianceBound distribution suffix
      extendedRealizes probe meanFactor deviationFactor
      deviationFactorNonnegative deviationSensitive).Contains
      (distribution.variance fun certificate => probe (points certificate)) := by
  let center := CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe
  let value := fun certificate => probe (points certificate)
  have deviationInside :=
    CCL.Prefix.extendedPrefixFamilyProbeExpectationBound_contains distribution suffix
      extendedRealizes (Function.Rat.poweredDeviationProbe probe center 2) deviationFactor
      deviationFactorNonnegative deviationSensitive points pointsRealize
  have varianceAroundInside :
      (CCL.Prefix.extendedPrefixFamilyProbeExpectationBound distribution suffix
        extendedRealizes (Function.Rat.poweredDeviationProbe probe center 2)
        deviationFactor deviationFactorNonnegative deviationSensitive).Contains
        (distribution.varianceAround value center) := by
    rw [distribution.varianceAround_eq_poweredL2Distance_constant,
      ← distribution.poweredLpDistance_two]
    exact deviationInside
  have meanErrorInside :=
    extendedPrefixFamilyProbeMeanSquareErrorBound_contains distribution suffix
      extendedRealizes probe meanFactor meanFactorNonnegative meanSensitive
      points pointsRealize
  have differenceInside := Interval.sub_contains
    varianceAroundInside meanErrorInside
  have varianceIdentity :
      distribution.varianceAround value center -
          (distribution.expectation value - center) ^ 2 =
        distribution.variance value := by
    rw [distribution.varianceAround_eq_variance_add_mean_sub_sq]
    ring1
  rw [varianceIdentity] at differenceInside
  exact differenceInside

/-- Suffix extension refines both terms of the original centered variance enclosure. -/
theorem extendedPrefixFamilyProbeCenteredVarianceBound_refines
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine → Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorNonnegative : 0 ≤ meanFactor)
    (deviationFactor : Fraction.Rational)
    (deviationFactorNonnegative : 0 ≤ deviationFactor)
    (deviationSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe
            (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2 left)
          (Function.Rat.poweredDeviationProbe probe
            (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2 right) ≤
        deviationFactor * Chordal.Basic.chordalSq left right) :
    Interval.Refines
      (extendedPrefixFamilyProbeCenteredVarianceBound distribution suffix
        extendedRealizes probe meanFactor deviationFactor
        deviationFactorNonnegative deviationSensitive)
      (prefixFamilyProbeCenteredVarianceBound distribution probe meanFactor
        deviationFactor deviationFactorNonnegative deviationSensitive) := by
  apply Interval.Refines.sub
  · exact CCL.Prefix.extendedPrefixFamilyProbeExpectationBound_refines distribution
      suffix extendedRealizes
      (Function.Rat.poweredDeviationProbe probe
        (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) 2)
      deviationFactor deviationFactorNonnegative deviationSensitive
  · exact extendedPrefixFamilyProbeMeanSquareErrorBound_refines distribution
      suffix meanFactor meanFactorNonnegative

end

end Purelib.Measure.CCL.Prefix

end
