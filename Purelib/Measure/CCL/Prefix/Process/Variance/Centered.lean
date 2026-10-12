module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
import Purelib.Approximation.Bound.Process
import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.Observation
import Purelib.Approximation.CCL.Prefix.Sensitivity
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Process
public import Purelib.Data.Function.Rat.Distance
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Distribution.Enclosure.Basic
public import Purelib.Measure.CCL.Prefix.Process.Enclosure
import Purelib.Measure.Distribution.Moments.Lp
import Purelib.Measure.Weighted.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

open Purelib.Data.CCL.Encoding.Cylinder.Basic (Realizes)

section
public section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

namespace Purelib.Measure.CCL.Prefix

open Purelib.Data

namespace PrefixFamilyProcess

section
open Purelib
section
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Measure
/-- Enclose squared mean error between zero and the current expected probe radius squared. -/
@[expose] def probeMeanSquareErrorBound {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (factor : Fraction.Rational) (state : process.State) :
    Data.Rat.Interval where
  lower := 0
  upper := (CCL.Prefix.PrefixFamilyProcess.probeRadius process) distribution factor state ^ 2
  valid := Fraction.Order.Arithmetic.sq_nonneg_direct _

/-- Pointwise block extension refines the squared mean-error enclosure for a nonnegative factor. -/
theorem probeMeanSquareErrorBound_refines_of_extends {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    {newer older : process.State}
    (extension : ∀ item, ∃ suffix,
      process.blocks newer item = process.blocks older item ++ suffix) :
    Interval.Refines
      ((probeMeanSquareErrorBound process) distribution factor newer)
      ((probeMeanSquareErrorBound process) distribution factor older) := by
  constructor
  · exact le_rfl
  · exact Fraction.Order.Arithmetic.pow_le_pow_direct
      ((CCL.Prefix.PrefixFamilyProcess.probeRadius_nonnegative process) distribution factor factorNonnegative
        newer)
      ((CCL.Prefix.PrefixFamilyProcess.probeRadius_le_of_extends process) distribution factor factorNonnegative
        extension)
      2

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The current squared mean-error enclosure contains the squared difference from the fixed witness expectation. -/
theorem probeMeanSquareErrorBound_contains {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes (process.blocks state atom.item)
        (points atom.item)) :
    ((probeMeanSquareErrorBound process) distribution factor state).Contains
      (((distribution.expectation fun item => probe (points item)) -
        (CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) ^ 2) := by
  have l1Bound : distribution.l1Distance
      (fun item => probe (points item))
      (fun item => probe (process.witness item)) ≤
      (CCL.Prefix.PrefixFamilyProcess.probeRadius process) distribution factor state := by
    change distribution.expectation (fun item =>
        Distance.rationalSeparation
          (probe (points item)) (probe (process.witness item))) ≤
      distribution.expectation fun item =>
        factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state item)
    apply distribution.expectation_mono
    intro atom member
    exact Approximation.CCL.Prefix.realized_probe_separation_le (pointsRealize atom member)
      (process.realizes state atom.item) probe factor factorNonnegative sensitive
  have separationLe :=
    (distribution.expectation_separation_le_l1Distance
      (fun item => probe (points item))
      (fun item => probe (process.witness item))).trans l1Bound
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
/-- Subtract the squared mean-error enclosure from the enclosure of squared deviation about the fixed witness
expectation.

The mean and centered-deviation terms retain separate sensitivity factors at the same original process state and finite
law. -/
@[expose] def probeCenteredVarianceBound {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (meanFactor : Fraction.Rational)
    (deviationFactor : Fraction.Rational) (deviationFactorPositive : 0 < deviationFactor)
    (deviationSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe
            ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2 left)
          (Function.Rat.poweredDeviationProbe probe
            ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2 right) ≤
        deviationFactor * Chordal.Basic.chordalSq left right)
    (state : process.State) : Data.Rat.Interval :=
  ((process.toProbeExpectationProcess distribution
    (Function.Rat.poweredDeviationProbe probe
      ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2)
    deviationFactor deviationFactorPositive deviationSensitive).bound state).sub
  ((probeMeanSquareErrorBound process) distribution meanFactor state)

/-- The centered enclosure contains the variance of every probe family realizing the current state's blocks. -/
theorem probeCenteredVarianceBound_contains {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorPositive : 0 < meanFactor)
    (meanSensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        meanFactor * Chordal.Basic.chordalSq left right)
    (deviationFactor : Fraction.Rational) (deviationFactorPositive : 0 < deviationFactor)
    (deviationSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe
            ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2 left)
          (Function.Rat.poweredDeviationProbe probe
            ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2 right) ≤
        deviationFactor * Chordal.Basic.chordalSq left right)
    (state : process.State) (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes (process.blocks state atom.item)
        (points atom.item)) :
    ((probeCenteredVarianceBound process) distribution probe meanFactor
      deviationFactor deviationFactorPositive deviationSensitive state).Contains
      (distribution.variance fun item => probe (points item)) := by
  let center := (CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe
  let value := fun item => probe (points item)
  have deviationInside :=
    process.expectation_mem_probeExpectationProcess_bound distribution
      (Function.Rat.poweredDeviationProbe probe center 2) deviationFactor
      deviationFactorPositive deviationSensitive state points pointsRealize
  have varianceAroundInside :
      ((process.toProbeExpectationProcess distribution
        (Function.Rat.poweredDeviationProbe probe center 2) deviationFactor
        deviationFactorPositive deviationSensitive).bound state).Contains
        (distribution.varianceAround value center) := by
    rw [distribution.varianceAround_eq_poweredL2Distance_constant,
      ← distribution.poweredLpDistance_two]
    exact deviationInside
  have meanErrorInside := (probeMeanSquareErrorBound_contains process)
    distribution probe meanFactor meanFactorPositive.le meanSensitive state
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

end

open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Build a variance-enclosure process centered at the original fixed witness expectation.

Requests retain the original state type and extend to the maximum of separate deviation and mean-error block budgets;
both terms refine and their widths sum to less than epsilon. -/
@[expose] def toProbeCenteredVarianceProcess {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorPositive : 0 < meanFactor)
    (meanSensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        meanFactor * Chordal.Basic.chordalSq left right)
    (deviationFactor : Fraction.Rational) (deviationFactorPositive : 0 < deviationFactor)
    (deviationSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe
            ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2 left)
          (Function.Rat.poweredDeviationProbe probe
            ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2 right) ≤
        deviationFactor * Chordal.Basic.chordalSq left right) :
    Approximation.BoundProcess where
  State := process.State
  bound state := (probeCenteredVarianceBound process) distribution probe
    meanFactor deviationFactor deviationFactorPositive deviationSensitive state
  initial := process.initial
  request state epsilon positive :=
    process.request state (max
      (Budget.requiredProbeBlockCount (epsilon / 4) deviationFactor)
      (Budget.requiredProbeBlockCount (Budget.centeredVarianceMeanTarget epsilon) meanFactor))
  request_refines state epsilon positive := by
    apply Interval.Refines.sub
    · apply (CCL.Prefix.PrefixFamilyProcess.probeExpectationBound_refines_of_extends process) distribution
        (Function.Rat.poweredDeviationProbe probe
          ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2)
        deviationFactor deviationFactorPositive deviationSensitive
      intro item
      exact process.request_extends state _ item
    · apply (probeMeanSquareErrorBound_refines_of_extends process) distribution
        meanFactor meanFactorPositive.le
      intro item
      exact process.request_extends state _ item
  accurate state epsilon positive := by
    let deviationCount :=
      Budget.requiredProbeBlockCount (epsilon / 4) deviationFactor
    let meanTarget := Budget.centeredVarianceMeanTarget epsilon
    let meanCount := Budget.requiredProbeBlockCount meanTarget meanFactor
    let count := max deviationCount meanCount
    let requested := process.request state count
    have quarterPositive : (0 : Fraction.Rational) < epsilon / 4 :=
      Fraction.Order.Field.div_pos_direct positive (by decide)
    have halfPositive : (0 : Fraction.Rational) < epsilon / 2 :=
      Fraction.Order.Field.div_pos_direct positive (by decide)
    have deviationWidthSmall :
        ((process.toProbeExpectationProcess distribution
          (Function.Rat.poweredDeviationProbe probe
            ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2)
          deviationFactor deviationFactorPositive deviationSensitive).bound
          requested).width < epsilon / 2 := by
      apply distribution.enclosedExpectation_width_lt_of_uniform _
        (epsilon / 4) (epsilon / 2)
      · intro atom member
        exact (Approximation.CCL.Prefix.completedPrefixProbeBound_width_lt_requested
          (process.witness atom.item) (process.realizes requested atom.item)
          (Function.Rat.poweredDeviationProbe probe
            ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2)
          deviationFactor deviationFactorPositive deviationSensitive
          (epsilon / 4) quarterPositive
          ((show deviationCount ≤ count from Nat.Order.le_max_left _ _).trans
            (process.request_length state count atom.item))).le
      · exact Fraction.quarter_lt_half positive
    have meanRadiusLe :
        (CCL.Prefix.PrefixFamilyProcess.probeRadius process) distribution meanFactor requested ≤ meanTarget := by
      calc
        (CCL.Prefix.PrefixFamilyProcess.probeRadius process) distribution meanFactor requested =
            distribution.expectation (fun item =>
              meanFactor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks requested item)) :=
          rfl
        _ ≤ distribution.expectation (fun _ => meanTarget) := by
          apply distribution.expectation_mono
          intro atom member
          have widthSmall := Approximation.CCL.Prefix.completedPrefixProbeBound_width_lt_requested
            (process.witness atom.item) (process.realizes requested atom.item)
            probe meanFactor meanFactorPositive meanSensitive meanTarget
            (Budget.centeredVarianceMeanTarget_positive positive)
            ((show meanCount ≤ count from Nat.Order.le_max_right _ _).trans
              (process.request_length state count atom.item))
          have radiusNonnegative : 0 ≤ meanFactor *
              Approximation.CCL.Cylinder.cylinderSpread (process.blocks requested atom.item) :=
            Fraction.Order.Arithmetic.mul_nonneg_direct meanFactorPositive.le
              (Approximation.CCL.Cylinder.cylinderSpread_nonneg _)
          calc
            meanFactor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks requested atom.item) ≤
                2 * (meanFactor *
                  Approximation.CCL.Cylinder.cylinderSpread (process.blocks requested atom.item)) := by
              calc
                _ = 0 + meanFactor *
                    Approximation.CCL.Cylinder.cylinderSpread (process.blocks requested atom.item) := by
                  ring1
                _ ≤ meanFactor * Approximation.CCL.Cylinder.cylinderSpread
                      (process.blocks requested atom.item) +
                    meanFactor * Approximation.CCL.Cylinder.cylinderSpread
                      (process.blocks requested atom.item) :=
                  Fraction.Order.Arithmetic.add_le_add_direct
                    radiusNonnegative le_rfl
                _ = _ := by ring1
            _ = (Approximation.CCL.Prefix.completedPrefixProbeBound
                (process.blocks requested atom.item) (process.witness atom.item)
                (process.realizes requested atom.item) probe meanFactor
                meanFactorPositive.le meanSensitive).width := by
              rw [Approximation.CCL.Prefix.completedPrefixProbeBound_width]
            _ ≤ meanTarget := widthSmall.le
        _ = meanTarget := distribution.expectation_constant meanTarget
    have meanSquareSmall :
        (CCL.Prefix.PrefixFamilyProcess.probeRadius process) distribution meanFactor requested ^ 2 <
          epsilon / 2 := by
      exact (Fraction.Order.Arithmetic.pow_le_pow_direct
        ((CCL.Prefix.PrefixFamilyProcess.probeRadius_nonnegative process) distribution meanFactor
          meanFactorPositive.le requested)
        meanRadiusLe 2).trans_lt
          (Budget.centeredVarianceMeanTarget_sq_lt_half positive)
    change ((probeCenteredVarianceBound process) distribution probe meanFactor
      deviationFactor deviationFactorPositive deviationSensitive requested).width <
        epsilon
    unfold probeCenteredVarianceBound
    rw [Interval.sub_width]
    change _ + ((CCL.Prefix.PrefixFamilyProcess.probeRadius process) distribution meanFactor requested ^ 2 - 0) < _
    calc
      _ = _ + (CCL.Prefix.PrefixFamilyProcess.probeRadius process) distribution meanFactor requested ^ 2 := by
        ring1
      _ < epsilon / 2 + epsilon / 2 :=
        Fraction.Order.Arithmetic.add_lt_add_direct deviationWidthSmall
          meanSquareSmall
      _ = (epsilon / 2) * 2 := by ring1
      _ = epsilon :=
        Fraction.Field.div_mul_cancel_of_ne epsilon 2 (by decide)
  refinesInitial state := by
    apply Interval.Refines.sub
    · apply (CCL.Prefix.PrefixFamilyProcess.probeExpectationBound_refines_of_extends process) distribution
        (Function.Rat.poweredDeviationProbe probe
          ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2)
        deviationFactor deviationFactorPositive deviationSensitive
      exact process.extendsInitial state
    · apply (probeMeanSquareErrorBound_refines_of_extends process) distribution
        meanFactor meanFactorPositive.le
      exact process.extendsInitial state

open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- The centered variance process encloses every variance realized by its current retained blocks. -/
theorem variance_mem_toProbeCenteredVarianceProcess_bound {ι :
  Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorPositive : 0 < meanFactor)
    (meanSensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        meanFactor * Chordal.Basic.chordalSq left right)
    (deviationFactor : Fraction.Rational) (deviationFactorPositive : 0 < deviationFactor)
    (deviationSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe
            ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2 left)
          (Function.Rat.poweredDeviationProbe probe
            ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2 right) ≤
        deviationFactor * Chordal.Basic.chordalSq left right)
    (state : process.State) (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes (process.blocks state atom.item)
        (points atom.item)) :
    (((toProbeCenteredVarianceProcess process) distribution probe meanFactor
      meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
      deviationSensitive).bound state).Contains
        (distribution.variance fun item => probe (points item)) :=
  (probeCenteredVarianceBound_contains process) distribution probe meanFactor
    meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
    deviationSensitive state points pointsRealize

/-- The requested centered variance enclosure is narrower than the positive epsilon. -/
theorem request_probeCenteredVariance_width_lt {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorPositive : 0 < meanFactor)
    (meanSensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        meanFactor * Chordal.Basic.chordalSq left right)
    (deviationFactor : Fraction.Rational) (deviationFactorPositive : 0 < deviationFactor)
    (deviationSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe
            ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2 left)
          (Function.Rat.poweredDeviationProbe probe
            ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2 right) ≤
        deviationFactor * Chordal.Basic.chordalSq left right)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (((toProbeCenteredVarianceProcess process) distribution probe meanFactor
      meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
      deviationSensitive).bound
      (((toProbeCenteredVarianceProcess process) distribution probe meanFactor
        meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
        deviationSensitive).request state epsilon positive)).width < epsilon :=
  ((toProbeCenteredVarianceProcess process) distribution probe meanFactor
    meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
    deviationSensitive).accurate state epsilon positive

/-- Two probe families realizing the requested blocks have both directed variance differences strictly below epsilon. -/
theorem request_realizedVariances_pairwise_difference_lt {ι :
  Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorPositive : 0 < meanFactor)
    (meanSensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        meanFactor * Chordal.Basic.chordalSq left right)
    (deviationFactor : Fraction.Rational) (deviationFactorPositive : 0 < deviationFactor)
    (deviationSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe
            ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2 left)
          (Function.Rat.poweredDeviationProbe probe
            ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2 right) ≤
        deviationFactor * Chordal.Basic.chordalSq left right)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (leftPoints rightPoints : ι → Line.GaussianLine)
    (leftRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes
        (process.blocks
          (((toProbeCenteredVarianceProcess process) distribution probe
            meanFactor meanFactorPositive meanSensitive deviationFactor
            deviationFactorPositive deviationSensitive).request state epsilon
              positive) atom.item)
        (leftPoints atom.item))
    (rightRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes
        (process.blocks
          (((toProbeCenteredVarianceProcess process) distribution probe
            meanFactor meanFactorPositive meanSensitive deviationFactor
            deviationFactorPositive deviationSensitive).request state epsilon
              positive) atom.item)
        (rightPoints atom.item)) :
    distribution.variance (fun item => probe (leftPoints item)) -
          distribution.variance (fun item => probe (rightPoints item)) < epsilon ∧
      distribution.variance (fun item => probe (rightPoints item)) -
          distribution.variance (fun item => probe (leftPoints item)) < epsilon := by
  let varianceProcess := (toProbeCenteredVarianceProcess process) distribution
    probe meanFactor meanFactorPositive meanSensitive deviationFactor
      deviationFactorPositive deviationSensitive
  apply varianceProcess.request_pairwise_difference_lt state epsilon positive
  · exact (variance_mem_toProbeCenteredVarianceProcess_bound process)
      distribution probe meanFactor meanFactorPositive meanSensitive
      deviationFactor deviationFactorPositive deviationSensitive
      (varianceProcess.request state epsilon positive) leftPoints leftRealize
  · exact (variance_mem_toProbeCenteredVarianceProcess_bound process)
      distribution probe meanFactor meanFactorPositive meanSensitive
      deviationFactor deviationFactorPositive deviationSensitive
      (varianceProcess.request state epsilon positive) rightPoints rightRealize

end

end PrefixFamilyProcess

end Purelib.Measure.CCL.Prefix

end
