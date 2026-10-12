module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
public import Purelib.Approximation.Bound.Process
import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.Observation
public import Purelib.Approximation.CCL.Prefix.Process
import Purelib.Approximation.CCL.Prefix.Threshold
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Process
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Classified.Threshold
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Distribution.Enclosure.Threshold
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

open Purelib.Data.CCL.Encoding.Cylinder.Basic (Realizes)

section
@[expose] public section

/-!
# Progressive threshold probabilities from finite CCL prefixes

A lower-threshold event can be decided after one finite prefix request when
each displayed witness probe has an explicit positive rational margin from
the threshold.  The requested completed-block count makes every current
probe enclosure narrower than that margin, so every finite row is classified
and the resulting probability enclosure has width zero.  No eventual CCL
point or infinite refinement sequence is introduced.
-/

namespace Purelib.Measure.CCL.Prefix
namespace PrefixFamilyProcess

open Purelib in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Enclose threshold probability by classifying probe ranges at the supplied original process state. -/
def probeThresholdBound {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : Fraction.Rational) (state : process.State) :
    Data.Rat.Interval :=
  Measure.eventBound
    (distribution.thresholdFrontier
      ((Approximation.CCL.Prefix.PrefixFamilyProcess.probeRange process) probe factor factorNonnegative sensitive state)
      threshold)

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- The margin-based block request resolves the threshold for each original atom separated from it by the retained
positive margin. -/
private theorem requestedProbeThresholdResolved {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe (process.witness atom.item) ∨
        probe (process.witness atom.item) + margin ≤ threshold)
    (state : process.State) (atom : Measure.Weighted ι)
    (member : atom ∈ distribution.atoms) :
    Measure.ThresholdResolved
      ((Approximation.CCL.Prefix.PrefixFamilyProcess.probeRange process) probe factor factorPositive.le sensitive
        (process.request state (Budget.requiredProbeBlockCount margin factor))
        atom.item)
      threshold := by
  unfold Approximation.CCL.Prefix.PrefixFamilyProcess.probeRange
  exact Approximation.CCL.Prefix.completedPrefixProbeBound_thresholdResolved_of_margin
    (process.witness atom.item)
    (process.realizes
      (process.request state (Budget.requiredProbeBlockCount margin factor))
      atom.item)
    probe factor factorPositive sensitive threshold margin marginPositive
    (separated atom member)
    (process.request_length state
      (Budget.requiredProbeBlockCount margin factor) atom.item)

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Build a threshold-probability process from witnesses uniformly separated from the threshold.

Every positive-width request extends the original state to the fixed margin budget, resolving every retained atom and
producing an exact zero-width probability interval. -/
def toProbeThresholdProcess {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe (process.witness atom.item) ∨
        probe (process.witness atom.item) + margin ≤ threshold) :
    Approximation.BoundProcess where
  State := process.State
  bound state := (probeThresholdBound process) distribution probe factor
    factorPositive.le sensitive threshold state
  initial := process.initial
  request state epsilon positive :=
    process.request state (Budget.requiredProbeBlockCount margin factor)
  request_refines state epsilon positive := by
    unfold probeThresholdBound
    apply distribution.thresholdFrontier_eventBound_refines
    intro atom member
    rcases process.request_extends state
      (Budget.requiredProbeBlockCount margin factor) atom.item with
      ⟨suffix, equal⟩
    unfold Approximation.CCL.Prefix.PrefixFamilyProcess.probeRange
    have spreadLe :
        Approximation.CCL.Cylinder.cylinderSpread
            (process.blocks
              (process.request state
                (Budget.requiredProbeBlockCount margin factor)) atom.item) ≤
          Approximation.CCL.Cylinder.cylinderSpread (process.blocks state atom.item) := by
      rw [equal]
      exact Approximation.CCL.Cylinder.cylinderSpread_le_of_append
        (process.blocks state atom.item) suffix
    have scaledLe :
        factor * Approximation.CCL.Cylinder.cylinderSpread
            (process.blocks
              (process.request state
                (Budget.requiredProbeBlockCount margin factor)) atom.item) ≤
          factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state atom.item) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        spreadLe factorPositive.le
    constructor
    · exact Fraction.Order.Arithmetic.sub_le_sub_left_direct scaledLe (probe (process.witness atom.item))
    · exact Fraction.Order.Arithmetic.add_le_add_direct le_rfl scaledLe
  accurate state epsilon positive := by
    unfold probeThresholdBound
    rw [distribution.thresholdFrontier_width_eq_zero_of_resolved]
    · exact positive
    · intro atom member
      exact (requestedProbeThresholdResolved process) distribution probe factor
        factorPositive sensitive threshold margin marginPositive separated
        state atom member
  refinesInitial state := by
    unfold probeThresholdBound
    apply distribution.thresholdFrontier_eventBound_refines
    intro atom member
    rcases process.extendsInitial state atom.item with ⟨suffix, equal⟩
    unfold Approximation.CCL.Prefix.PrefixFamilyProcess.probeRange
    have spreadLe : Approximation.CCL.Cylinder.cylinderSpread (process.blocks state atom.item) ≤
        Approximation.CCL.Cylinder.cylinderSpread (process.blocks process.initial atom.item) := by
      rw [equal]
      exact Approximation.CCL.Cylinder.cylinderSpread_le_of_append
        (process.blocks process.initial atom.item) suffix
    have scaledLe : factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state atom.item) ≤
        factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks process.initial atom.item) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        spreadLe factorPositive.le
    constructor
    · exact Fraction.Order.Arithmetic.sub_le_sub_left_direct scaledLe (probe (process.witness atom.item))
    · exact Fraction.Order.Arithmetic.add_le_add_direct le_rfl scaledLe

open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Every requested threshold enclosure has zero width under the retained witness margin. -/
theorem request_probeThreshold_width_eq_zero {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe (process.witness atom.item) ∨
        probe (process.witness atom.item) + margin ≤ threshold)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (((toProbeThresholdProcess process) distribution probe factor factorPositive
      sensitive threshold margin marginPositive separated).bound
      (((toProbeThresholdProcess process) distribution probe factor
        factorPositive sensitive threshold margin marginPositive separated)
        |>.request state epsilon positive)).width = 0 := by
  unfold toProbeThresholdProcess probeThresholdBound
  apply distribution.thresholdFrontier_width_eq_zero_of_resolved
  intro atom member
  exact (requestedProbeThresholdResolved process) distribution probe factor
    factorPositive sensitive threshold margin marginPositive separated
    state atom member

/-- The current threshold enclosure contains the event probability of any family realizing the current blocks. -/
theorem probability_mem_toProbeThresholdProcess_bound {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe (process.witness atom.item) ∨
        probe (process.witness atom.item) + margin ≤ threshold)
    (state : process.State) (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes (process.blocks state atom.item)
        (points atom.item)) :
    (((toProbeThresholdProcess process) distribution probe factor factorPositive
      sensitive threshold margin marginPositive separated).bound state).Contains
      (distribution.probability
        (Measure.atLeastEvent threshold fun item =>
          probe (points item))) := by
  unfold toProbeThresholdProcess probeThresholdBound
  apply distribution.probability_mem_thresholdFrontier
  intro atom member
  unfold Approximation.CCL.Prefix.PrefixFamilyProcess.probeRange
  exact Approximation.CCL.Prefix.completedPrefixProbeBound_contains
    (process.blocks state atom.item) (process.witness atom.item)
    (process.realizes state atom.item) probe factor factorPositive.le sensitive
    (pointsRealize atom member)

/-- Any two families realizing the requested threshold state have exactly equal threshold-event probabilities. -/
theorem request_probeThreshold_probabilities_eq {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe (process.witness atom.item) ∨
        probe (process.witness atom.item) + margin ≤ threshold)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (leftPoints rightPoints : ι → Line.GaussianLine)
    (leftRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes
        (process.blocks
          (((toProbeThresholdProcess process) distribution probe factor
            factorPositive sensitive threshold margin marginPositive separated)
            |>.request state epsilon positive) atom.item)
        (leftPoints atom.item))
    (rightRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes
        (process.blocks
          (((toProbeThresholdProcess process) distribution probe factor
            factorPositive sensitive threshold margin marginPositive separated)
            |>.request state epsilon positive) atom.item)
        (rightPoints atom.item)) :
    distribution.probability
        (Measure.atLeastEvent threshold fun item =>
          probe (leftPoints item)) =
      distribution.probability
        (Measure.atLeastEvent threshold fun item =>
          probe (rightPoints item)) := by
  let thresholdProcess := (toProbeThresholdProcess process) distribution probe
    factor factorPositive sensitive threshold margin marginPositive separated
  let requested := thresholdProcess.request state epsilon positive
  apply Interval.eq_of_contains_of_contains_of_width_eq_zero
    (bound := thresholdProcess.bound requested)
  · exact (probability_mem_toProbeThresholdProcess_bound process) distribution
      probe factor factorPositive sensitive threshold margin marginPositive
      separated requested leftPoints leftRealize
  · exact (probability_mem_toProbeThresholdProcess_bound process) distribution
      probe factor factorPositive sensitive threshold margin marginPositive
      separated requested rightPoints rightRealize
  · exact (request_probeThreshold_width_eq_zero process) distribution probe
      factor factorPositive sensitive threshold margin marginPositive separated
      state epsilon positive

end PrefixFamilyProcess

end Purelib.Measure.CCL.Prefix

end
