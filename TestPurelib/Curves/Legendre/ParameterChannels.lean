module

import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Roots.Sampling
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Roots.Sampling.Jet
import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling
import Purelib.Curves.Legendre.PicardFuchs.Polynomials
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Coordinates
import Purelib.Approximation.Gaussian.Name.Coherent.Transport
import Purelib.Data.Fin.Two
import Purelib.Data.Rat.Fraction.Cast

/-! # Original parallel sources and their fixed-spatial-point parameter channels

Both labelled circuits supply their actual retained quarter-source lifts.
The parameter move keeps each original spatial point and complete cofactor
certificate. Its normalized owner, cubic square and operational comparisons
are constructed internally. At the first seam, exact coordinate readbacks
check the changed radicand on the original spatial point.
The scalar jet consumes the identical cached pair on every quarter, retaining
both complete observations, original states, sampling indices and fixed-point
curve residuals without requesting either cubic root again.
-/

namespace TestPurelib.Curves.Legendre.ParameterChannels

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter

open Purelib
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation

/-- The original regular parameter one eighth from each labelled collision. -/
private def parameter (site : Fin 2) : Canonical := Degeneration.criticalValue site + (1 / 8 : Canonical)

/-- Both original source parameters are intrinsically regular at their labelled collision. -/
private theorem regular (site : Fin 2) : parameter site ≠ Degeneration.criticalValue site := by
  rcases Data.Fin.Two.finTwo_cases site with equal | equal
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- Both source parameters pay the computed radial-family admission. -/
private theorem radius (site : Fin 2) :
    Norm.Basic.normSq (parameter site - Degeneration.criticalValue site) ≤ (1 / 64 : Fraction.Rational) := by
  rcases Data.Fin.Two.finTwo_cases site with equal | equal
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- The nonzero displayed move pays the internally computed fixed-source increment bound at either site. -/
private theorem admitted (site : Fin 2) : Radial.Parameter.IncrementBound site (parameter site) (1 / 256) := by
  unfold Radial.Parameter.IncrementBound
  rcases Data.Fin.Two.finTwo_cases site with equal | equal
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- Construct the actual original circuit with all four prepared source and finish owners. -/
private def circuit (site : Fin 2) : Radial.Transport.Circuit site (parameter site) :=
  Radial.Transport.Circuit.build site (parameter site) (regular site) (radius site)

attribute [local irreducible] circuit

/-- Seed the known normalized root of the identical cached source lift from each original quarter. -/
private def anchor (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Radial.Parameter.Anchor ((circuit site).leg quarter).source.lift :=
  Radial.Parameter.Anchor.build ((circuit site).leg quarter).source.lift (regular site) (radius site)

attribute [local irreducible] anchor

/-- Advance the normalized root on the original source spatial point, retaining that source's full cofactor cache. -/
private def step (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Radial.Parameter.Step (anchor site quarter) (1 / 256) :=
  Radial.Parameter.Step.build (anchor site quarter) (1 / 256) (admitted site)

attribute [local irreducible] step

/-- Every moved channel retains the identical complete original source cofactor certificate. -/
theorem target_unitRoot (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (step site quarter).channels.unitRoot = ((circuit site).leg quarter).source.lift.unitRoot :=
  (step site quarter).channels_unitRoot

/-- The actual fixed-point target cube has the original changed-parameter curve square. -/
def target_square (site : Fin 2) (quarter : UnitCircuitQuarter) :
    NamedEquivalent ((step site quarter).value.mul (step site quarter).value).name
      (Named.exact ((Paths.polynomial (parameter site + (1 / 256))).eval
        (Radial.Parameter.sourcePoint site (parameter site) (Waist.direction quarter 0)).base)) :=
  (step site quarter).square

/-- The retained known-root source channel agrees with the actual original transported source cube. -/
def source_agrees (site : Fin 2) (quarter : UnitCircuitQuarter) :
    NamedEquivalent (anchor site quarter).sourceValue.name ((circuit site).leg quarter).source.lift.value.name :=
  (anchor site quarter).source_agrees

/-- The original target forward ordinate agrees with the actual advanced normalized-root channel. -/
def target_normalized_agrees (site : Fin 2) (quarter : UnitCircuitQuarter) :
    NamedEquivalent (step site quarter).channels.ordinate.name (step site quarter).root.value.name :=
  (step site quarter).normalized_agrees

/-- The actual target normalized owner remains inside the original source seed box. -/
theorem target_refines (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (step site quarter).target.track.initial.box.Refines (anchor site quarter).seed.owner.track.initial.box :=
  (step site quarter).target_refines

/-- The original first-quarter source has the exact retained unit direction one. -/
private theorem first_direction : (Waist.direction .first 0).value = (1 : Canonical) := by
  rewrite [Waist.direction_value, Stereographic.unitQuarterPoint_zero]
  decide +kernel

/-- The original source spatial coordinate stays nine sixty-fourths from its labelled collision. -/
theorem first_source_base (site : Fin 2) :
    (Radial.Parameter.sourcePoint site (parameter site) (Waist.direction .first 0)).base =
      Degeneration.criticalValue site + (9 / 64 : Canonical) := by
  unfold Radial.Parameter.sourcePoint
  rewrite [Radial.point_base, first_direction]
  rcases Data.Fin.Two.finTwo_cases site with equal | equal
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- The original first source has the nonzero normalized ordinate three sixty-fourths. -/
theorem first_source_ordinate (site : Fin 2) :
    (Radial.Parameter.sourcePoint site (parameter site) (Waist.direction .first 0)).ordinate =
      (3 / 64 : Canonical) := by
  unfold Radial.Parameter.sourcePoint
  rewrite [Radial.point_ordinate]
  unfold Radial.ordinateDirection
  rewrite [first_direction]
  rcases Data.Fin.Two.finTwo_cases site with equal | equal
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- The changed normalized square is computed at the original source coordinate, rather than a new radial point. -/
theorem first_target_radicand (site : Fin 2) :
    Radial.Parameter.radicand site (parameter site) (Waist.direction .first 0) (1 / 256) =
      (⟨27 / Fraction.Cast.fromInt 16384, 0⟩ : Canonical) := by
  unfold Radial.Parameter.radicand Radial.Parameter.branchFactor
  rewrite [first_source_base, first_source_ordinate]
  rcases Data.Fin.Two.finTwo_cases site with equal | equal
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- Both original full-cubic certificates consume the identical supplied geometric source preparation. -/
private def roots (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Radial.Parameter.Roots (step site quarter) ((circuit site).leg quarter).sourcePrepared :=
  Radial.Parameter.Roots.build (step site quarter) ((circuit site).leg quarter).sourcePrepared

attribute [local irreducible] roots

/-- The original fixed-point move determines the shared positive fourth-order residual request. -/
private def accuracy : AccuracyRequest :=
  Periods.Jets.Variation.Sampling.incrementRequest (1 / 256) (by decide +kernel)

/-- Select the two actual full-root observations with internally paid original source and target factor states. -/
private def observations (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Roots.Sampling.Pair (roots site quarter) accuracy accuracy :=
  Roots.Sampling.request (roots site quarter) accuracy accuracy

attribute [local irreducible] observations

/-- The full source certificate retains the exact original preparation's denominator cache. -/
theorem source_preparation (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (roots site quarter).sourceRoot.value = ((circuit site).leg quarter).sourcePrepared.denominator :=
  (roots site quarter).source_value

/-- Every pair of actual prepared full-root candidates pays the internally derived positive signed sum floor. -/
theorem candidate_sum (site : Fin 2) (quarter : UnitCircuitQuarter) {first last : Canonical}
    (firstPossible : (observations site quarter).source.observation.Possible first)
    (lastPossible : (observations site quarter).target.observation.Possible last) :
    Roots.Sampling.sumFloor (anchor site quarter) / 4 ≤ Norm.Basic.normSq (first + last) :=
  (observations site quarter).sum_normSq_lower firstPossible lastPossible

/-- The actual selected full-cubic witnesses retain that same internally paid geometric sum margin. -/
theorem reading_sum (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Roots.Sampling.sumFloor (anchor site quarter) / 4 ≤
      Norm.Basic.normSq ((observations site quarter).source.reading + (observations site quarter).target.reading) :=
  (observations site quarter).reading_sum_normSq_lower

/-- The full-cubic sum floor is strictly positive at every original source of both labelled circuits. -/
theorem sum_positive (site : Fin 2) (quarter : UnitCircuitQuarter) :
    0 < Roots.Sampling.sumFloor (anchor site quarter) / 4 :=
  (observations site quarter).sumFloor_positive

/-- Construct one sampled scalar core from the identical cached pair and unchanged fourth-order request. -/
private def jet (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Roots.Sampling.Jet.Core (roots site quarter) :=
  Roots.Sampling.Jet.ofPair (observations site quarter) rfl

attribute [local irreducible] jet

/-- The scalar core uses the identical original shared residual request on all eight quarter sources. -/
theorem jet_accuracy (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (jet site quarter).accuracy = accuracy := by
  unfold jet
  exact Roots.Sampling.Jet.ofPair_accuracy (observations site quarter) rfl

/-- Dense-curve reindexing keeps the exact supplied geometric source preparation's complete value cache. -/
theorem jet_source_preparation (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (Roots.Sampling.Jet.sourceRoot (roots site quarter)).value =
      ((circuit site).leg quarter).sourcePrepared.denominator :=
  (Roots.Sampling.Jet.sourceRoot_value (roots site quarter)).trans
    (source_preparation site quarter)

/-- The reindexed target certificate keeps the original retained changed-product preparation value. -/
theorem jet_target_preparation (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (Roots.Sampling.Jet.targetRoot (roots site quarter)).value =
      (roots site quarter).targetPrepared.denominator :=
  (Roots.Sampling.Jet.targetRoot_value (roots site quarter)).trans
    (roots site quarter).target_value

/-- The core stores the complete identical source observation from the original pair. -/
theorem jet_source_observation (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (jet site quarter).sourceSample.observation = (observations site quarter).source.observation := by
  unfold jet
  exact Roots.Sampling.Jet.ofPair_sourceObservation (observations site quarter) rfl

/-- The core stores the complete distinct target observation from that same original pair. -/
theorem jet_target_observation (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (jet site quarter).targetSample.observation = (observations site quarter).target.observation := by
  unfold jet
  exact Roots.Sampling.Jet.ofPair_targetObservation (observations site quarter) rfl

/-- The source state is the original cached process state under the complete certificate value equality. -/
theorem jet_source_state (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Coherent.CoherentNamed.castState (Roots.Sampling.Jet.sourceRoot_value (roots site quarter))
      (jet site quarter).sourceSample.state = (observations site quarter).source.state := by
  unfold jet
  exact Roots.Sampling.Jet.ofPair_sourceState (observations site quarter) rfl

/-- The target state is the original distinct cached state under its complete target value equality. -/
theorem jet_target_state (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Coherent.CoherentNamed.castState (Roots.Sampling.Jet.targetRoot_value (roots site quarter))
      (jet site quarter).targetSample.state = (observations site quarter).target.state := by
  unfold jet
  exact Roots.Sampling.Jet.ofPair_targetState (observations site quarter) rfl

/-- The core source preserves the original selected left sampling index and its retained minimum. -/
theorem jet_source_indices (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (jet site quarter).sourceSample.comparison.leftIndex = (observations site quarter).source.comparison.leftIndex ∧
      (jet site quarter).sourceSample.comparison.rightIndex = (observations site quarter).source.comparison.rightIndex ∧
        (jet site quarter).sourceSample.minimumIndex = (observations site quarter).source.minimumIndex := by
  unfold jet
  exact ⟨Roots.Sampling.Jet.ofPair_sourceIndex (observations site quarter) rfl,
    Roots.Sampling.Jet.ofPair_sourceRightIndex (observations site quarter) rfl,
    Roots.Sampling.Jet.ofPair_sourceMinimum (observations site quarter) rfl⟩

/-- The target retains both original selected comparison indices and its independent residual minimum. -/
theorem jet_target_indices (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (jet site quarter).targetSample.comparison.leftIndex = (observations site quarter).target.comparison.leftIndex ∧
      (jet site quarter).targetSample.comparison.rightIndex = (observations site quarter).target.comparison.rightIndex ∧
        (jet site quarter).targetSample.minimumIndex = (observations site quarter).target.minimumIndex := by
  unfold jet
  exact ⟨Roots.Sampling.Jet.ofPair_targetIndex (observations site quarter) rfl,
    Roots.Sampling.Jet.ofPair_targetRightIndex (observations site quarter) rfl,
    Roots.Sampling.Jet.ofPair_targetMinimum (observations site quarter) rfl⟩

/-- The retained source index still follows the original operational source-preparation comparison. -/
theorem jet_source_stage (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (observations site quarter).comparison.rightIndex ≤ (jet site quarter).sourceSample.comparison.leftIndex := by
  rewrite [(jet_source_indices site quarter).1]
  exact (observations site quarter).source_stage

/-- The target still follows its original computed full-product allowance stage. -/
theorem jet_target_stage (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Roots.Sampling.targetMinimum (roots site quarter) ≤
      (jet site quarter).targetSample.comparison.leftIndex := by
  rewrite [(jet_target_indices site quarter).1]
  exact (observations site quarter).target_stage

/-- Both scalar core readings are the identical originally selected full-cubic witnesses. -/
theorem jet_readings (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (jet site quarter).sourceSample.reading = (observations site quarter).source.reading ∧
      (jet site quarter).targetSample.reading = (observations site quarter).target.reading := by
  unfold jet
  exact ⟨Roots.Sampling.Jet.ofPair_sourceReading (observations site quarter) rfl,
    Roots.Sampling.Jet.ofPair_targetReading (observations site quarter) rfl⟩

/-- Each actual scalar source candidate pays the dense cubic residual at the original fixed spatial point. -/
theorem jet_source_residual (site : Fin 2) (quarter : UnitCircuitQuarter) {candidate : Canonical}
    (possible : (jet site quarter).sourceSample.observation.Possible candidate) :
    Norm.Basic.normSq (candidate * candidate - Polynomials.curveValue (parameter site)
      (Radial.Parameter.sourcePoint site (parameter site) (Waist.direction quarter 0)).base) <
        Norm.Basic.normSq (1 / 256 : Canonical) ^ 2 :=
  ((jet site quarter).sourceSample.residual_lt possible).trans_eq (jet site quarter).accuracy_eq

/-- Each target candidate pays the changed dense cubic residual at that identical original spatial point. -/
theorem jet_target_residual (site : Fin 2) (quarter : UnitCircuitQuarter) {candidate : Canonical}
    (possible : (jet site quarter).targetSample.observation.Possible candidate) :
    Norm.Basic.normSq (candidate * candidate - Polynomials.curveValue (parameter site + (1 / 256))
      (Radial.Parameter.sourcePoint site (parameter site) (Waist.direction quarter 0)).base) <
        Norm.Basic.normSq (1 / 256 : Canonical) ^ 2 :=
  ((jet site quarter).targetSample.residual_lt possible).trans_eq (jet site quarter).accuracy_eq

end TestPurelib.Curves.Legendre.ParameterChannels
