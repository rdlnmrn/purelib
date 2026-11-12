module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Roots.Sampling.Clearance
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Transport
import Purelib.Approximation.Gaussian.Name.Coherent.Transport
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Actual fixed-point parameter jets on the original parallel observations

The dense and factored Legendre curve values agree by the original evaluation
law. Exact parameter casts preserve both complete original cubic certificates,
their retained process states, observations and selected indices. One sampled
core consumes those same two observations and their internally paid clearance.
The request constructor retains its original paired sample once; no root or
scalar observation is requested again for individual differential rows.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Roots.Sampling.Jet

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {original : UnitVertex}
variable {unit : Owner ((unitPolynomial site).eval (sourcePoint site parameter original).base)}
variable {source : Lift (sourcePoint site parameter original) unit}
variable {anchor : Anchor source} {increment : Canonical}
variable {step : Step anchor increment} {sourcePrepared : Division.Prepared source.value}

/-- The original geometric increment admission internally pays the unit-quadrance Taylor range. -/
theorem increment_unit (step : Step anchor increment) : Norm.Basic.normSq increment ≤ 1 := by
  have gap := halfGap_bound site parameter anchor.bound
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct gap
    (by decide +kernel : (0 : Fraction.Rational) ≤ 1 / 256)
  exact step.admitted.trans (scaled.trans (by decide +kernel : ((1 / 256) * (1 / 256) : Fraction.Rational) ≤ 1))

/-- Reindex the complete actual full source certificate by its original dense-to-factored evaluation equality. -/
@[expose] def sourceRoot (roots : Roots step sourcePrepared) :
    CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter (sourcePoint site parameter original).base) :=
  CertifiedSquareRoot.Certificate.castParameter
    (last := Polynomials.curveValue parameter (sourcePoint site parameter original).base)
    (Paths.polynomial_eval parameter (sourcePoint site parameter original).base) roots.sourceRoot

/-- Reindex the complete actual full target certificate by the same original evaluation law at the changed parameter. -/
@[expose] def targetRoot (roots : Roots step sourcePrepared) :
    CertifiedSquareRoot.Certificate
      (Polynomials.curveValue (parameter + increment) (sourcePoint site parameter original).base) :=
  CertifiedSquareRoot.Certificate.castParameter
    (last := Polynomials.curveValue (parameter + increment) (sourcePoint site parameter original).base)
    (Paths.polynomial_eval (parameter + increment) (sourcePoint site parameter original).base) roots.targetRoot

/-- The source index cast retains the complete original prepared cubic value process and cache. -/
theorem sourceRoot_value (roots : Roots step sourcePrepared) : (sourceRoot roots).value = roots.sourceRoot.value :=
  roots.sourceRoot.castParameter_value (Paths.polynomial_eval parameter (sourcePoint site parameter original).base)

/-- The target index cast retains the complete changed cubic value process and its original factor caches. -/
theorem targetRoot_value (roots : Roots step sourcePrepared) : (targetRoot roots).value = roots.targetRoot.value :=
  roots.targetRoot.castParameter_value
    (Paths.polynomial_eval (parameter + increment) (sourcePoint site parameter original).base)

/-- The exact original sampled-core type on the retained fixed spatial coordinate and reindexed cubic certificates. -/
@[expose] def Core (roots : Roots step sourcePrepared) : Type :=
  Variation.Sampling.SampledJet parameter increment (sourcePoint site parameter original).base
    (sourceRoot roots) (targetRoot roots) (increment_unit step)

/-- Construct one scalar core from the exact supplied original pair and its internally paid geometric clearance. -/
def ofPair {roots : Roots step sourcePrepared} {accuracy : AccuracyRequest}
    (pair : Pair roots accuracy accuracy) (accuracy_eq : accuracy.tolerance = Norm.Basic.normSq increment ^ 2) :
    Core roots :=
  let sourceSample := CertifiedSquareRoot.Sampling.ResidualObservation.castParameter
    (last := Polynomials.curveValue parameter (sourcePoint site parameter original).base)
    (Paths.polynomial_eval parameter (sourcePoint site parameter original).base) pair.source
  let targetSample := CertifiedSquareRoot.Sampling.ResidualObservation.castParameter
    (last := Polynomials.curveValue (parameter + increment) (sourcePoint site parameter original).base)
    (Paths.polynomial_eval (parameter + increment) (sourcePoint site parameter original).base) pair.target
  let clearance := pair.clearance.castParameters
    (Paths.polynomial_eval parameter (sourcePoint site parameter original).base)
    (Paths.polynomial_eval (parameter + increment) (sourcePoint site parameter original).base)
  Variation.Sampling.ofObservations parameter increment (sourcePoint site parameter original).base
    (sourceRoot roots) (targetRoot roots) accuracy accuracy_eq sourceSample targetSample clearance (increment_unit step)

section Readbacks

variable {roots : Roots step sourcePrepared} {accuracy : AccuracyRequest}
variable (pair : Pair roots accuracy accuracy) (accuracy_eq : accuracy.tolerance = Norm.Basic.normSq increment ^ 2)

/-- The core uses the identical residual accuracy request retained by both original paired observations. -/
theorem ofPair_accuracy : (ofPair pair accuracy_eq).accuracy = accuracy := by
  unfold ofPair
  exact Variation.Sampling.ofObservations_accuracy _ _ _ _ _ _ _ _ _ _ _

/-- The core retains the complete original source observation after its exact curve-index cast. -/
theorem ofPair_sourceObservation : (ofPair pair accuracy_eq).sourceSample.observation = pair.source.observation := by
  unfold ofPair
  rewrite [Variation.Sampling.ofObservations_sourceSample]
  exact pair.source.castParameter_observation
    (Paths.polynomial_eval parameter (sourcePoint site parameter original).base)

/-- The core retains the complete distinct original target observation after its same-value curve-index cast. -/
theorem ofPair_targetObservation : (ofPair pair accuracy_eq).targetSample.observation = pair.target.observation := by
  unfold ofPair
  rewrite [Variation.Sampling.ofObservations_targetSample]
  exact pair.target.castParameter_observation
    (Paths.polynomial_eval (parameter + increment) (sourcePoint site parameter original).base)

/-- The actual core source witness is the identical original paired reading. -/
theorem ofPair_sourceReading : (ofPair pair accuracy_eq).sourceSample.reading = pair.source.reading :=
  congrArg (fun observation : Approximation.Observation Canonical
    (fun first last => Norm.Basic.normSq (first - last)) => observation.witness)
      (ofPair_sourceObservation pair accuracy_eq)

/-- The actual core target witness is the identical original paired reading. -/
theorem ofPair_targetReading : (ofPair pair accuracy_eq).targetSample.reading = pair.target.reading :=
  congrArg (fun observation : Approximation.Observation Canonical
    (fun first last => Norm.Basic.normSq (first - last)) => observation.witness)
      (ofPair_targetObservation pair accuracy_eq)

/-- The core source retains the exact original sampled process state under its complete value-cache equality. -/
theorem ofPair_sourceState : Name.Coherent.CoherentNamed.castState (sourceRoot_value roots)
    (ofPair pair accuracy_eq).sourceSample.state = pair.source.state := by
  unfold ofPair
  rewrite [Variation.Sampling.ofObservations_sourceSample]
  exact pair.source.castParameter_state (Paths.polynomial_eval parameter (sourcePoint site parameter original).base)

/-- The core target retains the exact original distinct sampled state under its complete value-cache equality. -/
theorem ofPair_targetState : Name.Coherent.CoherentNamed.castState (targetRoot_value roots)
    (ofPair pair accuracy_eq).targetSample.state = pair.target.state := by
  unfold ofPair
  rewrite [Variation.Sampling.ofObservations_targetSample]
  exact pair.target.castParameter_state
    (Paths.polynomial_eval (parameter + increment) (sourcePoint site parameter original).base)

/-- The core source uses the original pair's selected left sampling index. -/
theorem ofPair_sourceIndex : (ofPair pair accuracy_eq).sourceSample.comparison.leftIndex =
    pair.source.comparison.leftIndex := by
  unfold ofPair
  rewrite [Variation.Sampling.ofObservations_sourceSample]
  exact pair.source.castParameter_leftIndex (Paths.polynomial_eval parameter (sourcePoint site parameter original).base)

/-- The core target uses the original pair's independently selected left sampling index. -/
theorem ofPair_targetIndex : (ofPair pair accuracy_eq).targetSample.comparison.leftIndex =
    pair.target.comparison.leftIndex := by
  unfold ofPair
  rewrite [Variation.Sampling.ofObservations_targetSample]
  exact pair.target.castParameter_leftIndex
    (Paths.polynomial_eval (parameter + increment) (sourcePoint site parameter original).base)

/-- The core source also retains the original selected right square-comparison index. -/
theorem ofPair_sourceRightIndex : (ofPair pair accuracy_eq).sourceSample.comparison.rightIndex =
    pair.source.comparison.rightIndex := by
  unfold ofPair
  rewrite [Variation.Sampling.ofObservations_sourceSample]
  exact pair.source.castParameter_rightIndex
    (Paths.polynomial_eval parameter (sourcePoint site parameter original).base)

/-- The core target retains its distinct original selected right square-comparison index. -/
theorem ofPair_targetRightIndex : (ofPair pair accuracy_eq).targetSample.comparison.rightIndex =
    pair.target.comparison.rightIndex := by
  unfold ofPair
  rewrite [Variation.Sampling.ofObservations_targetSample]
  exact pair.target.castParameter_rightIndex
    (Paths.polynomial_eval (parameter + increment) (sourcePoint site parameter original).base)

/-- The core source retains the original minimum index paying its square-residual spread. -/
theorem ofPair_sourceMinimum : (ofPair pair accuracy_eq).sourceSample.minimumIndex = pair.source.minimumIndex := by
  unfold ofPair
  rewrite [Variation.Sampling.ofObservations_sourceSample]
  exact pair.source.castParameter_minimumIndex
    (Paths.polynomial_eval parameter (sourcePoint site parameter original).base)

/-- The core target retains its independently computed original residual-spread minimum. -/
theorem ofPair_targetMinimum : (ofPair pair accuracy_eq).targetSample.minimumIndex = pair.target.minimumIndex := by
  unfold ofPair
  rewrite [Variation.Sampling.ofObservations_targetSample]
  exact pair.target.castParameter_minimumIndex
    (Paths.polynomial_eval (parameter + increment) (sourcePoint site parameter original).base)

/-- The sampled core retains the source floor of its same original geometric observation pair. -/
theorem ofPair_sourceFloor : (ofPair pair accuracy_eq).clearance.sourceFloor = pair.clearance.sourceFloor := by
  unfold ofPair
  rewrite [Variation.Sampling.ofObservations_clearance]
  exact pair.clearance.castParameters_sourceFloor _ _

/-- The sampled core retains the distinct target floor on that same original geometric observation pair. -/
theorem ofPair_targetFloor : (ofPair pair accuracy_eq).clearance.targetFloor = pair.clearance.targetFloor := by
  unfold ofPair
  rewrite [Variation.Sampling.ofObservations_clearance]
  exact pair.clearance.castParameters_targetFloor _ _

/-- The sampled core preserves the exact paired-observation sum margin under its original curve-index casts. -/
theorem ofPair_sumFloor : (ofPair pair accuracy_eq).clearance.sumFloor = pair.clearance.sumFloor := by
  unfold ofPair
  rewrite [Variation.Sampling.ofObservations_clearance]
  exact pair.clearance.castParameters_sumFloor _ _

end Readbacks

/-- One retained original pair and the exact sampled core computed from that same cache. -/
@[expose] def Requested (roots : Roots step sourcePrepared) (nonzero : increment ≠ 0) : Type :=
  Σ pair : Pair roots (Variation.Sampling.incrementRequest increment nonzero)
      (Variation.Sampling.incrementRequest increment nonzero),
    { core : Core roots // core = ofPair pair rfl }

/-- Request the original geometric pair once and retain one scalar core on its same actual observations. -/
def request (roots : Roots step sourcePrepared) (nonzero : increment ≠ 0) : Requested roots nonzero :=
  let accuracy := Variation.Sampling.incrementRequest increment nonzero
  let pair := Sampling.request roots accuracy accuracy
  let core := ofPair pair rfl
  ⟨pair, ⟨core, rfl⟩⟩

namespace Requested

variable {roots : Roots step sourcePrepared} {nonzero : increment ≠ 0}

/-- Read the identical cached original pair of full cubic observations. -/
@[expose] def pair (requested : Requested roots nonzero) :
    Pair roots (Variation.Sampling.incrementRequest increment nonzero)
      (Variation.Sampling.incrementRequest increment nonzero) := requested.1

/-- Read the sampled scalar core cached on that same original pair. -/
@[expose] def core (requested : Requested roots nonzero) : Core roots := requested.2.val

/-- The retained core is the complete actual construction from the identical retained original pair. -/
theorem core_eq (requested : Requested roots nonzero) : requested.core = ofPair requested.pair rfl :=
  requested.2.property

end Requested

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Roots.Sampling.Jet
