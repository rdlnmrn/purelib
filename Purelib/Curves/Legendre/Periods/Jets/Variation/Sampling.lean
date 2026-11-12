module

public import Purelib.Curves.Legendre.Periods.Jets.Variation
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Clearance
public import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Requested two-owner Legendre coefficient observations

The core consumes the exact two paid root observations and their candidate
clearance. One inverse-root expansion and one cubic composition feed both
original row banks. A separate original-window view retains its side,
containments and identical core; its constructors request each original root
once before deriving the observation margins. Direct geometric clearances use
the same core without constructing a substitute window or another sample.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling

open Purelib
open Purelib.Approximation
open Purelib.Calculus.Jet
open Purelib.Calculus.Jet.Quadratic
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling (Clearance)

/-- The original positive residual request at the fourth-order increment scale. -/
@[expose] def incrementRequest (increment : Canonical) (nonzero : increment ≠ 0) : AccuracyRequest :=
  ⟨Norm.Basic.normSq increment ^ 2,
    Fraction.Order.Arithmetic.pow_pos_direct (Norm.Basic.normSq_pos nonzero) 2⟩

/-- A paid observation supplies the exact unit-factor scalar residual hypothesis. -/
theorem paid_residual_le {parameter increment : Canonical}
    {root : CertifiedSquareRoot.Certificate parameter} {accuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation root accuracy)
    (accuracy_eq : accuracy.tolerance = Norm.Basic.normSq increment ^ 2) :
    Norm.Basic.normSq (sample.reading * sample.reading - parameter) ≤
      1 * Norm.Basic.normSq increment ^ 2 := by
  rewrite [Fraction.Field.one_mul]
  exact sample.reading_residual_lt.le.trans_eq accuracy_eq

set_option genInjectivity false in
/-- Two exact paid root observations, their candidate clearance and shared scalar inverse/cubic caches.

The distinct original certificates index their actual states and observations.
Every clearance bound concerns those same observation predicates. All row-bank
entries use the retained inverse or cubic certificate, with no new root request.
-/
structure SampledJet (parameter increment point : Canonical)
    (source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point))
    (target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point))
    (unit : Norm.Basic.normSq increment ≤ 1) where
  /-- The shared original residual accuracy request. -/ accuracy : AccuracyRequest
  /-- Both root observations pay the fourth-order increment scale. -/ accuracy_eq :
    accuracy.tolerance = Norm.Basic.normSq increment ^ 2
  /-- The cached paid observation of the original source process. -/ sourceSample :
    CertifiedSquareRoot.Sampling.ResidualObservation source accuracy
  /-- The cached paid observation of the distinct original target process. -/ targetSample :
    CertifiedSquareRoot.Sampling.ResidualObservation target accuracy
  /-- Positive source, target and sum floors for every candidate of these exact observations. -/ clearance :
    Clearance sourceSample targetSample
  /-- The inverse-root scalar Taylor certificate shared by both value rows. -/ inverse :
    Quadratic.Basic.Certificate increment
  /-- The inverse cache is the original constructor on these same paid readings and residuals. -/ inverse_eq : inverse =
    SquareRoot.inverseCertificate sourceSample.reading targetSample.reading
      (Polynomials.curveValue parameter point) increment (Polynomials.baseValue point) 1 1
      (by decide +kernel) (by decide +kernel) sourceSample.reading_nonzero targetSample.reading_nonzero
      clearance.sum_nonzero unit (paid_residual_le sourceSample accuracy_eq) (by
        rewrite [← Variation.radicand_step]
        exact paid_residual_le targetSample accuracy_eq)
  /-- The cubic composition shared by both first derivative rows. -/ cubic :
    Quadratic.Basic.Certificate increment
  /-- The cubic cache uses the exact retained inverse and original power polynomial. -/ cubic_eq : cubic =
    inverse.compose
      (Quadratic.Polynomial.certificate (Dense.Gaussian.Power.Coordinate.coordinatePositivePower 2)
        inverse.base inverse.output)
      (by simpa only [Norm.Basic.normSq_eq_canonical] using unit)
  /-- The original value-row scalar certificate bank. -/ value : Fin 2 → Quadratic.Basic.Certificate increment
  /-- Each value row scales the same inverse cache by its original numerator and scale. -/ value_eq :
    ∀ coordinate, value coordinate = inverse.scale
      ((Specification.valueSpecification parameter coordinate).scale *
        (Specification.valueSpecification parameter coordinate).numerator.eval point)
  /-- The original first derivative-row scalar certificate bank. -/ first :
    Fin 2 → Quadratic.Basic.Certificate increment
  /-- Each first row scales the same cubic cache by its original numerator and scale. -/ first_eq :
    ∀ coordinate, first coordinate = cubic.scale
      ((Specification.firstDerivativeSpecification parameter coordinate).scale *
        (Specification.firstDerivativeSpecification parameter coordinate).numerator.eval point)

constructive_injectivity SampledJet

/-- Construct the scalar caches and row banks from the identical supplied paid observations and clearance.

Both original observations are stored directly. The geometric clearance
derives sum nonzeroness, while their residual payments derive both scalar
hypotheses. One inverse and one cubic cache then feed all original row entries.
-/
@[expose] def ofObservations (parameter increment point : Canonical)
    (source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point))
    (target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point))
    (accuracy : AccuracyRequest) (accuracy_eq : accuracy.tolerance = Norm.Basic.normSq increment ^ 2)
    (sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source accuracy)
    (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target accuracy)
    (clearance : Clearance sourceSample targetSample) (unit : Norm.Basic.normSq increment ≤ 1) :
    SampledJet parameter increment point source target unit := by
  let inverse := SquareRoot.inverseCertificate sourceSample.reading targetSample.reading
    (Polynomials.curveValue parameter point) increment (Polynomials.baseValue point) 1 1
      (by decide +kernel) (by decide +kernel) sourceSample.reading_nonzero targetSample.reading_nonzero
      clearance.sum_nonzero unit (paid_residual_le sourceSample accuracy_eq) (by
        rewrite [← Variation.radicand_step]
        exact paid_residual_le targetSample accuracy_eq)
  let cubic := inverse.compose
    (Quadratic.Polynomial.certificate (Dense.Gaussian.Power.Coordinate.coordinatePositivePower 2)
      inverse.base inverse.output)
    (by simpa only [Norm.Basic.normSq_eq_canonical] using unit)
  let value := fun coordinate => inverse.scale
    ((Specification.valueSpecification parameter coordinate).scale *
      (Specification.valueSpecification parameter coordinate).numerator.eval point)
  let first := fun coordinate => cubic.scale
    ((Specification.firstDerivativeSpecification parameter coordinate).scale *
      (Specification.firstDerivativeSpecification parameter coordinate).numerator.eval point)
  exact
    { accuracy := accuracy
      accuracy_eq := accuracy_eq
      sourceSample := sourceSample
      targetSample := targetSample
      clearance := clearance
      inverse := inverse
      inverse_eq := rfl
      cubic := cubic
      cubic_eq := rfl
      value := value
      value_eq := fun _ => rfl
      first := first
      first_eq := fun _ => rfl }

section ObservationReadbacks

variable (parameter increment point : Canonical)
  (source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point))
  (target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point))
  (accuracy : AccuracyRequest) (accuracy_eq : accuracy.tolerance = Norm.Basic.normSq increment ^ 2)
  (sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source accuracy)
  (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target accuracy)
  (clearance : Clearance sourceSample targetSample) (unit : Norm.Basic.normSq increment ≤ 1)

/-- The observation constructor retains the identical supplied residual request. -/
theorem ofObservations_accuracy : (ofObservations parameter increment point source target accuracy accuracy_eq
    sourceSample targetSample clearance unit).accuracy = accuracy := by
  unfold ofObservations
  rfl

/-- The core stores the complete original source observation without requesting it again. -/
theorem ofObservations_sourceSample : (ofObservations parameter increment point source target accuracy accuracy_eq
    sourceSample targetSample clearance unit).sourceSample = sourceSample := by
  unfold ofObservations
  rfl

/-- The core stores the complete distinct target observation without requesting it again. -/
theorem ofObservations_targetSample : (ofObservations parameter increment point source target accuracy accuracy_eq
    sourceSample targetSample clearance unit).targetSample = targetSample := by
  unfold ofObservations
  rfl

/-- The core retains the complete supplied geometric clearance on those identical two observations. -/
theorem ofObservations_clearance : (ofObservations parameter increment point source target accuracy accuracy_eq
    sourceSample targetSample clearance unit).clearance = clearance := by
  unfold ofObservations
  rfl

end ObservationReadbacks

set_option genInjectivity false in
/-- An original signed-window view retaining one exact sampled core and both candidate containments.

The original window and outside-side owner remain indices. The core is stored
once, and its clearance floors read the same original side margin. Candidate
containments concern its actual observations rather than replacement samples.
-/
structure WindowedJet (parameter increment point : Canonical)
    (source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point))
    (target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point))
    (window : Box) (side : Box.OutsideSide window 0) (unit : Norm.Basic.normSq increment ≤ 1) where
  /-- The identical retained sampled scalar core. -/ core : SampledJet parameter increment point source target unit
  /-- Every candidate of its actual source observation remains in the original window. -/ sourceCandidates :
    ∀ {candidate : Canonical}, core.sourceSample.observation.Possible candidate → window.Contains candidate
  /-- Every candidate of its distinct target observation remains in that original window. -/ targetCandidates :
    ∀ {candidate : Canonical}, core.targetSample.observation.Possible candidate → window.Contains candidate
  /-- The source margin is the same original window-side margin. -/ sourceFloor_eq :
    core.clearance.sourceFloor = side.margin
  /-- The target margin is the same original window-side margin. -/ targetFloor_eq :
    core.clearance.targetFloor = side.margin
  /-- The sum margin retains the original fourfold side margin. -/ sumFloor_eq :
    core.clearance.sumFloor = 4 * side.margin

constructive_injectivity WindowedJet

namespace WindowedJet

variable {parameter increment point : Canonical}
  {source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point)}
  {target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point)}
  {window : Box} {side : Box.OutsideSide window 0} {unit : Norm.Basic.normSq increment ≤ 1}

/-- Retain the exact supplied scalar core with its original signed-window evidence and margin equations. -/
@[expose] def ofCore (core : SampledJet parameter increment point source target unit)
    (sourceCandidates : ∀ {candidate : Canonical}, core.sourceSample.observation.Possible candidate →
      window.Contains candidate)
    (targetCandidates : ∀ {candidate : Canonical}, core.targetSample.observation.Possible candidate →
      window.Contains candidate)
    (sourceFloor_eq : core.clearance.sourceFloor = side.margin)
    (targetFloor_eq : core.clearance.targetFloor = side.margin)
    (sumFloor_eq : core.clearance.sumFloor = 4 * side.margin) :
    WindowedJet parameter increment point source target window side unit :=
  { core := core
    sourceCandidates := sourceCandidates
    targetCandidates := targetCandidates
    sourceFloor_eq := sourceFloor_eq
    targetFloor_eq := targetFloor_eq
    sumFloor_eq := sumFloor_eq }

/-- The signed-window view preserves the complete original supplied core, including its sampling and scalar caches. -/
theorem ofCore_core (core : SampledJet parameter increment point source target unit)
    (sourceCandidates : ∀ {candidate : Canonical}, core.sourceSample.observation.Possible candidate →
      window.Contains candidate)
    (targetCandidates : ∀ {candidate : Canonical}, core.targetSample.observation.Possible candidate →
      window.Contains candidate)
    (sourceFloor_eq : core.clearance.sourceFloor = side.margin)
    (targetFloor_eq : core.clearance.targetFloor = side.margin)
    (sumFloor_eq : core.clearance.sumFloor = 4 * side.margin) :
    (ofCore core sourceCandidates targetCandidates sourceFloor_eq targetFloor_eq sumFloor_eq).core = core := by
  unfold ofCore
  rfl

end WindowedJet

/-- Sample each original process once and retain its original window view and shared scalar caches. -/
@[expose] def build (parameter increment point : Canonical)
    (source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point))
    (target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point))
    (window : Box) (side : Box.OutsideSide window 0)
    (sourceWindow : ∀ {candidate : Canonical}, source.value.name.process.Possible source.value.name.state candidate →
      window.Contains candidate)
    (targetWindow : ∀ {candidate : Canonical}, target.value.name.process.Possible target.value.name.state candidate →
      window.Contains candidate)
    (nonzero : increment ≠ 0) (unit : Norm.Basic.normSq increment ≤ 1) :
    WindowedJet parameter increment point source target window side unit := by
  let accuracy := incrementRequest increment nonzero
  let sourceSample := CertifiedSquareRoot.Sampling.request source accuracy
  let targetSample := CertifiedSquareRoot.Sampling.request target accuracy
  have sourceCandidates : ∀ {candidate : Canonical}, sourceSample.observation.Possible candidate →
      window.Contains candidate := by
    intro candidate possible
    rewrite [sourceSample.observation_eq, sourceSample.state_eq] at possible
    exact sourceWindow (Approximation.Gaussian.Process.Sampling.stateAt_possible_at_start
      source.value.name.process source.value.name.state sourceSample.comparison.leftIndex possible)
  have targetCandidates : ∀ {candidate : Canonical}, targetSample.observation.Possible candidate →
      window.Contains candidate := by
    intro candidate possible
    rewrite [targetSample.observation_eq, targetSample.state_eq] at possible
    exact targetWindow (Approximation.Gaussian.Process.Sampling.stateAt_possible_at_start
      target.value.name.process target.value.name.state targetSample.comparison.leftIndex possible)
  let clearance := Clearance.ofWindow sourceSample targetSample window side sourceCandidates targetCandidates
  let core := ofObservations parameter increment point source target accuracy rfl
    sourceSample targetSample clearance unit
  exact WindowedJet.ofCore core sourceCandidates targetCandidates
    (Clearance.ofWindow_sourceFloor sourceSample targetSample window side sourceCandidates targetCandidates)
    (Clearance.ofWindow_targetFloor sourceSample targetSample window side sourceCandidates targetCandidates)
    (Clearance.ofWindow_sumFloor sourceSample targetSample window side sourceCandidates targetCandidates)

/-- Use the complete original-owner caches and box refinements to construct the retained window view.

The two input certificates retain their original processes and actual
observations. Each owner supplies candidate containment through its complete
cache equality and the original box refinement; neither root is re-isolated.
-/
@[expose] def buildFromOwners (parameter increment point : Canonical)
    (source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point))
    (target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point))
    (sourceOwner : Riemann.Topology.SquareRootContinuationChain.Owner (Polynomials.curveValue parameter point))
    (targetOwner : Riemann.Topology.SquareRootContinuationChain.Owner
      (Polynomials.curveValue (parameter + increment) point))
    (sourceCache : source = sourceOwner.certificate sourceOwner.parameterNonzero)
    (targetCache : target = targetOwner.certificate targetOwner.parameterNonzero)
    (window : Box) (side : Box.OutsideSide window 0)
    (sourceBox : sourceOwner.track.initial.box.Refines window)
    (targetBox : targetOwner.track.initial.box.Refines window)
    (nonzero : increment ≠ 0) (unit : Norm.Basic.normSq increment ≤ 1) :
    WindowedJet parameter increment point source target window side unit :=
  build parameter increment point source target window side
    (fun possible => sourceBox.contains
      (CertifiedSquareRoot.Sampling.candidate_in_initial_box sourceOwner sourceCache possible))
    (fun possible => targetBox.contains
      (CertifiedSquareRoot.Sampling.candidate_in_initial_box targetOwner targetCache possible))
    nonzero unit

namespace SampledJet

variable {parameter increment point : Canonical}
  {source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point)}
  {target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point)}
  {unit : Norm.Basic.normSq increment ≤ 1}

/-- The actual source reading retains its original certificate's denominator margin. -/
theorem source_lower (jet : SampledJet parameter increment point source target unit) :
    source.apart.certificate.lowerSq ≤ Norm.Basic.normSq jet.sourceSample.reading :=
  jet.sourceSample.reading_normSq_lower

/-- The actual target reading retains its distinct original certificate's denominator margin. -/
theorem target_lower (jet : SampledJet parameter increment point source target unit) :
    target.apart.certificate.lowerSq ≤ Norm.Basic.normSq jet.targetSample.reading :=
  jet.targetSample.reading_normSq_lower

/-- The same actual readings pay the separately retained geometric sum margin. -/
theorem sum_lower (jet : SampledJet parameter increment point source target unit) :
    jet.clearance.sumFloor ≤ Norm.Basic.normSq (jet.sourceSample.reading + jet.targetSample.reading) :=
  jet.clearance.sum_normSq_lower

/-- Every original value row agrees with its scalar constructor on these exact original observations. -/
theorem value_agrees (jet : SampledJet parameter increment point source target unit)
    (coordinate : Fin 2) : jet.value coordinate =
    Variation.valueCertificate coordinate parameter increment point jet.sourceSample.reading jet.targetSample.reading
      1 1 (by decide +kernel) (by decide +kernel) jet.sourceSample.reading_nonzero jet.targetSample.reading_nonzero
      jet.clearance.sum_nonzero unit
      (paid_residual_le jet.sourceSample jet.accuracy_eq) (paid_residual_le jet.targetSample jet.accuracy_eq) := by
  rewrite [jet.value_eq coordinate, jet.inverse_eq]
  rfl

/-- Every original first row agrees with its scalar constructor using the same retained inverse/cubic caches. -/
theorem first_agrees (jet : SampledJet parameter increment point source target unit)
    (coordinate : Fin 2) : jet.first coordinate =
    Variation.firstCertificate coordinate parameter increment point jet.sourceSample.reading jet.targetSample.reading
      1 1 (by decide +kernel) (by decide +kernel) jet.sourceSample.reading_nonzero jet.targetSample.reading_nonzero
      jet.clearance.sum_nonzero unit
      (paid_residual_le jet.sourceSample jet.accuracy_eq) (paid_residual_le jet.targetSample jet.accuracy_eq) := by
  rewrite [jet.first_eq coordinate, jet.cubic_eq, jet.inverse_eq]
  rfl

end SampledJet

namespace WindowedJet

variable {parameter increment point : Canonical}
  {source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point)}
  {target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point)}
  {window : Box} {side : Box.OutsideSide window 0} {unit : Norm.Basic.normSq increment ≤ 1}

/-- The original source window contains the witness of the identical retained core observation. -/
theorem sourceInside (view : WindowedJet parameter increment point source target window side unit) :
    window.Contains view.core.sourceSample.reading :=
  view.sourceCandidates view.core.sourceSample.observation.witness_possible

/-- The same original window contains the distinct actual target witness of the retained core. -/
theorem targetInside (view : WindowedJet parameter increment point source target window side unit) :
    window.Contains view.core.targetSample.reading :=
  view.targetCandidates view.core.targetSample.observation.witness_possible

/-- The two actual core readings retain the original window-side sum margin. -/
theorem sum_lower (view : WindowedJet parameter increment point source target window side unit) :
    4 * side.margin ≤ Norm.Basic.normSq (view.core.sourceSample.reading + view.core.targetSample.reading) := by
  have lower := view.core.sum_lower
  rewrite [view.sumFloor_eq] at lower
  exact lower

end WindowedJet

end Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling
