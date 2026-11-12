module

import Purelib.System.IO
import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Comparison.Observation
meta import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Comparison.Observation
meta import Purelib.Approximation.Gaussian.Logarithm.Chart.Transition.Comparison
meta import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchor.Unit
meta import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
meta import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.OperationalEquivalence
import Purelib.Approximation.Gaussian.Logarithm.Chart.Transition.Comparison
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Algebraic
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Equivalence
import Purelib.Approximation.Gaussian.Division.Prepared.FromEvidence
import Purelib.Approximation.Gaussian.Division.Obstruction.Zero
import Purelib.Examples.Approximation.Gaussian.Logarithm.Quotient.WorkedExamples
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchor.Unit
import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Step
import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport.Safety
import Purelib.Approximation.Gaussian.Logarithm.Chart.Safety
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Difference
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent

namespace TestPurelib.Approximation.Gaussian.Logarithm.TransitionComparison

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic
open Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic (BitLaw)
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement
open Purelib.Approximation.Gaussian.Logarithm.Chart
open Purelib.Approximation.Gaussian.Logarithm
open Purelib.Approximation.Gaussian.Logarithm.Chart.Transition
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Examples.Approximation.Gaussian.Logarithm.Quotient

/-- The first exact original target uses its retained initial state. -/
def firstState := LogarithmState.State.initial Anchor.Unit.exactOneInput

/-- The second schedule retains two genuine canonical refinements. -/
def secondState := firstState.advance.advance

/-- The exact unit source and based target have the actual unit as a common possible reading. -/
def unitOverlap (state : LogarithmState.State Anchor.Unit.exactOneInput) :
    Overlap.OverlapWitness Anchor.Unit.exactOneInput (LogarithmState.preparedTarget state) :=
  ⟨1, rfl, rfl⟩

/-- The first retained safety check admits the unit chart. -/
theorem firstSafety : Safety.Certificate Anchor.Unit.exactOneAnchor.chart.factor
    (Anchor.Unit.exactOneInput.name.process.ball firstState.source) firstState.nextIndex := by decide

/-- The later retained safety check uses its own actual schedule index. -/
theorem secondSafety : Safety.Certificate Anchor.Unit.exactOneAnchor.chart.factor
    (Anchor.Unit.exactOneInput.name.process.ball secondState.source) secondState.nextIndex := by decide

/-- Resume the first original overlap requirement without rerunning the safety search. -/
def first := Comparison.Prepared.resume Anchor.Unit.exactOneAnchor firstState
  (.overlap firstSafety) (unitOverlap firstState)

/-- Resume the later original overlap requirement on its distinct schedule. -/
def second := Comparison.Prepared.resume Anchor.Unit.exactOneAnchor secondState
  (.overlap secondSafety) (unitOverlap secondState)

/-- Independently scheduled ready outputs compare through the exact original unit anchor. -/
def outputsCompare : NamedEquivalent first.output.output.name second.output.output.name :=
  first.outputsEquivalentFromSameAnchor second (NamedEquivalent.refl _)

/-- The two actual source-to-target transition programs preserve their original branch. -/
def transitionsCompare : NamedEquivalent first.transition.name second.transition.name :=
  first.transitionsEquivalent second (NamedEquivalent.refl _) (NamedEquivalent.refl _)
    rfl (NamedEquivalent.refl _)

/-- The checked frontend uses the retained chart comparison through actual multiplication. -/
example : NamedEquivalent
    (CoherentNamed.mul first.output.output (CoherentNamed.Coherence.exact 2)).name
    (CoherentNamed.mul second.output.output (CoherentNamed.Coherence.exact 2)).name := by
  ccl_equiv [outputsCompare]

/-- Equal input channels with no supplied anchor alignment retain the exact typed request. -/
theorem missingAlignment : Comparison.comparePrepared first second (NamedEquivalent.refl _) none =
    .error .missing := rfl

/-- The actual unit target's retained exact algebraic evidence. -/
private def unitEvidence : Algebraic.Sidecar Anchor.Unit.exactOneInput :=
  Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 1)

example : (Comparison.compareAlgebraicPrepared first second unitEvidence unitEvidence none).2 =
    .error .missing := rfl

example : (match (Comparison.compareAlgebraicPrepared first second unitEvidence unitEvidence
    (some ⟨rfl, NamedEquivalent.refl _⟩)).2 with
  | .ok _ => true
  | .error _ => false) = true := rfl

example : (Comparison.compareAlgebraicPrepared first second unitEvidence unitEvidence none 2 3).1.left =
    unitEvidence := (Comparison.compareAlgebraicPrepared first second unitEvidence unitEvidence none 2 3).1.left_eq

namespace QuotientAlgebraic

open Purelib.Approximation.Gaussian.Logarithm.Quotient
open Purelib.Approximation.Gaussian.Division

/-- The original worked example's exact denominator and retained algebraic evidence. -/
private def halfEvidence : Algebraic.Sidecar WorkedExamples.client.denominator :=
  Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact WorkedExamples.half)

/-- Reuse the original anchor with an exact zero denominator. -/
private def zeroClient : Client := { WorkedExamples.client with denominator := CoherentNamed.Coherence.exact 0 }

/-- Exact zero evidence for the unchanged zero-denominator client. -/
private def zeroEvidence : Algebraic.Sidecar zeroClient.denominator :=
  Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 0)

/-- The actual successful algebraic decision for the original nonzero denominator. -/
private def cachedHalf : Quotient.Algebraic.CachedPreparation WorkedExamples.client halfEvidence := by
  cases selected : halfEvidence.decide with
  | prepared prepared => exact ⟨prepared, selected⟩
  | excluded zero =>
      exact (Obstruction.Zero.ZeroIdentity.incompatible_prepared zero
        (Prepared.ofEvidence WorkedExamples.denominatorState WorkedExamples.denominatorEvidence)).elim

/-- The existing manual denominator request at the original pending state. -/
private def manualRequest : Requirement.Blocked WorkedExamples.client :=
  Requirement.requestDenominator WorkedExamples.afterLog.log WorkedExamples.denominatorState true

/-- Retain the computed algebraic preparation while the original denominator is still pending. -/
private def pendingWithCache : Quotient.Algebraic.Cursor WorkedExamples.client halfEvidence :=
  ⟨manualRequest.state, halfEvidence, rfl, some cachedHalf⟩

/-- Resume the original manual request without discarding the algebraic preparation. -/
private def afterManual := pendingWithCache.resume manualRequest rfl WorkedExamples.denominatorEvidence

example : (match Quotient.Algebraic.step
    (Quotient.Algebraic.Cursor.start zeroEvidence { (State.initial zeroClient) with cursor := true }) with
  | .excluded .. => true
  | _ => false) = true := rfl

example : (match Quotient.Algebraic.step (Quotient.Algebraic.Cursor.start halfEvidence WorkedExamples.afterLog) with
  | .progressed next _ => match Quotient.Algebraic.step next with
    | .readyPrepared .. => true
    | _ => false
  | _ => false) = true := rfl

example : (match Quotient.Algebraic.step (Quotient.Algebraic.Cursor.start halfEvidence
    (State.withDenominatorSearching (.searching WorkedExamples.logState) WorkedExamples.denominatorState true)) with
  | .progressed next _ => match Quotient.Algebraic.step next with
    | .blocked retained _ _ _ => retained.preparation.isSome
    | _ => false
  | _ => false) = true := rfl

example : match Quotient.Algebraic.step (Quotient.Algebraic.Cursor.start halfEvidence WorkedExamples.initial) with
  | .blocked retained _ _ _ => retained.source = halfEvidence
  | _ => False := by rfl

example : match Quotient.Algebraic.step (Quotient.Algebraic.Cursor.start halfEvidence WorkedExamples.afterLog) with
  | .progressed next _ => next.source = halfEvidence
  | _ => False := by rfl

example : (match Quotient.Algebraic.step afterManual with
  | .ready retained _ _ _ => retained.preparation.isSome
  | _ => false) = true := rfl

example {client : Client} {sidecar : Algebraic.Sidecar client.denominator}
    (cursor : Quotient.Algebraic.Cursor client sidecar) (request : Requirement.Blocked client)
    (atState : request.state = cursor.current) (evidence : request.Evidence) :
    (cursor.resume request atState evidence).source = cursor.source :=
  cursor.resume_source request atState evidence

example {output : CoherentNamed} (ready : Quotient.PreparedReady WorkedExamples.client output) :
    NamedEquivalent output.name WorkedExamples.finalOutput.name :=
  Quotient.Equivalence.preparedReady_respects ready WorkedExamples.finalReady

end QuotientAlgebraic

/-- Zero finite budgets retain both original states and exhausted clearance work. -/
theorem zeroFuel_left_state :
    (Comparison.preflight Anchor.Unit.exactOneAnchor firstState secondState 0 0).left.state = firstState := rfl

/-- A successful finite safety check still requests its actual semantic overlap evidence. -/
theorem firstNeedsOverlap : ∃ discovered,
    Partial.Step.step _ _ Anchor.Unit.exactOneAnchor firstState = .blocked (.overlap discovered) :=
  Partial.Step.step_is_blocked_of_safe _ _ _ _ firstSafety

/-- Any proved factor mismatch rules out the fixed-factor route and supplies no global branch inequality. -/
theorem unequalFactor {leftSource rightSource : CoherentNamed}
    {leftAnchor : Anchored.AnchoredChart leftSource} {rightAnchor : Anchored.AnchoredChart rightSource}
    (different : leftAnchor.chart.factor ≠ rightAnchor.chart.factor)
    (alignment : Comparison.Alignment leftAnchor rightAnchor) : False :=
  Comparison.Alignment.impossible_of_factor_ne different alignment

/-- The second original anchor is the actual transported output at its retained later target state. -/
private def transportedAnchor := second.output

/-- Resume another original target from that same retained transported anchor and its actual unit overlap. -/
private def fromTransportedAnchor := Comparison.Prepared.resume transportedAnchor firstState
  (.overlap firstSafety) (⟨1, rfl, rfl⟩)

/-- These separately retained original anchor constructions need their own explicit alignment. -/
private theorem transportedAnchorRequest :
    Comparison.comparePrepared first fromTransportedAnchor (NamedEquivalent.refl _) none =
      .error .missing := rfl

/-- The actual transport preserves precisely the factor and correction needed by the fixed-factor alignment. -/
private def transportedAnchorAlignment : Comparison.Alignment Anchor.Unit.exactOneAnchor transportedAnchor :=
  ⟨rfl, NamedEquivalent.refl _⟩

/-- Execute the missing alignment for two original anchors and resume with their actual retained transport evidence.

The second source is the based future of the later preparation, and its anchor
is that preparation's actual transported output. A missing alignment requests
evidence for this pair; it asserts no inequality of their logarithm branches.
-/
public def checkAnchors : IO Unit := do
  let original := first
  let transported := fromTransportedAnchor
  unless second.state.nextIndex = 2 && transported.state.nextIndex = 0 do
    throw (IO.userError "Original anchor transport discarded the later source or original target schedule")
  match Comparison.comparePrepared original transported (NamedEquivalent.refl _) none with
  | .error .missing => pure ()
  | .ok _ => throw (IO.userError "Different original anchor constructions were compared without their alignment")
  match Comparison.comparePrepared original transported (NamedEquivalent.refl _) (some transportedAnchorAlignment) with
  | .error .missing => throw (IO.userError "The actual retained anchor transport failed to discharge its request")
  | .ok _ => pure ()
  Purelib.System.IO.println
    "Prepared logarithm anchors: original unit and retained transported source request explicit alignment"

/-- Execute prepared-chart comparison requests from two independent nonempty persistent prefixes. -/
public def check : IO Unit := do
  let preparedLeft := first
  let preparedRight := second
  let left := (ChannelCursor.initial preparedLeft.output.output).request 1 (by decide) 1
  let right := (ChannelCursor.initial preparedRight.output.output).request 1 (by decide) 2
  let result := ChannelCursor.compareSchedules left right
    (BitLaw.ofEquivalent
      (preparedLeft.outputsEquivalentFromSameAnchor preparedRight (NamedEquivalent.refl _)))
    [⟨1 / 4, by decide, 2⟩] [⟨1 / 16, by decide, 3⟩]
  unless result.sourceLeft.cursor.machine.emitted.length = 1 && result.sourceRight.cursor.machine.emitted.length = 2 do
    throw (IO.userError "Prepared chart comparison discarded an original nonempty prefix")
  unless result.outputLeft.cursor.machine.emitted.length = 3 && result.outputRight.cursor.machine.emitted.length = 5 do
    throw (IO.userError "Prepared chart comparison discarded its independently requested bit counts")
  let observed := result.observe 2 4 (1 / 16) (by decide)
  unless observed.comparison.leftIndex ≥ 2 && observed.comparison.rightIndex ≥ 4 && observed.residual < (1 / 16) do
    throw (IO.userError "Prepared chart comparison failed its actual cached finite observation")
  Purelib.System.IO.println
    "Prepared logarithm charts: prefixes 1/2 -> 3/5, sample starts 2/4 and cached request preserved"

end TestPurelib.Approximation.Gaussian.Logarithm.TransitionComparison
