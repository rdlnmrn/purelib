module

import Purelib.System.IO
import Purelib.Approximation.Gaussian.Translation.CCL.Cursor.RoundTrip.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Comparison.Observation
import Purelib.Approximation.Gaussian.Name.Coherent.Based
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Name.Coherent.Law.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Translation.CCL.Cursor.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.OperationalEquivalence
meta import Purelib.Approximation.Gaussian.Translation.CCL.Cursor.RoundTrip.Arithmetic
meta import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Comparison.Observation
meta import Purelib.Approximation.Gaussian.Name.Coherent.Based
meta import Purelib.Approximation.Gaussian.Name.Coherent.Law.Arithmetic
meta import Purelib.Approximation.Gaussian.Name.Coherent.Power
meta import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
meta import Purelib.Approximation.Gaussian.Name.Sampling
meta import Purelib.Data.Gaussian.Norm.Basic

/-! # Retained unary round trips and independent nonempty cursor request schedules -/

namespace TestPurelib.Approximation.Gaussian.Translation.CursorArithmetic

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Sequence (ApproximationData)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic (BitLaw)
open Purelib.Approximation.Gaussian.Translation.CCL.Cursor.RoundTrip
open Purelib.Approximation.Gaussian.Translation.CCL.Cursor.Basic (CursorObservation)
open Purelib.Data.Gaussian

/-- The original approximation remains a finite sampled exact-rational channel. -/
private def approximation := Sampling.approximation (CoherentNamed.Coherence.exact 2).name

/-- The original random-access approximation's own coherent process. -/
private def original := CoherentNamed.ofApproximation approximation

/-- One actual natural state of the original approximation-backed process. -/
private def originalState (index : Nat) : original.name.process.State := by
  change Nat
  exact index

/-- Reuse the same original process at its supplied dependent state. -/
private def atState (index : Nat) : CoherentNamed :=
  ⟨⟨original.name.process, originalState index⟩, original.coherent⟩

/-- The source comparison relates the two original retained dependent states. -/
private def statesEquivalent (first second : Nat) : NamedEquivalent (atState first).name (atState second).name :=
  NamedEquivalent.trans (NamedEquivalent.symm (original.rebaseEquivalent (originalState first)))
    (original.rebaseEquivalent (originalState second))

/-- The first approximation retains its original process at state zero. -/
private def firstApproximation := Sampling.approximation (atState 0).name

/-- The middle approximation retains an independently selected original state two. -/
private def middleApproximation := Sampling.approximation (atState 2).name

/-- The last approximation retains the original dependent state three. -/
private def lastApproximation := Sampling.approximation (atState 3).name

/-- The first complete retained translation certificate. -/
private def firstRoundTrip := certifiedApproximationCursorRoundTrip firstApproximation

/-- The exact middle translation certificate used by composition. -/
private def middleRoundTrip := certifiedApproximationCursorRoundTrip middleApproximation

/-- The last independent retained translation certificate. -/
private def lastRoundTrip := certifiedApproximationCursorRoundTrip lastApproximation

/-- Two actual retained round-trip comparisons compose through the same original middle sampler. -/
private def composed : Equivalent
    (CursorObservation.approximation firstApproximation.toNamed)
    (CursorObservation.approximation lastApproximation.toNamed) :=
  firstRoundTrip.compareThrough middleRoundTrip lastRoundTrip (statesEquivalent 0 2) (statesEquivalent 2 3)

/-- The first translated original channel. -/
private def firstTranslated :=
  CoherentNamed.ofApproximation (CursorObservation.approximation firstApproximation.toNamed)

/-- The independently represented last translated channel. -/
private def lastTranslated := CoherentNamed.ofApproximation (CursorObservation.approximation lastApproximation.toNamed)

/-- The actual negation of the original source approximation channel. -/
private def negativeSource := CoherentNamed.neg (CoherentNamed.ofApproximation firstApproximation)

/-- The actual negation after the original cursor round trip. -/
private def negativeTranslated := CoherentNamed.neg firstTranslated

/-- The retained round-trip certificate computes the original negation comparison. -/
private def negationLaw : BitLaw negativeSource negativeTranslated := BitLaw.ofEquivalent firstRoundTrip.neg_equivalent

/-- The original first translated channel's cubic power. -/
private def firstPower := Power.namedPower firstTranslated 3

/-- The original last translated channel's cubic power. -/
private def lastPower := Power.namedPower lastTranslated 3

/-- The cubic comparison uses the actual retained middle round trip and owned power congruence. -/
private def powerLaw : BitLaw firstPower lastPower :=
  BitLaw.ofEquivalent (Power.namedPower_respects _ _ composed.toNamed 3)

/-- The checked frontend consumes the actual unary round-trip certificate through original multiplication. -/
example : NamedEquivalent
    (CoherentNamed.mul negativeSource (CoherentNamed.Coherence.exact 3)).name
    (CoherentNamed.mul negativeTranslated (CoherentNamed.Coherence.exact 3)).name := by
  ccl_equiv [negationLaw.equivalent]

/-- The checked frontend retains both original channels of a finite power round trip. -/
example : NamedEquivalent
    (Power.namedPower (CoherentNamed.ofApproximation firstApproximation) 3).name
    (Power.namedPower
      (CoherentNamed.ofApproximation (CursorObservation.approximation firstApproximation.toNamed)) 3).name := by
  ccl_equiv [firstRoundTrip.power_equivalent 3]

/-- The composed independently represented cursor outputs remain checked original channels. -/
example : NamedEquivalent firstPower.name lastPower.name := by ccl_equiv [powerLaw.equivalent]

/-- Every retained cached observation is paid from the actual original schedule-comparison law. -/
example (left right : ChannelCursor) (leftSchedule rightSchedule : List ChannelCursor.RequestStep)
    (result : ChannelCursor.ScheduleComparison left right leftSchedule rightSchedule)
    (leftStart rightStart : Nat) (target : Purelib.Data.Rat.Fraction.Rational) (positive : 0 < target) :
    (result.observe leftStart rightStart target positive).residual < target :=
  (result.observe leftStart rightStart target positive).accurate

/-- Execute independent nonempty prefixes, original parser states, separate requests and cached sample payment. -/
private def checkCase (label : String) (leftChannel rightChannel : CoherentNamed)
    (law : BitLaw leftChannel rightChannel) : IO Unit := do
  let rightState := rightChannel.name.process.refine rightChannel.name.state (1 / 4) (by decide)
  let left := (ChannelCursor.atState leftChannel leftChannel.name.state).request 1 (by decide) 1
  let right := (ChannelCursor.atState rightChannel rightState).request 1 (by decide) 2
  let requestsLeft : List ChannelCursor.RequestStep := [⟨1 / 4, by decide, 1⟩, ⟨1 / 16, by decide, 2⟩]
  let requestsRight : List ChannelCursor.RequestStep := [⟨1 / 8, by decide, 2⟩]
  let result := ChannelCursor.compareSchedules left right law requestsLeft requestsRight
  unless result.sourceLeft.cursor.machine.emitted.length = 1 && result.sourceRight.cursor.machine.emitted.length = 2 do
    throw (IO.userError s!"{label}: discarded an original nonempty prefix")
  unless result.outputLeft.cursor.machine.emitted.length = 4 && result.outputRight.cursor.machine.emitted.length = 4 do
    throw (IO.userError s!"{label}: schedule failed to append the exact original requested bit counts")
  unless ChannelCursor.scheduledBitCount result.requestsLeft = 3 &&
      ChannelCursor.scheduledBitCount result.requestsRight = 2 do
    throw (IO.userError s!"{label}: discarded the independently retained requests")
  let observed := result.observe 2 5 (1 / 16) (by decide)
  unless observed.comparison.leftIndex ≥ 2 && observed.comparison.rightIndex ≥ 5 do
    throw (IO.userError s!"{label}: sample comparison discarded an original starting index")
  unless observed.residual = Norm.Basic.normSq (observed.first - observed.second) && observed.residual < (1 / 16) do
    throw (IO.userError s!"{label}: cached sample readings failed their actual retained payment")
  Purelib.System.IO.println s!"{label}: prefixes 1/2 -> 4/4, requests 3/2 bits, sample starts 2/5 preserved"

/-- Execute both actual unary construction chains through independently scheduled retained cursor observations. -/
public def check : IO Unit := do
  checkCase "negation-round-trip" negativeSource negativeTranslated negationLaw
  checkCase "composed-cubic-round-trips" firstPower lastPower powerLaw

end TestPurelib.Approximation.Gaussian.Translation.CursorArithmetic
