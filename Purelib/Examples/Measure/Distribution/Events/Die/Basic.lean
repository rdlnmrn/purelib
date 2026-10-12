module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.AccuracyRequest
import Purelib.Data.Rat.Interval.Basic
import Purelib.Examples.Measure.Distribution.Coin.Basic
public import Purelib.Examples.Measure.Distribution.Die.Basic
import Purelib.Integration.Cell.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Integration.Cell.Distribution
import Purelib.Measure.Distribution.Moments.PaleyZygmund
import Purelib.Measure.Distribution.Moments.Cantelli
import Purelib.Measure.Classified.Process
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.EventFamily
import Purelib.Measure.Distribution.Conditioning.Probability
import Purelib.Measure.Distribution.Conditioning.Basic
import Purelib.Measure.Distribution.Moments.Covariance

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Events.Die.Basic

open Purelib.Examples.Measure.Distribution.Die.Basic (fairDie)
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (coinPayoff fairCoin)

/-- The event selecting even natural-number die faces. -/
def evenFace (face : Nat) : Bool :=
  face % 2 == 0

/-- The fair die assigns the even event probability one half. -/
example : fairDie.probability evenFace = 1 / 2 :=
  by
  decide

/-- The event selecting face one. -/
def lowFace (face : Nat) : Bool := face == 1

/-- The event selecting face two. -/
def middleFace (face : Nat) : Bool := face == 2

/-- The union of the face-one and face-two events has probability one third. -/
example : fairDie.probability (unionEvents
  [lowFace, middleFace]) = 1 / 3 := by
  decide

/-- The two distinct face events have additive union probability. -/
example : fairDie.probability (unionEvents
  [lowFace, middleFace]) =
    fairDie.probability lowFace +
      fairDie.probability middleFace := by
  apply fairDie.probability_unionEvents_of_disjoint
  constructor
  · intro atom member overlap
    simp only [fairDie, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [lowFace, middleFace,
        unionEvents, unionEvent]
  · constructor
    · intro atom member overlap
      simp only [fairDie, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [middleFace, unionEvents]
    · trivial

/-- The event selecting die faces above three. -/
def highFace (face : Nat) : Bool :=
  3 < face

/-- The high-face event has positive fair-die probability. -/
theorem highFacePositive : 0 <
  fairDie.probability highFace := by
  decide

/-- The conditional even probability given a high face is two thirds. -/
example : fairDie.conditionalProbability evenFace
  highFace
    highFacePositive = 2 / 3 := by
  decide

/-- Conditioning on the high-face event makes that event certain. -/
example : (fairDie.conditioned highFace
  highFacePositive).probability
    highFace = 1 :=
  fairDie.conditioned_probability_condition
    highFace highFacePositive

/-- The fair-die coordinate expectation is `7/2`. -/
example : fairDie.expectation (fun face => (face : Fraction.Rational)) = 7 / 2 := by
  exact Measure.Distribution.Die.Basic.fairDie_coordinate_expectation

/-- The die's exact expectation cells yield the exact interval at `7/2`. -/
example : Purelib.Integration.integralBound
      (fairDie.expectationCells fun face => (face : Fraction.Rational)) =
    Purelib.Data.Rat.Interval.exact (7 / 2) := open Purelib in by
  rw [fairDie.integralBound_expectationCells]
  apply Data.Rat.Interval.ext <;> decide

/-- The fair-die coordinate variance is `35/12`. -/
example : fairDie.variance (fun face => (face : Fraction.Rational)) = 35 / 12 := by
  exact Measure.Distribution.Die.Basic.fairDie_coordinate_variance

/-- The squared die-coordinate expectation is bounded by its second moment. -/
example : fairDie.expectation (fun face => (face : Fraction.Rational)) ^ 2 ≤
    fairDie.expectation (fun face => (face : Fraction.Rational) ^ 2) :=
  fairDie.expectation_sq_le_secondMoment
    (fun face => (face : Fraction.Rational))

/-- The finite Paley-Zygmund bound controls the probability of exceeding half the die-coordinate mean. -/
example :
    (1 - (1 / 2 : Fraction.Rational)) ^ 2 *
          fairDie.expectation (fun face => (face : Fraction.Rational)) ^ 2 /
        fairDie.expectation (fun face => (face : Fraction.Rational) ^ 2) ≤
      fairDie.probability
        (fairDie.aboveFractionOfMeanEvent
        (fun face => (face : Fraction.Rational)) (1 / 2)) := by
  apply fairDie.paleyZygmund_bound (fun face => (face : Fraction.Rational))
    (1 / 2) (by decide) (by decide)
  · intro atom member
    simp only [fairDie, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · decide

/-- A coin payoff's covariance with itself equals its variance. -/
example : fairCoin.covariance
  coinPayoff
  coinPayoff =
    fairCoin.variance
      coinPayoff :=
  fairCoin.covariance_self coinPayoff

/-- Adding five to the coin payoff preserves its variance. -/
example : fairCoin.variance (fun outcome =>
  coinPayoff outcome + 5) =
    fairCoin.variance
      coinPayoff :=
  fairCoin.variance_add_constant
    coinPayoff 5

/-- The high-face probability satisfies the Markov bound with threshold four. -/
example : fairDie.probability highFace ≤
    fairDie.expectation (fun face => (face : Fraction.Rational)) / 4 := by
  apply fairDie.markov_bound highFace (fun face =>
    (face : Fraction.Rational)) 4
    (by decide)
  · intro atom member
    simp only [fairDie, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro atom member selected
    simp only [fairDie, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [highFace] <;> decide

/-- The high-face probability satisfies the one-sided variance bound at deviation one half. -/
example : fairDie.probability highFace ≤
    fairDie.variance (fun face => (face : Fraction.Rational)) /
      (fairDie.variance (fun face => (face : Fraction.Rational)) + (1 / 2) ^ 2) := by
  apply fairDie.cantelli_bound highFace
    (fun face => (face : Fraction.Rational)) (1 / 2) (by decide)
  intro atom member selected
  simp only [fairDie, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [highFace] <;> decide

/-- The exact even-event frontier has width zero. -/
example : (eventBound (fairDie.eventFrontier
  evenFace)).width = 0 :=
  fairDie.eventFrontier_bound_exact evenFace

/-- The exact even-event process meets every positive width request. -/
example (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    ((fairDie.exactEventProcess
      evenFace).toBoundProcess.bound ()).width <
      epsilon := by
  simpa only [EventProcess.toBoundProcess,
    Distribution.exactEventProcess] using
      (fairDie.exactEventProcess
        evenFace).request_width_lt () epsilon positive

/-- A completed finite list of exact-event requests meets each retained member tolerance for unresolved weight. -/
example (request : Purelib.Approximation.AccuracyRequest) (requests : List Purelib.Approximation.AccuracyRequest)
    (member : request ∈ requests) :
    unresolvedWeight ((fairDie.exactEventProcess
      evenFace).frontier
      ((fairDie.exactEventProcess
        evenFace).runRequests () requests)) <
        request.tolerance :=
  (fairDie.exactEventProcess
    evenFace).runRequests_unresolved_lt_of_mem
    () requests request member

end Purelib.Examples.Measure.Distribution.Events.Die.Basic

end
