import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Protocol

/-!
# Rational enclosures as finite observations

This module connects the rational-bound and neutral observation interfaces.
The symmetric rational separation is the maximum of the two directed
differences, so no absolute-value or completed metric structure is required.
-/

namespace FiniteMeasure

/-- Symmetric rational separation computed from two directed differences. -/
def rationalSeparation (left right : Coordinate) : Coordinate :=
  max (left - right) (right - left)

theorem rationalSeparation_symm (left right : Coordinate) :
    rationalSeparation left right = rationalSeparation right left := by
  unfold rationalSeparation
  exact max_comm _ _

theorem rationalSeparation_nonneg (left right : Coordinate) :
    0 ≤ rationalSeparation left right := by
  by_cases order : left ≤ right
  · exact le_max_of_le_right
      (RFAP.ConstructiveFraction.sub_nonneg_direct order)
  · have reverse : right ≤ left :=
      (RFAP.ConstructiveFraction.lt_of_not_ge_direct order).le
    exact le_max_of_le_left
      (RFAP.ConstructiveFraction.sub_nonneg_direct reverse)

namespace Bound

/-- A rational enclosure as an inhabited finite observation of its admitted
rational candidates. -/
def toObservation (bound : Bound) :
    Observation Coordinate rationalSeparation where
  Possible := bound.Contains
  witness := bound.sample
  witness_possible := bound.sample_contains
  spread := bound.width
  spread_nonnegative := bound.width_nonneg
  pairwise := by
    intro left right leftInside rightInside
    have directed := Bound.pairwise_difference_le leftInside rightInside
    exact max_le directed.1 directed.2

theorem Refines.toObservation {inner outer : Bound}
    (refines : Refines inner outer) :
    Observation.Refines inner.toObservation outer.toObservation :=
  ⟨fun possible => refines.contains possible⟩

end Bound

namespace Observation

/-- Center a rational enclosure at the displayed witness of a rational
observation and use its certified spread as the radius. -/
def rationalBound
    (observation : Observation Coordinate rationalSeparation) : Bound where
  lower := observation.witness - observation.spread
  upper := observation.witness + observation.spread
  valid :=
    (sub_le_self observation.witness observation.spread_nonnegative).trans
      (le_add_of_nonneg_right observation.spread_nonnegative)

/-- Every admitted rational candidate lies in the witness-centred enclosure.
The result uses only the displayed witness and the finite pairwise-spread
certificate. -/
theorem rationalBound_contains
    (observation : Observation Coordinate rationalSeparation)
    {value : Coordinate} (possible : observation.Possible value) :
    observation.rationalBound.Contains value := by
  have separation := observation.pairwise possible observation.witness_possible
  have directed :
      value - observation.witness ≤ observation.spread ∧
        observation.witness - value ≤ observation.spread :=
    max_le_iff.mp separation
  constructor
  · apply (sub_le_iff_le_add).2
    calc
      observation.witness ≤ observation.spread + value :=
        (sub_le_iff_le_add).1 directed.2
      _ = value + observation.spread := by ring1
  · calc
      value ≤ observation.spread + observation.witness :=
        (sub_le_iff_le_add).1 directed.1
      _ = observation.witness + observation.spread := by ring1

/-- The witness-centred enclosure has exactly twice the displayed rational
spread. -/
theorem rationalBound_width
    (observation : Observation Coordinate rationalSeparation) :
    observation.rationalBound.width = 2 * observation.spread := by
  dsimp only [rationalBound, Bound.width]
  ring1

end Observation

namespace BoundProcess

/-- Every finite rational enclosure process is a progressive neutral
observation process with the same states, requests, and rational widths. -/
def toProgressiveObservation (process : BoundProcess) :
    ProgressiveObservation Coordinate rationalSeparation where
  State := process.State
  observation state := (process.bound state).toObservation
  initial := process.initial
  request := process.request
  request_refines state epsilon positive :=
    (process.request_refines state epsilon positive).toObservation
  accurate := process.accurate
  refinesInitial state := (process.refinesInitial state).toObservation

/-- The neutral observation theorem recovers finite pairwise separation for
every rational admitted after a request. -/
theorem request_rationalSeparation_lt (process : BoundProcess)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon)
    {left right : Coordinate}
    (leftInside :
      (process.bound (process.request state epsilon positive)).Contains left)
    (rightInside :
      (process.bound (process.request state epsilon positive)).Contains right) :
    rationalSeparation left right < epsilon :=
  process.toProgressiveObservation.request_pairwise state epsilon positive
    leftInside rightInside

end BoundProcess

end FiniteMeasure
