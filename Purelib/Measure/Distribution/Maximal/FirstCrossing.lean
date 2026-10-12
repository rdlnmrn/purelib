module
import Purelib.Data.Bool.Decide
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.EventFamily
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Event.Family
public import Purelib.Measure.Event.FirstCrossing
import Purelib.Measure.Weighted.Event
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
public section

/-!
# Finite first-crossing maximal inequality

A displayed list of rational observables has explicit first-crossing events
at every positive threshold.  These events are disjoint.  If each crossing
value transfers its restricted integral to one nonnegative terminal
observable, finite subadditivity and disjoint additivity give the sharp
Doob-style L1 maximal inequality.  The transfer property is explicit data;
there is no unbounded time, stopping-time space, or optional-limit theorem.
-/

namespace Purelib.Measure

open Purelib Purelib.Data.Rat Purelib.Data.Bool

namespace Distribution

/-- Sum each stage observable's integral on its first-crossing event within the retained active event.

The recursive tail removes all occurrences crossing the current threshold, so each stage retains its own disjoint
first-crossing event. -/
@[expose]
def crossingValueIntegralSumFrom {α : Type}
    (distribution : Distribution α) (active : α → Bool)
    (threshold : Fraction.Rational) : List (α → Fraction.Rational) → Fraction.Rational
  | [] => 0
  | value :: remaining =>
      distribution.eventIntegral
          (intersectionEvent active
            (Measure.atLeastEvent threshold value)) value +
        distribution.crossingValueIntegralSumFrom
          (intersectionEvent active
            (complementEvent (Measure.atLeastEvent threshold value)))
          threshold remaining

/-- Sum the fixed terminal observable's integrals over the same successive first-crossing events. -/
@[expose]
def crossingTerminalIntegralSumFrom {α : Type}
    (distribution : Distribution α) (active : α → Bool)
    (threshold : Fraction.Rational) (terminal : α → Fraction.Rational) :
    List (α → Fraction.Rational) → Fraction.Rational
  | [] => 0
  | value :: remaining =>
      distribution.eventIntegral
          (intersectionEvent active
            (Measure.atLeastEvent threshold value)) terminal +
        distribution.crossingTerminalIntegralSumFrom
          (intersectionEvent active
            (complementEvent (Measure.atLeastEvent threshold value)))
          threshold terminal remaining

/-- Require each retained first-crossing event to transfer its current observable integral to at most the terminal
integral.

The recursive condition updates the original active event by excluding the current crossing before checking the
remaining stages. -/
@[expose]
def CrossingTransferFrom {α : Type}
    (distribution : Distribution α) (active : α → Bool)
    (threshold : Fraction.Rational) (terminal : α → Fraction.Rational) :
    List (α → Fraction.Rational) → Prop
  | [] => True
  | value :: remaining =>
      distribution.eventIntegral
          (intersectionEvent active
            (Measure.atLeastEvent threshold value)) value ≤
        distribution.eventIntegral
          (intersectionEvent active
            (Measure.atLeastEvent threshold value)) terminal ∧
      distribution.CrossingTransferFrom
        (intersectionEvent active
          (complementEvent (Measure.atLeastEvent threshold value)))
        threshold terminal remaining

/-- Combine crossing-transfer certificates for a stage list and its tail started on the exact surviving event. -/
theorem crossingTransferFrom_append {α : Type}
    (distribution : Distribution α) (active : α → Bool)
    (threshold : Fraction.Rational) (terminal : α → Fraction.Rational) :
    ∀ (left right : List (α → Fraction.Rational)),
      distribution.CrossingTransferFrom active threshold terminal left →
      distribution.CrossingTransferFrom
        (survivingEventFrom active threshold left) threshold terminal right →
      distribution.CrossingTransferFrom active threshold terminal
        (left ++ right)
  | [], right, leftTransfer, rightTransfer => rightTransfer
  | value :: remaining, right, leftTransfer, rightTransfer => by
      constructor
      · exact leftTransfer.1
      · exact distribution.crossingTransferFrom_append
          (intersectionEvent active
            (complementEvent (Measure.atLeastEvent threshold value)))
          threshold terminal remaining right leftTransfer.2 rightTransfer

/-- Threshold times the sum of first-crossing probabilities is bounded by the corresponding crossing-value integral sum.
-/
theorem threshold_mul_crossingProbabilitySum_le {α : Type}
    (distribution : Distribution α) (threshold : Fraction.Rational) :
    ∀ (values : List (α → Fraction.Rational)) (active : α → Bool),
      threshold *
          ((firstCrossingEventsFrom active threshold values).map
            distribution.probability).sum ≤
        distribution.crossingValueIntegralSumFrom active threshold values
  | [], active => by
      simp only [firstCrossingEventsFrom, List.map_nil, List.sum_nil,
        mul_zero, crossingValueIntegralSumFrom]
      exact le_rfl
  | value :: remaining, active => by
      let crossing := intersectionEvent active
        (Measure.atLeastEvent threshold value)
      let laterActive := intersectionEvent active
        (complementEvent (Measure.atLeastEvent threshold value))
      have headBound : threshold * distribution.probability crossing ≤
          distribution.eventIntegral crossing value := by
        have restricted := distribution.eventIntegral_mono_on_event crossing
          (fun _ => threshold) value (by
            intro atom member selected
            have hitTrue : Measure.atLeastEvent threshold value atom.item =
                true := (Decide.and_true_iff _ _ |>.mp selected).2
            exact of_decide_eq_true hitTrue)
        rw [distribution.eventIntegral_constant] at restricted
        calc
          threshold * distribution.probability crossing =
              distribution.probability crossing * threshold := by ring1
          _ ≤ distribution.eventIntegral crossing value := restricted
      have tailBound :=
        distribution.threshold_mul_crossingProbabilitySum_le threshold
          remaining laterActive
      change threshold * (distribution.probability crossing +
          ((firstCrossingEventsFrom laterActive threshold remaining).map
            distribution.probability).sum) ≤
        distribution.eventIntegral crossing value +
          distribution.crossingValueIntegralSumFrom laterActive threshold
            remaining
      calc
        threshold * (distribution.probability crossing +
            ((firstCrossingEventsFrom laterActive threshold remaining).map
              distribution.probability).sum) =
          threshold * distribution.probability crossing +
            threshold *
              ((firstCrossingEventsFrom laterActive threshold remaining).map
                distribution.probability).sum := by ring1
        _ ≤ distribution.eventIntegral crossing value +
            distribution.crossingValueIntegralSumFrom laterActive threshold
              remaining := add_le_add headBound tailBound

/-- A retained crossing-transfer certificate bounds the current-value integral sum by the terminal integral sum on those
same events. -/
theorem crossingValueIntegralSum_le_terminal {α : Type}
    (distribution : Distribution α) (threshold : Fraction.Rational)
    (terminal : α → Fraction.Rational) :
    ∀ (values : List (α → Fraction.Rational)) (active : α → Bool),
      distribution.CrossingTransferFrom active threshold terminal values →
      distribution.crossingValueIntegralSumFrom active threshold values ≤
        distribution.crossingTerminalIntegralSumFrom active threshold
          terminal values
  | [], active, transfer => le_rfl
  | value :: remaining, active, transfer => by
      exact add_le_add transfer.1
        (distribution.crossingValueIntegralSum_le_terminal threshold terminal
          remaining
          (intersectionEvent active
            (complementEvent (Measure.atLeastEvent threshold value)))
          transfer.2)

/-- The recursive terminal integral sum equals the finite sum over the exact retained first-crossing event list. -/
theorem crossingTerminalIntegralSumFrom_eq {α : Type}
    (distribution : Distribution α) (threshold : Fraction.Rational)
    (terminal : α → Fraction.Rational) :
    ∀ (values : List (α → Fraction.Rational)) (active : α → Bool),
      distribution.crossingTerminalIntegralSumFrom active threshold terminal
          values =
        ((firstCrossingEventsFrom active threshold values).map fun event =>
          distribution.eventIntegral event terminal).sum
  | [], active => rfl
  | value :: remaining, active => by
      simp only [crossingTerminalIntegralSumFrom, firstCrossingEventsFrom,
        List.map_cons, List.sum_cons]
      rw [distribution.crossingTerminalIntegralSumFrom_eq threshold terminal
        remaining
        (intersectionEvent active
          (complementEvent (Measure.atLeastEvent threshold value)))]

/-- A first-stage transfer bound supplies the crossing-transfer certificate for the two-stage list ending in the
terminal observable. -/
theorem crossingTransferFrom_two_of_first {α : Type}
    (distribution : Distribution α) (threshold : Fraction.Rational)
    (first terminal : α → Fraction.Rational)
    (firstTransfer : distribution.eventIntegral
        (intersectionEvent (fun _ => true)
          (Measure.atLeastEvent threshold first)) first ≤
      distribution.eventIntegral
        (intersectionEvent (fun _ => true)
          (Measure.atLeastEvent threshold first)) terminal) :
    distribution.CrossingTransferFrom (fun _ => true) threshold terminal
      [first, terminal] := by
  refine ⟨firstTransfer, ?_⟩
  constructor
  · exact le_rfl
  · trivial

/-- A positive threshold times any-stage crossing probability is bounded by terminal expectation under retained integral
transfer and terminal nonnegativity. -/
theorem firstCrossing_l1_maximal {α : Type}
    (distribution : Distribution α) (threshold : Fraction.Rational)
    (positive : 0 < threshold) (values : List (α → Fraction.Rational))
    (terminal : α → Fraction.Rational)
    (terminalNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ terminal atom.item)
    (transfer : distribution.CrossingTransferFrom (fun _ => true)
      threshold terminal values) :
    threshold * distribution.probability
        (unionEvents (values.map (Measure.atLeastEvent threshold))) ≤
      distribution.expectation terminal := by
  let crossings := firstCrossingEvents threshold values
  have unionProbabilitySame :
      distribution.probability (unionEvents crossings) =
        distribution.probability
          (unionEvents (values.map (Measure.atLeastEvent threshold))) :=
    distribution.probability_congr _ _ (fun item =>
      unionEvents_firstCrossingEvents threshold values item)
  have unionBound := distribution.probability_unionEvents_le_sum crossings
  have scaledUnion :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct unionBound
      positive.le
  have crossingLower :=
    distribution.threshold_mul_crossingProbabilitySum_le threshold values
      (fun _ => true)
  have transferred :=
    distribution.crossingValueIntegralSum_le_terminal threshold terminal
      values (fun _ => true) transfer
  have terminalSum :=
    distribution.crossingTerminalIntegralSumFrom_eq threshold terminal
      values (fun _ => true)
  have packed :=
    distribution.eventIntegrals_sum_le_expectation_of_disjoint_nonnegative
      crossings terminal
      (firstCrossingEvents_mutuallyDisjointOn distribution.atoms threshold
        values)
      terminalNonnegative
  rw [← unionProbabilitySame]
  exact scaledUnion.trans (crossingLower.trans
    (transferred.trans (terminalSum.le.trans packed)))

/-- A first-stage integral transfer and nonnegative terminal observable bound the two-stage crossing probability by
terminal expectation divided by the positive threshold. -/
theorem twoStage_l1_maximal {α : Type}
    (distribution : Distribution α) (threshold : Fraction.Rational)
    (positive : 0 < threshold) (first terminal : α → Fraction.Rational)
    (terminalNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ terminal atom.item)
    (firstTransfer : distribution.eventIntegral
        (intersectionEvent (fun _ => true)
          (Measure.atLeastEvent threshold first)) first ≤
      distribution.eventIntegral
        (intersectionEvent (fun _ => true)
          (Measure.atLeastEvent threshold first)) terminal) :
    threshold * distribution.probability
        (unionEvents ([first, terminal].map
          (Measure.atLeastEvent threshold))) ≤
      distribution.expectation terminal :=
  distribution.firstCrossing_l1_maximal threshold positive
    [first, terminal] terminal terminalNonnegative
    (distribution.crossingTransferFrom_two_of_first threshold first terminal
      firstTransfer)
end Distribution

end Purelib.Measure

end
