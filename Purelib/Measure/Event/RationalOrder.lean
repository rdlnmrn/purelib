module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
import Purelib.CCL.Measure.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Function.Rat.Algebra
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Measure.Weighted.Event

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
public section

/-!
# Threshold stability for squared-sensitive finite CCL probes

Discontinuous threshold events cannot be controlled from a shrinking metric
bound alone when a value may lie on the threshold.  An explicit positive
rational witness margin repairs this constructively.  Squared-probe
sensitivity then requires a finite request at `margin^2`; after that request
every compatible realization has exactly the witness's Boolean
classification, so all resulting finite probabilities are equal.
-/

namespace Purelib.Measure.Event

open Purelib.Data.Rat in
/-- A strict distance bound preserves a weak threshold decision when its witness has the retained positive margin on
either side.

The same margin bounds the rational separation and separates the witness from the threshold. This forces the value and
witness to make exactly the same Boolean comparison. -/
theorem atLeastDecision_eq_of_margin
    {value witness threshold margin : Fraction.Rational}
    (marginPositive : 0 < margin)
    (close : Distance.rationalSeparation value witness < margin)
    (separated : threshold + margin ≤ witness ∨
      witness + margin ≤ threshold) :
    decide (threshold ≤ value) = decide (threshold ≤ witness) := by
  have valueMinusWitnessSmall : value - witness < margin :=
    (Fraction.Order.Basic.le_max_left (value - witness) (witness - value)).trans_lt close
  have witnessMinusValueSmall : witness - value < margin :=
    (Fraction.Order.Basic.le_max_right (value - witness) (witness - value)).trans_lt close
  rcases separated with above | below
  · have witnessInside : threshold ≤ witness := by
      calc
        threshold ≤ threshold + margin :=
          le_add_of_nonneg_right marginPositive.le
        _ ≤ witness := above
    have witnessLtValuePlusMargin : witness < value + margin := by
      have moved := Fraction.Order.Arithmetic.add_lt_add_right_direct
        witnessMinusValueSmall value
      calc
        witness = (witness - value) + value := by ring1
        _ < margin + value := moved
        _ = value + margin := _root_.add_comm _ _
    have thresholdMarginLt : threshold + margin < value + margin :=
      above.trans_lt witnessLtValuePlusMargin
    have valueInside : threshold ≤ value :=
      (Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct
        thresholdMarginLt).le
    rw [decide_eq_true valueInside,
      decide_eq_true witnessInside]
  · have valueLtWitnessPlusMargin : value < witness + margin := by
      have moved := Fraction.Order.Arithmetic.add_lt_add_right_direct
        valueMinusWitnessSmall witness
      calc
        value = (value - witness) + witness := by ring1
        _ < margin + witness := moved
        _ = witness + margin := _root_.add_comm _ _
    have valueBelow : value < threshold :=
      valueLtWitnessPlusMargin.trans_le below
    have witnessLtWitnessPlusMargin : witness < witness + margin := by
      have moved :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct marginPositive witness
      simpa only [-eq_self, -iff_self, add_zero] using moved
    have witnessBelow : witness < threshold :=
      witnessLtWitnessPlusMargin.trans_le below
    rw [decide_eq_false valueBelow.2,
      decide_eq_false witnessBelow.2]

end Purelib.Measure.Event

end

section
public section

/-!
# Finite rational cumulative contents

For a rational-valued finite distribution, cumulative probabilities are
exact evaluations of executable order tests.  Monotonicity and interval-mass
identities are finite Boolean-event calculations.  No continuity, supremum,
or real-valued distribution function is introduced.
-/

namespace Purelib.Measure

section
open Purelib.Data.Rat
/-- Decide whether a rational value is at most the supplied threshold. -/
@[expose] def atMostEvent (threshold : Fraction.Rational) : Fraction.Rational → Bool :=
  fun value => decide (value ≤ threshold)

/-- Decide strict membership above the lower endpoint and weak membership below the upper endpoint. -/
@[expose] def openClosedIntervalEvent (lower upper : Fraction.Rational) : Fraction.Rational → Bool :=
  fun value => decide (lower < value) && decide (value ≤ upper)

end

namespace Distribution

open Purelib.Data.Rat in
/-- For ordered endpoints, the lower cut union its following open-closed interval equals the upper cut pointwise.

The interval starts strictly above the lower endpoint and includes the upper endpoint. Each rational input is tested by
the retained Boolean order decisions. -/
theorem atMost_union_interval
    {lower upper : Fraction.Rational} (order : lower ≤ upper) (value : Fraction.Rational) :
    unionEvent (atMostEvent lower)
        (openClosedIntervalEvent lower upper) value =
      atMostEvent upper value := by
  by_cases valueLeLower : value ≤ lower
  · have valueLeUpper := valueLeLower.trans order
    have notAbove : ¬ lower < value := fun strict => strict.2 valueLeLower
    simp only [-eq_self, -iff_self, unionEvent, atMostEvent, openClosedIntervalEvent,
      decide_eq_true valueLeLower, decide_eq_true valueLeUpper,
      decide_eq_false notAbove, Bool.true_or]
    rfl
  · have lowerLtValue :=
      Fraction.Order.Arithmetic.lt_of_not_ge_direct valueLeLower
    by_cases valueLeUpper : value ≤ upper
    · simp only [-eq_self, -iff_self, unionEvent, atMostEvent, openClosedIntervalEvent,
        decide_eq_false valueLeLower, decide_eq_true lowerLtValue,
        decide_eq_true valueLeUpper, Bool.true_and, Bool.false_or]
      rfl
    · simp only [-eq_self, -iff_self, unionEvent, atMostEvent, openClosedIntervalEvent,
        decide_eq_false valueLeLower, decide_eq_true lowerLtValue,
        decide_eq_false valueLeUpper, Bool.true_and, Bool.false_or]
      rfl

end Distribution

end Purelib.Measure

end

section
public section

/-!
# Finite probability of rational-interval membership

A rational enclosure for each displayed atom can certify that its value is
inside a target rational interval, outside it, or still unresolved.  The
resulting finite lower/upper sums enclose the exact probability for every
explicit rational observable admitted by those enclosures.  Narrower source
enclosures can only narrow the probability enclosure.
-/

namespace Purelib.Measure

open Purelib in
open Purelib.Data.Rat in
/-- Decide whether the observable lies in the exact retained rational interval. -/
@[expose] def withinBoundEvent {α : Type} (target : Data.Rat.Interval)
    (value : α → Fraction.Rational) : α → Bool :=
  fun item => decide (target.Contains (value item))

end Purelib.Measure

end

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

open Purelib.Data.Rat in
/-- Decide whether the observable is at least the supplied rational threshold. -/
@[expose] def atLeastEvent {α : Type} (threshold : Fraction.Rational)
    (value : α → Fraction.Rational) : α → Bool :=
  fun item => decide (threshold ≤ value item)

end Purelib.Measure

end

section
/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

public section

namespace Purelib.Measure.Event

open Purelib in
open Purelib.Data.Rat in
/-- The Boolean complement of a strict lower-threshold event equals the corresponding weak upper-threshold event. -/
theorem complement_strictlyBelowProbe
    {α : Type} (value : α → Fraction.Rational) (threshold : Fraction.Rational) (item : α) :
    Measure.complementEvent
        (fun candidate => decide (value candidate < threshold)) item =
      Measure.atLeastEvent threshold value item := by
  by_cases below : value item < threshold
  · have notAtLeast : ¬threshold ≤ value item := below.2
    simp only [-eq_self, -iff_self, Measure.complementEvent,
      Measure.atLeastEvent, decide_eq_true below, decide_eq_false notAtLeast, Bool.not_true]
    rfl
  · have atLeast : threshold ≤ value item :=
      Fraction.Order.Arithmetic.le_of_not_gt_direct below
    simp only [-eq_self, -iff_self, Measure.complementEvent,
      Measure.atLeastEvent, decide_eq_false below, decide_eq_true atLeast, Bool.not_false]
    rfl

open Purelib in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Negating a projective probe and threshold turns its weak lower test into the original weak upper test. -/
theorem atLeast_negProbe_negThreshold
    {α : Type} (probe : Line.GaussianLine → Fraction.Rational) (points : α →
      Line.GaussianLine)
    (threshold : Fraction.Rational) (item : α) :
    Measure.atLeastEvent (-threshold)
        (fun candidate => Function.Rat.negProbe probe (points candidate)) item =
      decide (probe (points item) ≤ threshold) := by
  by_cases order : probe (points item) ≤ threshold
  · have negated : -threshold ≤ -probe (points item) :=
      Fraction.Order.Arithmetic.neg_le_neg_direct order
    simp only [-eq_self, -iff_self, Measure.atLeastEvent, Function.Rat.negProbe, decide_eq_true order]
    exact decide_eq_true negated
  · have notNegated : ¬(-threshold ≤ -probe (points item)) := by
      intro negated
      apply order
      have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct negated
      simpa only [-eq_self, -iff_self, neg_neg] using reversed
    simp only [-eq_self, -iff_self, Measure.atLeastEvent, Function.Rat.negProbe, decide_eq_false order]
    exact decide_eq_false notNegated
end Purelib.Measure.Event

end

section
public section

/-!
# Constructive finite rational quantiles

A rational-valued finite distribution admits an executable lower quantile at
every displayed level in `(0, 1]`.  The implementation insertion-sorts the
displayed atom table and performs a terminating weighted crossing search.
The result is accompanied by the exact strict-lower and cumulative
inequalities; no infimum, completed real line, or choice principle occurs.
-/

namespace Purelib.Measure

open Purelib.Data.Rat
/-- Decide whether a rational value is strictly below the supplied threshold. -/
@[expose] def strictlyBelowEvent (threshold : Fraction.Rational) : Fraction.Rational → Bool :=
  fun value => decide (value < threshold)

/-- Decide whether a rational coordinate is at least the supplied threshold. -/
@[expose] def atLeastCoordinateEvent (threshold : Fraction.Rational) : Fraction.Rational → Bool :=
  fun value => decide (threshold ≤ value)

/-- The complement of a strict rational lower cut equals the weak upper cut at the same threshold.

The two event evaluations use the same rational input and threshold. Their Boolean values agree by the direct strict and
weak order alternatives. -/
theorem complement_strictlyBelowEvent
    (threshold value : Fraction.Rational) :
    complementEvent (strictlyBelowEvent threshold) value =
      atLeastCoordinateEvent threshold value := by
  by_cases below : value < threshold
  · have notAtLeast : ¬threshold ≤ value := below.2
    simp only [-eq_self, -iff_self, complementEvent, strictlyBelowEvent, atLeastCoordinateEvent,
      decide_eq_true below, decide_eq_false notAtLeast, Bool.not_true]
    rfl
  · have atLeast : threshold ≤ value :=
      Fraction.Order.Arithmetic.le_of_not_gt_direct below
    simp only [-eq_self, -iff_self, complementEvent, strictlyBelowEvent, atLeastCoordinateEvent,
      decide_eq_false below, decide_eq_true atLeast, Bool.not_false]
    rfl

end Purelib.Measure

end

section
public section

/-!
# Finite Scheffé identities

Two nonnegative rational densities of expectation one define finite
reweighted probability laws.  The executable event where the first density
dominates the second attains their event-probability discrepancy.  Its mass is
the integral of the positive density difference, which equals the negative
part because both densities normalise.  Consequently atomic total variation
is exactly half the original-law L1 density separation.
-/

namespace Purelib.Measure

open Purelib.Data.Rat in
/-- Decide where the first rational density is at least the second. -/
@[expose] def densityDominanceEvent {α : Type}
    (first second : α → Fraction.Rational) : α → Bool :=
  fun item => decide (second item ≤ first item)

end Purelib.Measure

end
