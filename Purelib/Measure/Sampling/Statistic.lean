module
import Purelib.Algebra.NatCast
public import Purelib.Data.List.Event
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

section
public section

/-!
# Explicit finite repeated sampling

An `iidSamples` table contains lists of exactly a supplied natural number of
draws from one displayed rational distribution.  The construction uses only
finite products and pushforwards.  Sample sums and means then have exact
rational expectation and variance formulas, giving a one-shot finite
Chebyshev estimate with the familiar reciprocal sample-count factor.

No infinite product, sequence of random variables, or asymptotic law is
constructed.
-/

namespace Purelib.Measure

open Purelib.Algebra

open Purelib.Data.Rat in
/-- Sum the rational observable over the exact ordered finite sample list. -/
@[expose] def sampleSum {α : Type} (value : α → Fraction.Rational) :
    List α → Fraction.Rational
  | [] => 0
  | item :: remaining => value item + sampleSum value remaining

namespace Distribution

open Purelib.Data.Rat
/-- Multiply the exact sample sum by the reciprocal of the supplied natural count.

The divisor is the supplied count, with the field's zero-inverse convention. This definition does not itself require the
sample length to equal that count. -/
@[expose] def sampleMean {α : Type} (count : Nat) (value : α → Fraction.Rational)
    (sample : List α) : Fraction.Rational :=
  ((count : Fraction.Rational))⁻¹ * sampleSum value sample

/-! ## Finite event frequencies -/

/-- Compute the event-indicator sample mean using the exact supplied count. -/
@[expose] def eventFrequency {α : Type} (count : Nat) (event : α → Bool) :
    List α → Fraction.Rational :=
  sampleMean count (indicator event)
end Distribution

end Purelib.Measure

end

section
section
public section

/-!
# Finite counting and empirical measures

A displayed sample list gives an exact rational counting content.  When its
length is explicitly positive, uniform normalization gives an exact empirical
distribution.  Probabilities are selected natural counts divided by the
displayed finite sample size.
-/

namespace Purelib.Measure

open Purelib.Algebra

open Purelib.Data.Rat
/-- Sum the supplied rational observable over the exact finite sample list. -/
@[expose] def sumValues {α : Type} : List α → (α → Fraction.Rational) → Fraction.Rational
  | [], _ => 0
  | item :: remaining, value =>
      value item + sumValues remaining value

/-- Pointwise equal observables give equal sums on the same retained sample list. -/
theorem sumValues_congr {α : Type} (samples : List α)
    (left right : α → Fraction.Rational)
    (equal : ∀ item, left item = right item) :
    sumValues samples left = sumValues samples right := by
  induction samples with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      rw [sumValues, sumValues, equal item, inductionHypothesis]

/-- The two argument-order presentations compute the same exact finite sample sum. -/
theorem sumValues_eq_sampleSum {α : Type}
    (samples : List α) (value : α → Fraction.Rational) :
    sumValues samples value = sampleSum value samples := by
  induction samples with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, sumValues, sampleSum, inductionHypothesis]
      rfl

/-- Summing after mapping samples equals summing the pulled-back observable on the original list. -/
theorem sumValues_map {α β : Type} (samples : List α)
    (function : α → β) (value : β → Fraction.Rational) :
    sumValues (samples.map function) value =
      sumValues samples (fun item => value (function item)) := by
  induction samples with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, List.map_cons, sumValues, inductionHypothesis]
      rfl
end Purelib.Measure

end

end

section
/-!
# Stationary finite dynamics and occupation averages

A finite transition preserves a displayed rational law when one exact step is
evaluation-equivalent to the original law.  This module proves preservation
at every supplied finite horizon and computes the exact expectation of a
finite Markov-path occupation count and frequency.  A final Chebyshev theorem
isolates the remaining dynamical input as the exact variance of that finite
occupation frequency.

This is a finite quantitative mean-ergodic interface, not an asymptotic
ergodic theorem: every path, horizon, event, expectation, and variance is
displayed finite rational data.
-/

public section

namespace Purelib.Measure

open Purelib.Algebra

open Purelib
open Purelib.Data.Rat
/-- The rational cast of a visit count is the head event indicator plus the exact tail visit count. -/
theorem cast_pathVisitCount_cons {alpha : Type} (event : alpha → Bool)
    (item : alpha) (remaining : List alpha) :
    (Data.List.pathVisitCount event (item :: remaining) : Fraction.Rational) =
      Distribution.indicator event item +
        (Data.List.pathVisitCount event remaining : Fraction.Rational) := by
  cases selected : event item
  · simp only [-eq_self, -iff_self, Data.List.pathVisitCount, selected, if_neg (by decide : ¬ false = true),
      Distribution.indicator, zero_add]
    rfl
  · simp only [-eq_self, -iff_self, Data.List.pathVisitCount, selected, if_pos rfl,
      Distribution.indicator, NatCast.add, Nat.cast_one]
    rfl

/-- Divide the exact finite path visit count by the supplied natural count using rational reciprocal multiplication. -/
@[expose] def pathVisitFrequency {alpha : Type} (count : Nat)
    (event : alpha → Bool) (path : List alpha) : Fraction.Rational :=
  (count : Fraction.Rational)⁻¹ * (Data.List.pathVisitCount event path : Fraction.Rational)

end Purelib.Measure

end
