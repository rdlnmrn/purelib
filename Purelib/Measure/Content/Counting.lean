module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction

import Purelib.Data.List.Event
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Operations
import Purelib.Measure.Sampling.Statistic
public import Purelib.Measure.Weighted.Unit
import Purelib.Measure.Weighted.Basic

section
@[expose] public section

/-!
# Finite counting and empirical measures

A displayed sample list gives an exact rational counting content.  When its
length is explicitly positive, uniform normalization gives an exact empirical
distribution.  Probabilities are selected natural counts divided by the
displayed finite sample size.
-/

namespace Purelib.Measure

open Purelib in
/-- Assign unit nonnegative weight to each exact sample occurrence, preserving order and repetitions. -/
def countingContent {α : Type} (samples : List α) : Measure.Content α :=
  ⟨unitAtoms samples⟩

/-- Counting content of concatenated samples is the append of their two counting contents. -/
theorem countingContent_append {α : Type} (left right : List α) :
    countingContent (left ++ right) =
      (countingContent left).append (countingContent right) := by
  unfold countingContent Content.append
  congr 1
  exact unitAtoms_append left right

open Purelib.Data.Rat in
/-- The total mass of counting content is the rational cast of the exact sample-list length. -/
theorem countingContent_total {α : Type} (samples : List α) :
    (countingContent samples).total = (samples.length : Fraction.Rational) :=
  totalWeight_unitAtoms samples

open Purelib in
open Purelib.Data.Rat in
/-- An event's counting-content mass is the rational cast of its selecting sample count. -/
theorem countingContent_measure {α : Type} (samples : List α)
    (event : α → Bool) :
    (countingContent samples).measure event =
      (Data.List.countEvent samples event : Fraction.Rational) :=
  eventWeight_unitAtoms samples event

open Purelib.Data.Rat in
/-- Integrating over counting content is the sum of observable values over the original sample list. -/
theorem countingContent_integral {α : Type} (samples : List α)
    (value : α → Fraction.Rational) :
    (countingContent samples).integral value = sumValues samples value :=
  expectationWeight_unitAtoms samples value
end Purelib.Measure

end
