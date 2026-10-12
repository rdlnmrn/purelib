module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Event.Family
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Measure.Weighted.IntegralTransform

section
/-!
# Conditional expectation over displayed finite partitions

This module proves the finite rational form of the law of total expectation.
Every partition cell is an executable Boolean event, every sum is a displayed
list sum, and positivity of conditioning cells is carried explicitly.  No
sigma-algebra, completion, or limiting conditional expectation is formed.
-/

public section

namespace Purelib.Measure

open Purelib Purelib.Data.Rat

/-- Sum the rational indicators of the exact finite event list, retaining repeated positions. -/
@[expose]
def sumIndicators {α : Type} : List (α → Bool) → α → Fraction.Rational
  | [], _ => 0
  | event :: remaining, item =>
      Distribution.indicator event item + sumIndicators remaining item

/-- For events mutually disjoint on the retained atoms, their indicator sum equals the union indicator at each retained
payload.

The retained disjointness witness excludes simultaneous selection by a head event and its remaining union, so each
original atom contributes either zero or one. -/
theorem sumIndicators_eq_indicator_unionEvents_of_disjoint
    {α : Type} (atoms : List (Weighted α)) :
    ∀ {events : List (α → Bool)},
      MutuallyDisjointOn atoms events →
      ∀ (atom : Weighted α), atom ∈ atoms →
        sumIndicators events atom.item =
          Distribution.indicator (unionEvents events) atom.item
  | [], _, atom, member => by
      simp only [sumIndicators, unionEvents, Distribution.indicator, -eq_self, -iff_self]
      rfl
  | event :: remaining, disjoint, atom, member => by
      have tail := sumIndicators_eq_indicator_unionEvents_of_disjoint
        atoms disjoint.2 atom member
      cases headSelected : event atom.item <;>
        cases tailSelected : unionEvents remaining atom.item
      · simp only [sumIndicators, Distribution.indicator, headSelected,
          tailSelected, unionEvents, unionEvent, Bool.false_or, tail,
          zero_add, -eq_self, -iff_self]
        rfl
      · simp only [sumIndicators, Distribution.indicator, headSelected,
          tailSelected, unionEvents, unionEvent, Bool.false_or, tail,
          zero_add, -eq_self, -iff_self]
        rfl
      · simp only [sumIndicators, Distribution.indicator, headSelected,
          tailSelected, unionEvents, unionEvent, Bool.true_or, tail,
          add_zero, -eq_self, -iff_self]
        rfl
      · exact (disjoint.1 atom member
          ⟨headSelected, tailSelected⟩).elim

/-- A rejected finite event union has zero indicator-weighted coefficient sum at that same payload.

Every event in the exact retained list rejects the payload, so each displayed coefficient
is multiplied by its original zero indicator. Structural recursion preserves the event order. -/
theorem indicatorWeightedSum_eq_zero_of_unionEvents_false
    {α : Type} (item : α) (coefficient : (α → Bool) → Fraction.Rational) :
    ∀ events : List (α → Bool), unionEvents events item = false →
      (events.map fun event =>
        Distribution.indicator event item * coefficient event).sum = 0
  | [], unionFalse => rfl
  | event :: remaining, unionFalse => by
      cases selected : event item
      · simp only [-eq_self, -iff_self, List.map_cons, List.sum_cons, Distribution.indicator,
          selected, zero_mul, zero_add]; try rfl
        apply indicatorWeightedSum_eq_zero_of_unionEvents_false
        simpa only [-eq_self, -iff_self, unionEvents, unionEvent, selected, Bool.false_or]
          using unionFalse
      · simp only [-eq_self, -iff_self, unionEvents, unionEvent, selected, Bool.true_or]
          at unionFalse
        exact Bool.noConfusion unionFalse

end Purelib.Measure

end
