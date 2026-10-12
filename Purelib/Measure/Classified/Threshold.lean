module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Classified.Basic
public import Purelib.Measure.Classified.Split
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Threshold events from finite rational enclosures

Pointwise rational enclosures can decide some threshold comparisons and leave
the rest explicitly unresolved.  The resulting lower and upper probability
sums contain the exact threshold probability of every rational observable
admitted by the displayed enclosures.  Refining the enclosures narrows the
probability bound.
-/

namespace Purelib.Measure

section
open Purelib
open Purelib.Data.Rat
/-- Classify an interval as wholly at or above the threshold, strictly below it, or unresolved. -/
def thresholdStatus (range : Data.Rat.Interval) (threshold : Fraction.Rational) : Status :=
  if threshold ≤ range.lower then .inside
  else if range.upper < threshold then .outside
  else .unresolved

/-- Narrowing an original interval preserves or refines its status at the same retained threshold. -/
theorem thresholdStatus_refines {inner outer : Data.Rat.Interval}
    {threshold : Fraction.Rational} (refines : Interval.Refines inner outer) :
    (Measure.thresholdStatus inner threshold).Refines
      (Measure.thresholdStatus outer threshold) := by
  by_cases outerInside : threshold ≤ outer.lower
  · have innerInside : threshold ≤ inner.lower :=
      outerInside.trans refines.lower
    unfold Measure.thresholdStatus
    rewrite [if_pos outerInside, if_pos innerInside]
    rfl
  · by_cases outerOutside : outer.upper < threshold
    · have innerOutside : inner.upper < threshold :=
        refines.upper.trans_lt outerOutside
      have innerNotInside : ¬threshold ≤ inner.lower := by
        intro selected
        exact innerOutside.2 (selected.trans inner.valid)
      unfold Measure.thresholdStatus
      rewrite [if_neg outerInside, if_pos outerOutside,
        if_neg innerNotInside, if_pos innerOutside]
      rfl
    · unfold Measure.thresholdStatus
      rewrite [if_neg outerInside, if_neg outerOutside]
      trivial

/-- Require the exact interval to lie wholly at or above the threshold or strictly below it. -/
def ThresholdResolved (range : Data.Rat.Interval) (threshold : Fraction.Rational) : Prop :=
  threshold ≤ range.lower ∨ range.upper < threshold

/-- Resolving every original atom's range at the threshold makes the exact classified frontier's unresolved weight zero.
-/
public theorem unresolvedWeight_thresholdFrontier_eq_zero
    {α : Type} (ranges : α → Data.Rat.Interval) (threshold : Fraction.Rational) :
    ∀ atoms : List (Weighted α),
      (∀ atom, atom ∈ atoms →
        Measure.ThresholdResolved (ranges atom.item) threshold) →
      unresolvedWeight (atoms.map fun atom =>
        ⟨atom, Measure.thresholdStatus (ranges atom.item) threshold⟩) = 0
  | [], _ => rfl
  | atom :: remaining, resolved => by
      have head := resolved atom List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          Measure.ThresholdResolved (ranges candidate.item) threshold :=
        fun candidate member =>
          resolved candidate (List.mem_cons_of_mem atom member)
      simp only [-eq_self, -iff_self, List.map_cons, unresolvedWeight]
      rw [unresolvedWeight_thresholdFrontier_eq_zero
        ranges threshold remaining tail]
      rcases head with definitelyInside | definitelyOutside
      · unfold Measure.thresholdStatus
        rewrite [if_pos definitelyInside]
        change (0 : Fraction.Rational) + 0 = 0
        exact zero_add 0
      · have notInside : ¬threshold ≤ (ranges atom.item).lower := by
          intro selected
          exact definitelyOutside.2
            (selected.trans (ranges atom.item).valid)
        unfold Measure.thresholdStatus
        rewrite [if_neg notInside, if_pos definitelyOutside]
        change (0 : Fraction.Rational) + 0 = 0
        exact zero_add 0

end

end Purelib.Measure

end
