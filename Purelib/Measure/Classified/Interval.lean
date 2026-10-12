module
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Measure.Classified.Soundness
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Content.Density.Aligned
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Classified.Split
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Finite probability of rational-interval membership

A rational enclosure for each displayed atom can certify that its value is
inside a target rational interval, outside it, or still unresolved.  The
resulting finite lower/upper sums enclose the exact probability for every
explicit rational observable admitted by those enclosures.  Narrower source
enclosures can only narrow the probability enclosure.
-/

namespace Purelib.Measure

section
open Purelib
/-- Classify an interval as inside a target interval, strictly separated from it, or unresolved.

Containment includes both target endpoints; outside requires strict separation, and overlapping intervals with
unresolved containment remain unresolved. -/
def withinBoundStatus (range target : Data.Rat.Interval) : Status :=
  if target.lower ≤ range.lower ∧ range.upper ≤ target.upper then .inside
  else if range.upper < target.lower ∨ target.upper < range.lower then .outside
  else .unresolved

/-- Select items whose exact retained interval has unresolved classification against the supplied target interval. -/
def withinBoundUnresolvedEvent {α : Type} (ranges : α → Data.Rat.Interval)
    (target : Data.Rat.Interval) : α → Bool :=
  Measure.unresolvedStatusEvent fun item => Measure.withinBoundStatus (ranges item) target

end

open Purelib in
open Purelib.Data.Rat in
/-- Narrowing the exact source interval preserves or refines its status relative to the same original target interval.
-/
theorem withinBoundStatus_refines {inner outer target : Data.Rat.Interval}
    (refines : Interval.Refines inner outer) :
    (Measure.withinBoundStatus inner target).Refines
      (Measure.withinBoundStatus outer target) := by
  by_cases outerInside :
      target.lower ≤ outer.lower ∧ outer.upper ≤ target.upper
  · have innerInside :
        target.lower ≤ inner.lower ∧ inner.upper ≤ target.upper :=
      ⟨outerInside.1.trans refines.lower,
        refines.upper.trans outerInside.2⟩
    unfold Measure.withinBoundStatus
    rewrite [if_pos outerInside, if_pos innerInside]
    rfl
  · by_cases outerOutside :
        outer.upper < target.lower ∨ target.upper < outer.lower
    · have innerOutside :
          inner.upper < target.lower ∨ target.upper < inner.lower := by
        rcases outerOutside with left | right
        · exact Or.inl (refines.upper.trans_lt left)
        · exact Or.inr (right.trans_le refines.lower)
      have innerNotInside :
          ¬(target.lower ≤ inner.lower ∧ inner.upper ≤ target.upper) := by
        intro selected
        rcases innerOutside with left | right
        · exact left.2 (selected.1.trans inner.valid)
        · exact right.2 (inner.valid.trans selected.2)
      unfold Measure.withinBoundStatus
      rewrite [if_neg outerInside, if_pos outerOutside,
        if_neg innerNotInside, if_pos innerOutside]
      rfl
    · unfold Measure.withinBoundStatus
      rewrite [if_neg outerInside, if_neg outerOutside]
      trivial

open Purelib
/-- Require the exact source interval to be contained in the target or strictly separated on one side. -/
def WithinBoundResolved (range target : Data.Rat.Interval) : Prop :=
  (target.lower ≤ range.lower ∧ range.upper ≤ target.upper) ∨
    range.upper < target.lower ∨ target.upper < range.lower

/-- If every original retained atom's interval is resolved against the target, the exact classified frontier has zero
unresolved weight. -/
public theorem unresolvedWeight_withinBoundFrontier_eq_zero
    {α : Type} (ranges : α → Data.Rat.Interval) (target : Data.Rat.Interval) :
    ∀ atoms : List (Weighted α),
      (∀ atom, atom ∈ atoms →
        Measure.WithinBoundResolved (ranges atom.item) target) →
      unresolvedWeight (atoms.map fun atom =>
        ⟨atom, Measure.withinBoundStatus (ranges atom.item) target⟩) = 0
  | [], _ => rfl
  | atom :: remaining, resolved => by
      have head := resolved atom List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          Measure.WithinBoundResolved (ranges candidate.item) target :=
        fun candidate member =>
          resolved candidate (List.mem_cons_of_mem atom member)
      simp only [-eq_self, -iff_self, List.map_cons, unresolvedWeight]
      rw [unresolvedWeight_withinBoundFrontier_eq_zero
        ranges target remaining tail]
      rcases head with whollyInside | separated
      · unfold Measure.withinBoundStatus
        rewrite [if_pos whollyInside]
        change (0 : Data.Rat.Fraction.Rational) + 0 = 0
        exact zero_add 0
      · have notInside :
            ¬(target.lower ≤ (ranges atom.item).lower ∧
              (ranges atom.item).upper ≤ target.upper) := by
          intro selected
          rcases separated with left | right
          · exact left.2 (selected.1.trans (ranges atom.item).valid)
          · exact right.2 ((ranges atom.item).valid.trans selected.2)
        unfold Measure.withinBoundStatus
        rewrite [if_neg notInside, if_pos separated]
        change (0 : Data.Rat.Fraction.Rational) + 0 = 0
        exact zero_add 0

end Purelib.Measure

end
