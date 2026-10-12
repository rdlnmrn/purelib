module
import Purelib.Data.List.Filter
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Polynomial.Geometry.Grid.AxisWalks
public import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Axis.Full
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

public section

/-!
# Complete retained axis walks inside a rectangular window

A monotone walk through a separated interval bank contains exactly the
intervals between its endpoints. The proof compares finite lists directly;
it neither equates functions extensionally nor repeats an axis search.
-/

namespace Purelib.Polynomial.Geometry.Grid.WindowAxes

open Geometry.Grid

universe u
variable {Alpha : Type u} {key : Alpha → Fraction.Rational}

/-- Predicates agreeing on a finite list select the same retained entries.

Each displayed head selects the same Boolean branch for both predicates.
The retained tail keeps its original occurrence order and multiplicity. -/
private theorem filter_congr_on {Beta : Type u} (first second : Beta → Prop)
    [DecidablePred first] [DecidablePred second] (entries : List Beta)
    (equal : ∀ entry ∈ entries, first entry ↔ second entry) :
    entries.filter (fun entry => decide (first entry)) = entries.filter (fun entry => decide (second entry)) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      have rest := ih (fun entry member => equal entry (List.mem_cons_of_mem _ member))
      by_cases kept : first head
      · have other := (equal head List.mem_cons_self).mp kept
        rw [List.Filter.filter_cons_of_pos (predicate := fun entry => decide (first entry)) (decide_eq_true kept),
          List.Filter.filter_cons_of_pos (predicate := fun entry => decide (second entry)) (decide_eq_true other)]
        exact congrArg (List.cons head) rest
      · have other : ¬second head := fun yes => kept ((equal head List.mem_cons_self).mpr yes)
        rw [List.Filter.filter_cons_of_neg (predicate := fun entry => decide (first entry)) (fun accepted => kept
          (of_decide_eq_true accepted)),
          List.Filter.filter_cons_of_neg (predicate := fun entry => decide (second entry)) (fun accepted => other
            (of_decide_eq_true accepted))]
        exact rest

/-- No positive-length axis interval lies inside a singleton coordinate window.

The two weak window bounds contradict each interval's strict endpoint order.
Filtering therefore rejects every displayed occurrence. -/
private theorem filter_empty (entries : List (ClearGrid.Interval key)) (point : Fraction.Rational) :
    entries.filter (fun interval => decide (point ≤ key interval.lower ∧ key interval.upper ≤ point)) = [] := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      have outside : ¬(point ≤ key head.lower ∧ key head.upper ≤ point) :=
        fun inside => (not_lt_of_ge (inside.2.trans inside.1)) head.ordered
      rw [List.Filter.filter_cons_of_neg (predicate := fun interval : ClearGrid.Interval key => decide (point ≤ key
        interval.lower ∧ key interval.upper ≤ point)) (fun accepted => outside (of_decide_eq_true accepted))]
      exact ih

/-- An increasing walk selects exactly the separated intervals within its endpoint bounds.

The supplied membership condition relates its actual edge list to the original interval list. -/
private theorem edges_eq_filter_in {intervals : List (ClearGrid.Interval key)} (entries : List (ClearGrid.Interval key))
    (separated : entries.Pairwise ClearGrid.Interval.Before) {start finish : Fraction.Rational} (walk :
      AxisWalks.IncreasingWalk intervals start finish)
    (included : ∀ interval ∈ walk.edges, interval ∈ entries) :
    walk.edges = entries.filter (fun interval => decide (start ≤ key interval.lower ∧ key interval.upper ≤ finish)) :=
      by
  induction entries generalizing start finish with
  | nil =>
      cases walk with
      | nil => rfl
      | cons first _ tail => exact (List.not_mem_nil (included first List.mem_cons_self)).elim
  | cons head rest ih =>
      cases walk with
      | nil => exact (filter_empty (head :: rest) _).symm
      | cons first _ tail =>
          rcases List.Membership.mem_cons.mp (included first List.mem_cons_self) with same | member
          · subst first
            have tailIncluded (interval : ClearGrid.Interval key) (member : interval ∈ tail.edges) : interval ∈ rest :=
              by
              rcases List.Membership.mem_cons.mp (included interval (List.mem_cons_of_mem _ member)) with same | member
              · subst interval
                exact (not_lt_of_ge (tail.edge_bounds head member).1 head.ordered).elim
              · exact member
            have remaining := ih (List.pairwise_cons.mp separated).2 tail tailIncluded
            have filters := filter_congr_on
              (fun interval : ClearGrid.Interval key => key head.upper ≤ key interval.lower ∧ key interval.upper ≤
                finish)
              (fun interval : ClearGrid.Interval key => key head.lower ≤ key interval.lower ∧ key interval.upper ≤
                finish)
              rest (fun interval member =>
                ⟨fun inside => ⟨head.ordered.le.trans inside.1, inside.2⟩,
                 fun inside => by
                   have ordered : ClearGrid.Interval.Before head interval := (List.pairwise_cons.mp separated).1
                     interval member
                   change key head.upper ≤ key interval.lower at ordered
                   exact ⟨ordered, inside.2⟩⟩)
            have kept : key head.lower ≤ key head.lower ∧ key head.upper ≤ finish := ⟨le_rfl, tail.ordered⟩
            change head :: tail.edges = _
            rw [List.Filter.filter_cons_of_pos (predicate := fun interval : ClearGrid.Interval key => decide (key
              head.lower ≤ key interval.lower ∧ key interval.upper ≤ finish)) (decide_eq_true kept)]
            exact congrArg (List.cons head) (remaining.trans filters)
          · have before : key head.upper ≤ key first.lower := by
              have ordered : ClearGrid.Interval.Before head first := (List.pairwise_cons.mp separated).1 first member
              change key head.upper ≤ key first.lower at ordered
              exact ordered
            have outside : ¬(key first.lower ≤ key head.lower ∧ key head.upper ≤ finish) :=
              fun inside => (not_lt_of_ge (before.trans inside.1)) head.ordered
            have restIncluded (interval : ClearGrid.Interval key)
                (member : interval ∈ (AxisWalks.IncreasingWalk.cons first ‹first ∈ intervals› tail).edges) : interval ∈
                  rest := by
              rcases List.Membership.mem_cons.mp (included interval member) with same | member
              · subst interval
                have bounded := (AxisWalks.IncreasingWalk.cons first ‹first ∈ intervals› tail).edge_bounds head member
                exact (not_lt_of_ge (before.trans bounded.1)) head.ordered |>.elim
              · exact member
            rw [List.Filter.filter_cons_of_neg (predicate := fun interval : ClearGrid.Interval key => decide (key
              first.lower ≤ key interval.lower ∧ key interval.upper ≤ finish)) (fun accepted => outside
              (of_decide_eq_true accepted))]
            exact ih (List.pairwise_cons.mp separated).2 _ restIncluded

namespace IncreasingWalk

/-- An increasing walk reads back exactly the intervals within its endpoint bounds.

Separation orders the retained interval bank. The actual walk's edges agree
with the ordered filter, including for a previously cached walk. -/
theorem edges_eq_filter {intervals : List (ClearGrid.Interval key)} (separated : intervals.Pairwise
  ClearGrid.Interval.Before)
    {start finish : Fraction.Rational} (walk : AxisWalks.IncreasingWalk intervals start finish) :
    walk.edges = intervals.filter (fun interval => decide (start ≤ key interval.lower ∧ key interval.upper ≤ finish)) :=
  edges_eq_filter_in intervals separated walk walk.edge_mem

/-- Finite endpoint telescoping for the actual emitted interval spine. -/
theorem sum_differences {intervals : List (ClearGrid.Interval key)} (value : Fraction.Rational →
  Gaussian.Basic.Canonical) :
    {start finish : Fraction.Rational} → (walk : AxisWalks.IncreasingWalk intervals start finish) →
      CellBoundary.sumValues (fun interval => value (key interval.lower) - value (key interval.upper)) walk.edges =
        value start - value finish
  | _, _, .nil _ => (sub_self _).symm
  | _, _, .cons interval _ tail => by
      change value (key interval.lower) - value (key interval.upper) +
        CellBoundary.sumValues (fun interval => value (key interval.lower) - value (key interval.upper)) tail.edges = _
      rw [sum_differences value tail]
      ring1

end IncreasingWalk
end Purelib.Polynomial.Geometry.Grid.WindowAxes
