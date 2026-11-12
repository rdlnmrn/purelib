module
import Purelib.Data.Fin
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Algebra.Semiring.Normalization
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
public import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Exact widths and counts for the retained dyadic vertex list. -/
namespace Purelib.Integration.Path.Dyadic.DyadicSteps

section
open Purelib.Data.Rat

/-- Every successive point differs from its predecessor by one exact step.

The recursive predicate retains the original first point and ordered tail.
Each nonempty step supplies its scalar difference and the remaining certificate. -/
@[expose] def Steps : Fraction.Rational → List Fraction.Rational → Fraction.Rational → Prop
  | _, [], _ => True
  | first, next :: rest, step => next - first = step ∧ Purelib.Integration.Path.Dyadic.DyadicSteps.Steps next rest step

end

section
open Purelib.Data.Rat
open Purelib.Integration.Path.Dyadic
/-- Concatenate two exact-step lists at the first list's retained terminal point. -/
theorem Steps.append {first step : Fraction.Rational} {left right : List Fraction.Rational}
    (a : DyadicSteps.Steps first left step) (b : DyadicSteps.Steps (DyadicTrace.terminal first left) right step) :
      DyadicSteps.Steps first (left ++ right) step := by
  induction left generalizing first with
  | nil => exact b
  | cons next rest ih => exact ⟨a.1, ih a.2 b⟩

/-- Every bounded indexed edge of an exact-step list has its common width.

Finite first-position splitting reads the corresponding adjacent points of
the original list and retains the supplied edge index and its bound. -/
theorem Steps.indexed {first step : Fraction.Rational} {rest : List Fraction.Rational} (steps : DyadicSteps.Steps first
  rest step)
    (edge : Fin rest.length) : DyadicTrace.indexed first rest edge.succ - DyadicTrace.indexed first rest edge.castSucc =
      step := by
  induction rest generalizing first with
  | nil => exact Fin.elim0 edge
  | cons next rest ih =>
      refine Purelib.Data.Fin.cases_induction ?_ (fun edge => ?_) edge
      · exact steps.1
      · exact ih steps.2 edge

end

open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path.Dyadic in
/-- The original dyadic parameter tail has constant step equal to endpoint width times one half to the depth. -/
theorem tail_steps (depth : Nat) (first last : Fraction.Rational) :
    DyadicSteps.Steps first (DyadicTrace.tail depth first last) ((last - first) * (1 / 2) ^ depth) := by
  induction depth generalizing first last with
  | zero => exact ⟨by ring1, trivial⟩
  | succ depth ih =>
      have halves : PreparedBoxPartitions.midpoint first last - first = (last - first) / 2 ∧
          last - PreparedBoxPartitions.midpoint first last = (last - first) / 2 := by
        have twice := Fraction.Field.div_mul_cancel_of_ne (last - first) 2 (by decide)
        constructor
        · unfold PreparedBoxPartitions.midpoint; ring1
        · calc
            _ = (last - first) - (last - first) / 2 := by unfold PreparedBoxPartitions.midpoint; ring1
            _ = ((last - first) / 2) * 2 - (last - first) / 2 := by rw [twice]
            _ = _ := by ring1
      have left := ih first (PreparedBoxPartitions.midpoint first last)
      have right := ih (PreparedBoxPartitions.midpoint first last) last
      have width : ((last - first) / 2) * (1 / 2) ^ depth = (last - first) * (1 / 2) ^ (depth + 1) := by
        rw [pow_succ]
        simp only [Fraction.Field.div_eq_mul_inv_direct]
        ring1
      rw [halves.1, width] at left
      rw [halves.2, width] at right
      rw [DyadicTrace.tail]
      apply left.append
      rw [DyadicTrace.tail_terminal]
      exact right

open Purelib.Data.Rat in
open Purelib.Integration.Path.Dyadic in
/-- The dyadic parameter tail has exactly two to the depth entries.

At each successor depth the original left and right tails concatenate. Their
length certificates add without changing either retained parameter list. -/
theorem tail_length (depth : Nat) (first last : Fraction.Rational) : (DyadicTrace.tail depth first last).length = 2 ^
  depth := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih => rw [DyadicTrace.tail, Purelib.Data.List.Append.length_append, ih, ih, Nat.pow_succ]; omega0

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Integration.Path.Dyadic in
/-- Every retained squared edge width has the exact quarter-radius decay.

The common dyadic width factors as the original endpoint difference times
a half power; squaring that product gives the displayed quarter power. -/
theorem Steps.width_square {depth : Nat} {first last : Fraction.Rational} {rest : List Fraction.Rational}
    (steps : DyadicSteps.Steps first rest ((last - first) * (1 / 2) ^ depth)) (edge : Fin rest.length) :
    (DyadicTrace.indexed first rest edge.succ - DyadicTrace.indexed first rest edge.castSucc) ^ 2 =
      Geometric.Basic.quarterRadius 1 depth * (last - first) ^ 2 := by
  rw [steps.indexed, Purelib.Algebra.Semiring.Normalization.product_pow, ← pow_mul, Nat.mul_comm depth 2, pow_mul,
    show (1 / 2 : Fraction.Rational) ^ 2 = 1 / 4 by decide, Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

section Location

open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Integration.Path.Dyadic

/-- Nonnegative exact steps keep every indexed vertex beyond the original start.

The bounded original index follows the same finite spine. Each successor step
adds its nonnegative width before reading the unchanged remaining vertices.
-/
theorem Steps.first_le_indexed {first step : Fraction.Rational} {rest : List Fraction.Rational}
    (steps : Steps first rest step) (nonnegative : 0 ≤ step)
    (vertex : Fin (rest.length + 1)) : first ≤ DyadicTrace.indexed first rest vertex := by
  induction rest generalizing first with
  | nil =>
      refine Data.Fin.cases_induction ?_ (fun index => Fin.elim0 index) vertex
      exact le_rfl
  | cons next rest retained =>
      refine Data.Fin.cases_induction ?_ (fun index => ?_) vertex
      · exact le_rfl
      · have forward : first ≤ next := by
          have shifted := Fraction.Order.Arithmetic.add_le_add_direct nonnegative (le_rfl : first ≤ first)
          rewrite [← steps.1] at shifted
          calc
            first = 0 + first := (Fraction.Field.zero_add first).symm
            _ ≤ (next - first) + first := shifted
            _ = next := by ring1
        exact forward.trans (retained steps.2 index)

/-- The original locator selects the supplied edge when the query is strictly past its start and before its end.

Positive original steps exclude every earlier endpoint. The recursion consumes
the same original tail and returns its original bounded edge index; equality
at the right endpoint stays with that edge, preserving repeated query policy.
-/
theorem Steps.locate_eq {first step : Fraction.Rational} {rest : List Fraction.Rational}
    (steps : Steps first rest step) (positive : 0 < step) (nonempty : rest ≠ [])
    (time : Fraction.Rational) (lower : first ≤ time) (upper : time ≤ DyadicTrace.terminal first rest)
    (edge : Fin rest.length) (past : DyadicTrace.indexed first rest edge.castSucc < time)
    (before : time ≤ DyadicTrace.indexed first rest edge.succ) :
    (DyadicTrace.locate first rest nonempty time lower upper).val = edge := by
  induction rest generalizing first with
  | nil => exact Fin.elim0 edge
  | cons next rest retained =>
      revert past before
      refine Data.Fin.cases_induction ?_ (fun edge => ?_) edge
      · intro past before
        change time ≤ next at before
        unfold DyadicTrace.locate
        rewrite [dif_pos before]
        rfl
      · intro past before
        have after : ¬time ≤ next := by
          have start := steps.2.first_le_indexed positive.le edge.castSucc
          change DyadicTrace.indexed next rest edge.castSucc < time at past
          exact (start.trans_lt past).not_ge
        unfold DyadicTrace.locate
        rewrite [dif_neg after]
        exact congrArg Fin.succ (retained steps.2 _ _ _ edge past before)

/-- Every displayed equal-width interval is the same original indexed edge of its endpoint trace.

The actual membership constructor selects a bounded occurrence in Prop. Exact
widths recover its lower endpoint from the original preceding vertex; the
upper endpoint is read directly from the same mapped list. No data is selected
from the existential index, and repeated occurrences remain ordered.
-/
theorem Steps.interval {first step : Fraction.Rational} {spans : List Interval.Bounds}
    (steps : Steps first (spans.map (fun span => span.upper)) step)
    (widths : ∀ span ∈ spans, span.width = step) {span : Interval.Bounds} (member : span ∈ spans) :
    ∃ edge : Fin (spans.map (fun span => span.upper)).length,
      DyadicTrace.indexed first (spans.map (fun span => span.upper)) edge.castSucc = span.lower ∧
        DyadicTrace.indexed first (spans.map (fun span => span.upper)) edge.succ = span.upper := by
  induction spans generalizing first with
  | nil => nomatch member
  | cons head spans retained =>
      rcases Membership.mem_cons.mp member with same | member
      · subst span
        refine ⟨⟨0, Nat.zero_lt_succ _⟩, ?_, rfl⟩
        change first = head.lower
        have width := widths head (List.Mem.head spans)
        calc
          first = head.upper - (head.upper - first) := by ring1
          _ = head.upper - step := congrArg (fun value => head.upper - value) steps.1
          _ = head.upper - (head.upper - head.lower) :=
            congrArg (fun value => head.upper - value) width.symm
          _ = head.lower := by ring1
      · rcases retained steps.2 (fun span member => widths span (List.Mem.tail head member)) member with
          ⟨edge, start, finish⟩
        exact ⟨edge.succ, start, finish⟩

/-- Every original dyadic part is the same bounded edge in the original dyadic endpoint trace.

The retained interval parts have exactly the common dyadic width. Their upper
endpoint row is the original trace, so the displayed member supplies both
endpoint equalities at one bounded occurrence without constructing new cells.
-/
theorem tail_part (depth : Nat) (span : Interval.Bounds) {part : Interval.Bounds}
    (member : part ∈ Interval.Bisection.parts depth span) :
    ∃ edge : Fin (DyadicTrace.tail depth span.lower span.upper).length,
      DyadicTrace.indexed span.lower (DyadicTrace.tail depth span.lower span.upper) edge.castSucc = part.lower ∧
        DyadicTrace.indexed span.lower (DyadicTrace.tail depth span.lower span.upper) edge.succ = part.upper := by
  have steps : Steps span.lower ((Interval.Bisection.parts depth span).map (fun part => part.upper))
      ((span.upper - span.lower) * (1 / 2) ^ depth) := by
    rewrite [← DyadicTrace.tail_eq_parts_upper]
    exact tail_steps depth span.lower span.upper
  have selected := steps.interval (fun part member => Interval.Bisection.parts_width depth span member) member
  rewrite [← DyadicTrace.tail_eq_parts_upper] at selected
  exact selected

/-- The original finite locator contains the whole finer dyadic part when queried at that part's upper endpoint.

The midpoint recursion supplies a genuine coarse ancestor. Its positive-width
fine part lies strictly past that ancestor's start and at most at its end, so
the unchanged strict-left, closed-right locator selects that same occurrence.
Only proof data uses the ancestor; the actual returned index remains computed
by the original locator on the retained trace. With no further subdivision,
the same computed edge has exactly the displayed part's two endpoints.
-/
theorem tail_locate_contains (coarse extra : Nat) (span : Interval.Bounds)
    (proper : span.lower < span.upper) {part : Interval.Bounds}
    (member : part ∈ Interval.Bisection.parts (coarse + extra) span)
    (nonempty : DyadicTrace.tail coarse span.lower span.upper ≠ [])
    (lower : span.lower ≤ part.upper)
    (upper : part.upper ≤ DyadicTrace.terminal span.lower (DyadicTrace.tail coarse span.lower span.upper)) :
    let selected := DyadicTrace.locate span.lower (DyadicTrace.tail coarse span.lower span.upper)
      nonempty part.upper lower upper
    (DyadicTrace.indexed span.lower (DyadicTrace.tail coarse span.lower span.upper) selected.val.castSucc ≤
        part.lower ∧
      part.upper ≤ DyadicTrace.indexed span.lower (DyadicTrace.tail coarse span.lower span.upper)
        selected.val.succ) ∧
      (extra = 0 →
        DyadicTrace.indexed span.lower (DyadicTrace.tail coarse span.lower span.upper) selected.val.castSucc =
            part.lower ∧
          DyadicTrace.indexed span.lower (DyadicTrace.tail coarse span.lower span.upper) selected.val.succ =
            part.upper) := by
  rcases Interval.Bisection.parts_ancestor coarse extra span member with ⟨parent, parentMember, childMember⟩
  have lowerContained := Interval.Bisection.parts_subset extra parent childMember
    (show part.Contains part.lower from ⟨le_rfl, part.valid⟩)
  have upperContained := Interval.Bisection.parts_subset extra parent childMember
    (show part.Contains part.upper from ⟨part.valid, le_rfl⟩)
  have contained : parent.lower ≤ part.lower ∧ part.upper ≤ parent.upper :=
    ⟨lowerContained.1, upperContained.2⟩
  have parentProper := Interval.Bisection.parts_proper coarse span proper parentMember
  have childProper := Interval.Bisection.parts_proper extra parent parentProper childMember
  rcases tail_part coarse span parentMember with ⟨edge, start, finish⟩
  have positive : 0 < (span.upper - span.lower) * (1 / 2) ^ coarse :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Order.Arithmetic.sub_pos_direct proper)
      (Fraction.Order.Arithmetic.pow_pos_direct (by decide +kernel) coarse)
  have past : DyadicTrace.indexed span.lower (DyadicTrace.tail coarse span.lower span.upper)
      edge.castSucc < part.upper := by
    rewrite [start]
    exact contained.1.trans_lt childProper
  have before : part.upper ≤ DyadicTrace.indexed span.lower
      (DyadicTrace.tail coarse span.lower span.upper) edge.succ := by
    rewrite [finish]
    exact contained.2
  have selected := (tail_steps coarse span.lower span.upper).locate_eq positive nonempty part.upper
    lower upper edge past before
  dsimp only
  rewrite [selected, start, finish]
  refine ⟨contained, ?_⟩
  intro zero
  have same : part = parent := by
    cases zero
    change part ∈ [parent] at childMember
    rcases Membership.mem_cons.mp childMember with same | impossible
    · exact same
    · nomatch impossible
  exact ⟨congrArg Interval.Bounds.lower same.symm, congrArg Interval.Bounds.upper same.symm⟩

end Location

end Purelib.Integration.Path.Dyadic.DyadicSteps
