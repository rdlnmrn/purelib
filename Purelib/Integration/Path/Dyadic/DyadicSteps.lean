module
import Purelib.Data.Fin
import Purelib.Data.List.Append
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

end Purelib.Integration.Path.Dyadic.DyadicSteps
