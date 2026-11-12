module

public import Purelib.Riemann.Branches.ClearSheetContinuation
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Original dyadic endpoint containment and paid finite widths

Every actual edge of the original dyadic list retains its original order
inside its original interval. The finite mesh width law then supplies exact
squared-width payments at every chosen minimum, without changing that list.
-/

public section

namespace Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

open Purelib
open Purelib.Approximation.Rational
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Riemann.Meshes

/-- Every original dyadic edge lies in its original ordered interval with the SAME left-to-right orientation. -/
theorem dyadicEdges_bounds (depth : Nat) (left right : Endpoint) (ordered : left.parameter ≤ right.parameter)
    (edge : ParameterEdge) (member : edge ∈ dyadicEdges depth left right) :
    left.parameter ≤ edge.left.parameter ∧ edge.left.parameter ≤ edge.right.parameter ∧
      edge.right.parameter ≤ right.parameter := by
  induction depth generalizing left right with
  | zero =>
      have same := Membership.mem_singleton.mp member
      cases same
      exact ⟨Fraction.Order.Basic.le_refl _, ordered, Fraction.Order.Basic.le_refl _⟩
  | succ depth retained =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
      change edge ∈ dyadicEdges depth left middle ++ dyadicEdges depth middle right at member
      cases Membership.mem_append.mp member with
      | inl first =>
          have bounds := retained left middle (left_le_midpoint ordered) first
          exact ⟨bounds.1, bounds.2.1, bounds.2.2.trans (midpoint_le_right ordered)⟩
      | inr last =>
          have bounds := retained middle right (midpoint_le_right ordered) last
          exact ⟨(left_le_midpoint ordered).trans bounds.1, bounds.2.1, bounds.2.2⟩

/-- A point of an original ordered dyadic edge remains within one full original interval width of its left source. -/
theorem dyadicEdges_source_distance_le (depth : Nat) (left right : Endpoint)
    (ordered : left.parameter ≤ right.parameter) (edge : ParameterEdge)
    (member : edge ∈ dyadicEdges depth left right) (time : Fraction.Rational)
    (inside : edge.left.parameter ≤ time ∧ time ≤ edge.right.parameter) :
    (time - left.parameter) ^ 2 ≤ (right.parameter - left.parameter) ^ 2 := by
  have bounds := dyadicEdges_bounds depth left right ordered edge member
  have lower := Arithmetic.sub_nonneg_direct (bounds.1.trans inside.1)
  have upper := Arithmetic.sub_le_sub_right_direct
    (inside.2.trans bounds.2.2) left.parameter
  exact Arithmetic.pow_le_pow_direct lower upper 2

/-- The squared width of an original ordered unit-interval edge is at most one. -/
theorem endpoint_width_le_one (left right : Endpoint) (ordered : left.parameter ≤ right.parameter) :
    (right.parameter - left.parameter) ^ 2 ≤ (1 : Fraction.Rational) := by
  have upper := Arithmetic.sub_le_sub_direct right.inside.2 left.inside.1
  have unit : (1 : Fraction.Rational) - 0 = 1 := by ring1
  rewrite [unit] at upper
  have squared := Arithmetic.pow_le_pow_direct
    (Arithmetic.sub_nonneg_direct ordered) upper 2
  exact squared.trans_eq (of_decide_eq_true rfl : (1 : Fraction.Rational) ^ 2 = 1)

/-- Every original dyadic edge at a sufficient finite depth pays the retained unit quarter-radius minimum. -/
theorem dyadicEdges_width_le (depth minimum : Nat) (enough : minimum ≤ depth) (left right : Endpoint)
    (ordered : left.parameter ≤ right.parameter) (edge : ParameterEdge)
    (member : edge ∈ dyadicEdges depth left right) :
    (edge.right.parameter - edge.left.parameter) ^ 2 ≤ Geometric.Basic.quarterRadius 1 minimum := by
  rewrite [UniformPrimitiveMesh.dyadicEdges_width depth left right edge member]
  exact (Geometric.Basic.quarterRadius_scale_mono (endpoint_width_le_one left right ordered) depth).trans
    (Geometric.Basic.quarterRadius_antitone (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 1) enough)

end Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

end
