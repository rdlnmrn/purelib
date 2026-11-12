module

public import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Algebra.Field.Midpoint
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Exact parameter bounds for retained dyadic edges

Every original dyadic edge has the original signed interval's square
scaled by its finite quarter radius. Both original endpoint records remain
unchanged, including their unit-interval certificates.
-/

namespace Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

open Purelib
open Purelib.Data.Rat
open Purelib.Approximation.Rational.Geometric
open Purelib.Algebra.Field

/-- The actual original dyadic edge list retained with its exact depth and original endpoint equation. -/
public abbrev DyadicEdges (depth : Nat) (left right : Endpoint) :=
  { value : List ParameterEdge // value = dyadicEdges depth left right }

/-- Squaring either midpoint half gives one quarter of the original signed parameter-displacement square. -/
public theorem midpoint_parameterSquares (left right : Coordinate) :
    (midpoint left right - left) ^ 2 = (right - left) ^ 2 / 4 ∧
      (right - midpoint left right) ^ 2 = (right - left) ^ 2 / 4 := by
  have first := Midpoint.left_sub_midpoint_coordinate left right (by decide : (2 : Coordinate) ≠ 0)
  have last := Midpoint.right_sub_midpoint_coordinate left right (by decide : (2 : Coordinate) ≠ 0)
  change left - midpoint left right = _ at first
  change right - midpoint left right = _ at last
  constructor
  · rewrite [show (midpoint left right - left) ^ 2 = (left - midpoint left right) ^ 2 by ring1, first]
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    have halfSquare : ((2 : Coordinate)⁻¹) ^ 2 = (4 : Coordinate)⁻¹ := by decide +kernel
    calc
      _ = (right - left) ^ 2 * ((2 : Coordinate)⁻¹) ^ 2 := by ring1
      _ = _ := by rewrite [halfSquare]; rfl
  · rewrite [last]
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    have halfSquare : ((2 : Coordinate)⁻¹) ^ 2 = (4 : Coordinate)⁻¹ := by decide +kernel
    calc
      _ = (right - left) ^ 2 * ((2 : Coordinate)⁻¹) ^ 2 := by ring1
      _ = _ := by rewrite [halfSquare]; rfl

/-- Every retained dyadic edge has exactly the original parameter-displacement square at its finite depth. -/
public theorem dyadicEdges_parameterSquare (depth : Nat) (left right : Endpoint)
    (edge : ParameterEdge) (member : edge ∈ dyadicEdges depth left right) :
    (edge.right.parameter - edge.left.parameter) ^ 2 =
      Basic.quarterRadius ((right.parameter - left.parameter) ^ 2) depth := by
  induction depth generalizing left right with
  | zero =>
      have same := Data.List.Membership.mem_singleton.mp member
      cases same
      rewrite [Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct]
      rfl
  | succ depth previous =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
      change edge ∈ dyadicEdges depth left middle ++ dyadicEdges depth middle right at member
      cases Data.List.Membership.mem_append.mp member with
      | inl before =>
          rewrite [previous left middle before]
          change Basic.quarterRadius ((midpoint left.parameter right.parameter - left.parameter) ^ 2) depth = _
          rewrite [(midpoint_parameterSquares left.parameter right.parameter).1,
            Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow, pow_succ]
          simp only [Fraction.Field.div_eq_mul_inv_direct]
          ring1
      | inr after =>
          rewrite [previous middle right after]
          change Basic.quarterRadius ((right.parameter - midpoint left.parameter right.parameter) ^ 2) depth = _
          rewrite [(midpoint_parameterSquares left.parameter right.parameter).2,
            Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow, pow_succ]
          simp only [Fraction.Field.div_eq_mul_inv_direct]
          ring1

/-- The two retained unit-interval endpoint certificates bound their signed parameter-displacement square by one. -/
public theorem endpoint_parameterSquare_le (left right : Endpoint) :
    (right.parameter - left.parameter) ^ 2 ≤ (1 : Coordinate) := by
  have lower := Fraction.Order.Arithmetic.sub_le_sub_direct right.inside.1 left.inside.2
  have upper := Fraction.Order.Arithmetic.sub_le_sub_direct right.inside.2 left.inside.1
  have lower' : -(1 : Coordinate) ≤ right.parameter - left.parameter := by
    exact (show -(1 : Coordinate) = 0 - 1 by ring1).trans_le lower
  have upper' : right.parameter - left.parameter ≤ (1 : Coordinate) := upper.trans_eq (by ring1)
  exact (Data.Rat.Bounds.Square.sq_le_sq_of_bounds lower' upper').trans_eq (by ring1)

/-- Every actual retained dyadic edge's parameter-displacement square meets the unit-scale quarter radius. -/
public theorem dyadicEdges_parameterSquare_le (depth : Nat) (left right : Endpoint)
    (edge : ParameterEdge) (member : edge ∈ dyadicEdges depth left right) :
    (edge.right.parameter - edge.left.parameter) ^ 2 ≤ Basic.quarterRadius 1 depth := by
  rewrite [dyadicEdges_parameterSquare depth left right edge member]
  exact Basic.quarterRadius_scale_mono (endpoint_parameterSquare_le left right) depth

end Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
