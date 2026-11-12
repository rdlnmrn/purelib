module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Quantitative comparison of actual consecutive regular parallel layers -/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement

open Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement.PathModel

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Approximation
open Purelib.Approximation.Rational

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}

namespace Steps

/-- Every retained comparison cell has the actual child geometry and the paid parent-plus-child allowance. -/
theorem comparison_bounds : {parents : List (Piece data actual accuracy)} →
    (steps : Steps parents) → (width allowance : Fraction.Rational) →
    (∀ parent ∈ parents, parent.span.width ^ 2 = width ∧ parent.cell.allowance = allowance) →
    ∀ cell ∈ CompatibleConstantPathRefinement.comparisonCells steps.compatible,
      normSq cell.displacement = width / 4 ∧ cell.localAllowance = 2 * (allowance + allowance / 4)
  | _, .nil, _, _, _, _, impossible => nomatch impossible
  | parent :: parents, .cons split tail, width, allowance, bounds, cell, member => by
      change cell ∈ [Basic.PathModel.comparisonCell parent.model split.left.cell,
        Basic.PathModel.comparisonCell parent.model split.right.cell] ++
        CompatibleConstantPathRefinement.comparisonCells tail.compatible at member
      cases Membership.mem_append.mp member with
      | inl head =>
          have parentBounds := bounds parent (List.Mem.head parents)
          have childBound (child : Piece data actual accuracy.quarter)
              (member : child ∈ Piece.children parent split) :
              normSq (Basic.PathModel.comparisonCell parent.model child.model).displacement = width / 4 ∧
              (Basic.PathModel.comparisonCell parent.model child.model).localAllowance =
                2 * (allowance + allowance / 4) := by
            have childBounds := parent.children_bounds split child member
            constructor
            · change normSq child.model.displacement = _
              rewrite [child.displacement_sq, childBounds.1, parentBounds.1]
              rfl
            · change 2 * (parent.cell.allowance + child.cell.allowance) = _
              rewrite [childBounds.2, parentBounds.2]
              rfl
          cases head with
          | head =>
              exact childBound (Piece.ofCell
                (fun time contained => parent.within time (Interval.Bisection.leftHalf_subset contained)) split.left)
                (List.Mem.head _)
          | tail _ remaining =>
              cases remaining with
              | head =>
                  exact childBound (Piece.ofCell
                    (fun time contained => parent.within time (Interval.Bisection.rightHalf_subset contained))
                    split.right)
                    (List.Mem.tail _ (List.Mem.head _))
              | tail _ impossible => nomatch impossible
      | inr remaining =>
          exact tail.comparison_bounds width allowance
            (fun value occurrence => bounds value (List.Mem.tail parent occurrence)) cell remaining

end Steps

namespace Layer

variable {initial : Piece data actual accuracy} {depth : Nat}

/-- The actual consecutive comparison pays at most four original width-times-allowance quarter radii. -/
theorem comparisonAllowance_le (layer : Layer initial depth) (steps : Steps layer.pieces) :
    CompatibleConstantPathRefinement.comparisonAllowance (layer.compatible steps) ≤
      Geometric.Basic.quarterRadius (4 * initial.span.width ^ 2 * initial.cell.allowance) depth := by
  rewrite [CompatibleConstantPathRefinement.comparisonAllowance,
    layer.comparisonCells_eq]
  have bounds := steps.comparison_bounds
    (Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth)
    (Geometric.Basic.quarterRadius initial.cell.allowance depth)
    (fun parent member => ⟨layer.widths parent member, layer.allowances parent member⟩)
  have allowance := Basic.PathModel.uniform_aggregateAllowance_le
    ⟨CompatibleConstantPathRefinement.comparisonCells steps.compatible⟩
    (depth + 1) (initial.span.width ^ 2)
    (2 * (Geometric.Basic.quarterRadius initial.cell.allowance depth +
      Geometric.Basic.quarterRadius initial.cell.allowance depth / 4))
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (by
      rewrite [CompatibleConstantPathRefinement.comparisonCells_length]
      rewrite [Piece.models, Map.length_map, steps.children_length, layer.count, Nat.pow_succ]
      exact Nat.mul_comm _ _)
    (by
      intro cell member
      have cellBounds := bounds cell member
      constructor
      · rewrite [cellBounds.1, Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ, Fraction.Field.div_eq_mul_inv_direct]
        have quarter : (1 / 4 : Fraction.Rational) = (4 : Fraction.Rational)⁻¹ := by decide +kernel
        rewrite [quarter]
        apply Eq.le
        ring1
      · exact cellBounds.2.le)
  apply allowance.trans
  have localNonnegative := Geometric.Basic.quarterRadius_nonneg initial.cell.allowance_nonnegative depth
  have factorBound : 2 * (Geometric.Basic.quarterRadius initial.cell.allowance depth +
      Geometric.Basic.quarterRadius initial.cell.allowance depth / 4) ≤
      4 * Geometric.Basic.quarterRadius initial.cell.allowance depth := by
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (show (5 / 2 : Fraction.Rational) ≤ 4 by decide +kernel) localNonnegative
    apply Eq.trans_le _ scaled
    have factor : (5 / 2 : Fraction.Rational) = 2 * (1 + 1 / 4) := by decide +kernel
    rewrite [factor]
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    ring1
  apply (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct factorBound
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans_eq
  rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

end Layer

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement
