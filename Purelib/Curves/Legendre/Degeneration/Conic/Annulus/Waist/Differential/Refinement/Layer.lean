module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement.Piece
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Integration.Polynomial.Gaussian.Path.Uniform
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Cached dyadic layers of an original waist differential -/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Approximation.Rational

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Bounds.Data site parameter differential} {simple : differential.denominatorPairs = 0}
variable {quarter : UnitCircuitQuarter} {regular : parameter ≠ criticalValue site}
variable {bound : normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)}
variable {accuracy : Fraction.Rational}

set_option genInjectivity false in
/-- An ordered dyadic layer retaining its original waist pieces and their cached numerical model.

The initial piece and finite depth remain indices. Exact count, squared-width
and allowance equations describe these same pieces; the model caches their
original readback without preparing their owners or observations again.
-/
structure Layer {initialAccuracy : Fraction.Rational}
    (initial : Piece data simple quarter regular bound initialAccuracy) (depth : Nat) where
  /-- The actual common residual request at this layer. -/
  accuracy : Fraction.Rational
  /-- The request is the initial request divided by the original finite power of four. -/
  accuracy_eq : accuracy = Geometric.Basic.quarterRadius initialAccuracy depth
  /-- The actual retained ordered pieces at this residual request. -/
  pieces : List (Piece data simple quarter regular bound accuracy)
  /-- The exact original dyadic piece count. -/
  count : pieces.length = 2 ^ depth
  /-- Every retained span has the original squared-width quarter radius. -/
  widths : ∀ piece ∈ pieces,
    piece.span.width ^ 2 = Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth
  /-- Every retained cell has the original allowance quarter radius. -/
  allowances : ∀ piece ∈ pieces,
    piece.cell.allowance = Geometric.Basic.quarterRadius initial.cell.allowance depth
  /-- The cached numerical model of these same original pieces. -/
  model : Basic.PathModel
  /-- The cache reads exactly the retained original cells in their same order. -/
  model_cells : model.cells = Piece.models pieces

constructive_injectivity Layer

namespace Layer

variable {initial : Piece data simple quarter regular bound accuracy} {depth : Nat}

/-- Retain the original singleton layer with its identical complete piece and numerical cell. -/
@[expose] def ofPiece (initial : Piece data simple quarter regular bound accuracy) : Layer initial 0 :=
  { accuracy
    accuracy_eq := by
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct]
      rfl
    pieces := [initial]
    count := rfl
    widths := by
      intro piece member
      cases Membership.mem_singleton.mp member
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct]
      rfl
    allowances := by
      intro piece member
      cases Membership.mem_singleton.mp member
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct]
      rfl
    model := ⟨[initial.model]⟩
    model_cells := rfl }

/-- Assemble the next cached layer from these exact already completed midpoint splits.

The supplied steps retain each original split. Their child pieces and model
are computed once here, and all certificates consume those same caches.
-/
@[expose] def next (layer : Layer initial depth) (steps : Steps layer.pieces) : Layer initial (depth + 1) :=
  let pieces := steps.children
  let model : Basic.PathModel := ⟨Piece.models pieces⟩
  { accuracy := layer.accuracy / 4
    accuracy_eq := by
      rewrite [layer.accuracy_eq, Geometric.Basic.quarterRadius_eq_mul_pow,
        Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ, Fraction.Field.div_eq_mul_inv_direct]
      have quarter : (1 / 4 : Fraction.Rational) = (4 : Fraction.Rational)⁻¹ := by decide +kernel
      rewrite [quarter]
      ring1
    pieces
    count := by
      rewrite [Steps.children_length, layer.count, Nat.pow_succ]
      exact Nat.mul_comm _ _
    widths := by
      intro piece member
      have widths := steps.children_bounds
        (Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth)
        (Geometric.Basic.quarterRadius initial.cell.allowance depth)
        (fun parent parentMember => ⟨layer.widths parent parentMember, layer.allowances parent parentMember⟩)
        piece member
      rewrite [widths.1, Geometric.Basic.quarterRadius_eq_mul_pow,
        Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ, Fraction.Field.div_eq_mul_inv_direct]
      have quarter : (1 / 4 : Fraction.Rational) = (4 : Fraction.Rational)⁻¹ := by decide +kernel
      rewrite [quarter]
      ring1
    allowances := by
      intro piece member
      have allowances := steps.children_bounds
        (Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth)
        (Geometric.Basic.quarterRadius initial.cell.allowance depth)
        (fun parent parentMember => ⟨layer.widths parent parentMember, layer.allowances parent parentMember⟩)
        piece member
      rewrite [allowances.2, Geometric.Basic.quarterRadius_eq_mul_pow,
        Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ, Fraction.Field.div_eq_mul_inv_direct]
      have quarter : (1 / 4 : Fraction.Rational) = (4 : Fraction.Rational)⁻¹ := by decide +kernel
      rewrite [quarter]
      ring1
    model
    model_cells := rfl }

/-- The cached models carry the original compatible comparison of these same completed splits. -/
def compatible (layer : Layer initial depth) (steps : Steps layer.pieces) :
    Basic.PathModel.CompatibleConstantPathRefinement layer.model.cells (layer.next steps).model.cells := by
  rewrite [layer.model_cells]
  exact steps.compatible

/-- Transporting the model cache preserves the exact original ordered comparison cells. -/
theorem comparisonCells_eq (layer : Layer initial depth) (steps : Steps layer.pieces) :
    CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonCells (layer.compatible steps) =
      CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonCells steps.compatible := by
  cases layer with
  | mk accuracy accuracy_eq pieces count widths allowances model model_cells =>
      cases model with
      | mk cells =>
          cases model_cells
          rfl

/-- The exact finite piece count is also the count of the same cached numerical cells. -/
theorem model_count (layer : Layer initial depth) : layer.model.cells.length = 2 ^ depth := by
  rewrite [layer.model_cells]
  exact (Map.length_map ..).trans layer.count

/-- The cached model's aggregate allowance is bounded by the original squared span width and decaying allowance. -/
theorem aggregateAllowance_le (layer : Layer initial depth) :
    layer.model.aggregateAllowance ≤ initial.span.width ^ 2 *
      Geometric.Basic.quarterRadius initial.cell.allowance depth := by
  apply Basic.PathModel.uniform_aggregateAllowance_le layer.model depth _ _
    (Fraction.Order.Arithmetic.sq_nonneg_direct _) layer.model_count
  intro model member
  rewrite [layer.model_cells] at member
  rcases Map.mem_map.mp member with ⟨piece, pieceMember, rfl⟩
  constructor
  · rewrite [piece.displacement_sq, layer.widths piece pieceMember]
    exact Fraction.Order.Basic.le_refl _
  · exact (layer.allowances piece pieceMember).le

end Layer

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement
