module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement.Split
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Field

/-! # Ordered retained waist cells and their actual midpoint refinement steps -/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Integration.Polynomial.Gaussian.Path

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

set_option genInjectivity false in
/-- One original chart span with its complete cofactor owner, cubic lift and residual-controlled numerical cell.

The original site, family parameter, differential and oriented quarter remain
indices. All later subdivision operations use these exact retained inputs.
-/
structure Piece (data : Bounds.Data site parameter differential) (simple : differential.denominatorPairs = 0)
    (quarter : UnitCircuitQuarter) (regular : parameter ≠ criticalValue site)
    (bound : normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational))
    (accuracy : Fraction.Rational) where
  /-- The original closed rational chart span. -/
  span : Interval.Bounds
  /-- The complete original cofactor owner at this same span's lower endpoint. -/
  unit : Owner ((unitPolynomial site).eval (point site parameter (direction quarter span.lower) regular bound).base)
  /-- The original cubic lift retaining that same owner. -/
  lift : Conic.Lift (point site parameter (direction quarter span.lower) regular bound) unit
  /-- The actual numerical cell on that same lift and span. -/
  cell : Cell data simple lift accuracy

constructive_injectivity Piece

namespace Piece

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Bounds.Data site parameter differential} {simple : differential.denominatorPairs = 0}
variable {quarter : UnitCircuitQuarter} {regular : parameter ≠ criticalValue site}
variable {bound : normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)}
variable {accuracy : Fraction.Rational}

/-- Retain a supplied original numerical cell with its identical span, complete owner and cubic lift. -/
@[expose] def ofCell {span : Interval.Bounds}
    {unit : Owner ((unitPolynomial site).eval
      (point site parameter (direction quarter span.lower) regular bound).base)}
    {lift : Conic.Lift (point site parameter (direction quarter span.lower) regular bound) unit}
    (cell : Cell data simple lift accuracy) : Piece data simple quarter regular bound accuracy :=
  { span, unit, lift, cell }

/-- Read the retained original parameter-integration model. -/
@[expose] def model (piece : Piece data simple quarter regular bound accuracy) := piece.cell.model

/-- The original parameter cell's displacement quadrance is exactly its retained squared chart width. -/
theorem displacement_sq (piece : Piece data simple quarter regular bound accuracy) :
    normSq piece.model.displacement = piece.span.width ^ 2 := by
  rewrite [Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  change (piece.span.upper - piece.span.lower) * (piece.span.upper - piece.span.lower) +
    (0 - 0) * (0 - 0) = (piece.span.upper - piece.span.lower) ^ 2
  ring1

/-- Read the exact original models in their retained piece order. -/
@[expose] def models (pieces : List (Piece data simple quarter regular bound accuracy)) :
    List Purelib.Integration.Polynomial.Gaussian.Cell.Basic.CellModel := pieces.map model

/-- Retain the actual left and right children of one already completed split, in their original order. -/
@[expose] def children (piece : Piece data simple quarter regular bound accuracy) (split : Split piece.cell) :
    List (Piece data simple quarter regular bound (accuracy / 4)) :=
  [ofCell split.left, ofCell split.right]

/-- The retained child pieces read exactly the models of the same original split. -/
theorem children_models (piece : Piece data simple quarter regular bound accuracy) (split : Split piece.cell) :
    models (children piece split) = split.children.cells := rfl

/-- Every actual midpoint child has exactly one quarter of its parent's squared width and local allowance. -/
theorem children_bounds (piece : Piece data simple quarter regular bound accuracy) (split : Split piece.cell)
    (child : Piece data simple quarter regular bound (accuracy / 4)) (member : child ∈ children piece split) :
    child.span.width ^ 2 = piece.span.width ^ 2 / 4 ∧ child.cell.allowance = piece.cell.allowance / 4 := by
  have halfSquare : (piece.span.width / 2) ^ 2 = piece.span.width ^ 2 / 4 := by
    rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.mul_pow_direct]
    have inverseTwoSquare : ((2 : Fraction.Rational)⁻¹) ^ 2 = (4 : Fraction.Rational)⁻¹ := by decide +kernel
    rewrite [inverseTwoSquare]
    rfl
  cases member with
  | head =>
      constructor
      · change (Interval.Bisection.leftHalf piece.span).width ^ 2 = _
        rewrite [Interval.Bisection.leftHalf_width]
        exact halfSquare
      · exact split.left_allowance_eq
  | tail _ member =>
      cases member with
      | head =>
          constructor
          · change (Interval.Bisection.rightHalf piece.span).width ^ 2 = _
            rewrite [Interval.Bisection.rightHalf_width]
            exact halfSquare
          · exact split.right_allowance_eq
      | tail _ impossible => nomatch impossible

end Piece

set_option genInjectivity false in
/-- Actual cached midpoint splits of an ordered list of original residual-controlled cells.

Every head retains the completed original split of its exact parent. The
tail keeps the same original parent order; no owner preparation is replayed
when child models or comparisons are read back.
-/
inductive Steps {data : Bounds.Data site parameter differential} {simple : differential.denominatorPairs = 0}
    {quarter : UnitCircuitQuarter} {regular : parameter ≠ criticalValue site}
    {bound : normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)}
    {accuracy : Fraction.Rational} : List (Piece data simple quarter regular bound accuracy) → Type 1
  /-- The empty parent list requires no completed split. -/
  | nil : Steps []
  /-- Retain the actual head split and already completed tail steps. -/
  | cons {parent : Piece data simple quarter regular bound accuracy} {parents}
      (split : Split parent.cell) (tail : Steps parents) : Steps (parent :: parents)

constructive_injectivity Steps

namespace Steps

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Bounds.Data site parameter differential} {simple : differential.denominatorPairs = 0}
variable {quarter : UnitCircuitQuarter} {regular : parameter ≠ criticalValue site}
variable {bound : normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)}
variable {accuracy : Fraction.Rational}

/-- Compute and retain each actual midpoint split once, following the original parent list order. -/
@[expose] def build : (parents : List (Piece data simple quarter regular bound accuracy)) → Steps parents
  | [] => .nil
  | parent :: parents => .cons (Split.build parent.cell) (build parents)

/-- Read the ordered child pieces from the same retained completed splits. -/
@[expose] def children : {parents : List (Piece data simple quarter regular bound accuracy)} →
    Steps parents → List (Piece data simple quarter regular bound (accuracy / 4))
  | _, .nil => []
  | parent :: _, .cons split tail =>
      Piece.children parent split ++ children tail

/-- The actual ordered parent and child models carry the existing compatible refinement certificate. -/
@[expose] def compatible : {parents : List (Piece data simple quarter regular bound accuracy)} →
    (steps : Steps parents) → Basic.PathModel.CompatibleConstantPathRefinement
      (Piece.models parents) (Piece.models steps.children)
  | _, .nil => .nil
  | _, .cons split tail => .cons split.comparison (compatible tail)

/-- Every completed parent split contributes exactly two retained child pieces. -/
theorem children_length : {parents : List (Piece data simple quarter regular bound accuracy)} →
    (steps : Steps parents) → steps.children.length = 2 * parents.length
  | _, .nil => rfl
  | _, .cons split tail => by
      change ([_, _] ++ children tail).length = 2 * (_ :: _).length
      rewrite [List.length_append, children_length]
      simp only [List.length_cons, List.length_nil]
      omega0

/-- Actual children preserve the uniform parent bounds with exact quarter contraction. -/
theorem children_bounds : {parents : List (Piece data simple quarter regular bound accuracy)} →
    (steps : Steps parents) → (width allowance : Fraction.Rational) →
    (∀ parent ∈ parents, parent.span.width ^ 2 = width ∧ parent.cell.allowance = allowance) →
    ∀ child ∈ steps.children, child.span.width ^ 2 = width / 4 ∧ child.cell.allowance = allowance / 4
  | _, .nil, _, _, _, _, impossible => nomatch impossible
  | parent :: parents, .cons split tail, width, allowance, bounds, child, member => by
      change child ∈ Piece.children parent split ++ tail.children at member
      cases Purelib.Data.List.Membership.mem_append.mp member with
      | inl head =>
          have childBounds := parent.children_bounds split child head
          have parentBounds := bounds parent (List.Mem.head parents)
          rewrite [parentBounds.1, parentBounds.2] at childBounds
          exact childBounds
      | inr remaining =>
          exact tail.children_bounds width allowance
            (fun value occurrence => bounds value (List.Mem.tail parent occurrence)) child remaining

end Steps

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement
