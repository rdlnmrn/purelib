module

public import Purelib.Calculus.Linear.Euler.Blocks
public import Purelib.Algebra.Recurrence.Affine.Constant
public import Purelib.Approximation.AccuracyRequest
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Computed fine counts for requested finite Euler endpoint quadrance

The original affine response on the fixed coarse count gives a rational
scale. The original bounded quarter-radius Selection computes a positive
fourth-power refinement before any fine node is acquired.
-/

public section

namespace Purelib.Calculus.Linear.Euler

open Purelib
open Purelib.Algebra.FiniteSum.Prefix
open Purelib.Algebra.Recurrence
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

/-- The original zero-initial doubling recurrence responds nonnegatively to unit forcing. -/
theorem doublingResponse_nonnegative (count : Nat) :
    0 ≤ Affine.iterate (fun _ => (2 : Rational)) (fun _ => 1) 0 count :=
  Affine.iterate_nonnegative _ _ _ _ (by decide) (fun _ _ => by decide) (fun _ _ => by decide)

/-- The actual block forcing is bounded by four times the fixed factor divided by positive refinement.

The coarse count and refinement are both positive. Their original count
product gives the fine width. Its exact block-width readback, unit bound
and reciprocal order are the only estimates used.
-/
theorem blockForcing_le (blocks refinement : Nat) (positiveBlocks : 0 < blocks)
    (positiveRefinement : 0 < refinement) (factor : Rational) (factorNonnegative : 0 ≤ factor) :
    2 * ((refinement : Rational) *
      (factor * ((1 / ((blocks * refinement : Nat) : Rational)) + 1) *
        (1 / ((blocks * refinement : Nat) : Rational)) ^ 3)) ≤ 4 * factor / (refinement : Rational) := by
  let width : Rational := 1 / ((blocks * refinement : Nat) : Rational)
  have refinementPositive := Cast.Order.natCast_pos_direct positiveRefinement
  have countPositive := Cast.Order.natCast_pos_direct (Nat.mul_pos positiveBlocks positiveRefinement)
  have widthPositive : 0 < width := Order.Field.div_pos_direct (by decide) countPositive
  have widthUnit : width ≤ 1 := reciprocalWidth_le_one _ (Nat.mul_pos positiveBlocks positiveRefinement)
  have blockWidth : (refinement : Rational) * width = 1 / (blocks : Rational) :=
    (coordinateSum_constant width refinement).symm.trans (reciprocalWidth_sum blocks refinement positiveRefinement)
  have blockUnit : (refinement : Rational) * width ≤ 1 :=
    blockWidth.trans_le (reciprocalWidth_le_one blocks positiveBlocks)
  have denominatorOrder : (refinement : Rational) ≤ ((blocks * refinement : Nat) : Rational) :=
    (Fraction.Field.one_mul (refinement : Rational)).symm.trans_le
      ((Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Cast.Order.natCast_le_direct (m := 1) (n := blocks) positiveBlocks) refinementPositive.le).trans_eq
          (Algebra.NatCast.mul (R := Rational) blocks refinement).symm)
  have inverseOrder := Order.Field.inv_le_inv_of_pos_direct refinementPositive denominatorOrder
  have widthOrder : width ≤ 1 / (refinement : Rational) :=
    Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inverseOrder (by decide : (0 : Rational) ≤ 1)
  have squareUnit : width ^ 2 ≤ width :=
    (show width ^ 2 = width * width by ring1).trans_le
      ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthUnit widthPositive.le).trans_eq
        (Fraction.Field.mul_one_direct width))
  have weightedCube : (refinement : Rational) * width ^ 3 ≤ 1 / (refinement : Rational) :=
    (((show (refinement : Rational) * width ^ 3 =
        ((refinement : Rational) * width) * width ^ 2 by ring1).trans_le
      (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct blockUnit
        (Order.Arithmetic.sq_nonneg_direct width))).trans_eq
          (Fraction.Field.one_mul (width ^ 2))).trans (squareUnit.trans widthOrder)
  have doubledFactorNonnegative : (0 : Rational) ≤ 2 * factor :=
    Order.Arithmetic.mul_nonneg_direct (by decide) factorNonnegative
  have widthPlus : width + 1 ≤ (2 : Rational) :=
    (Order.Arithmetic.add_le_add_direct widthUnit (Order.Basic.le_refl (1 : Rational))).trans_eq (by decide)
  have coefficient : 2 * factor * (width + 1) ≤ 4 * factor :=
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthPlus doubledFactorNonnegative).trans_eq (by ring1)
  have cubeNonnegative : (0 : Rational) ≤ (refinement : Rational) * width ^ 3 :=
    Order.Arithmetic.mul_nonneg_direct refinementPositive.le
      (Order.Arithmetic.pow_nonneg_direct widthPositive.le 3)
  have actual := (show 2 * ((refinement : Rational) * (factor * (width + 1) * width ^ 3)) =
      (2 * factor * (width + 1)) * ((refinement : Rational) * width ^ 3) by ring1).trans_le
    ((Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficient cubeNonnegative).trans
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct weightedCube
        (Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 4) factorNonnegative)))
  exact actual.trans_eq (by
    rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
    ring1)

/-- Compute the fixed rational quarter-radius scale from the original coarse response and Taylor factor. -/
@[expose] def endpointScale (blocks : Nat) (factor : Rational) : Rational :=
  4 * Affine.iterate (fun _ => (2 : Rational)) (fun _ => 1) 0 blocks * factor

/-- The original coarse response gives a nonnegative endpoint scale, including zero factors. -/
theorem endpointScale_nonnegative (blocks : Nat) (factor : Rational) (nonnegative : 0 ≤ factor) :
    0 ≤ endpointScale blocks factor :=
  Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct (by decide) (doublingResponse_nonnegative blocks)) nonnegative

/-- The same original affine block bound is at most its fixed scale divided by the actual positive refinement. -/
theorem blockBound_le (blocks refinement : Nat) (positiveBlocks : 0 < blocks)
    (positiveRefinement : 0 < refinement) (factor : Rational) (factorNonnegative : 0 ≤ factor) :
    Affine.iterate (fun _ => (2 : Rational))
      (fun _ => 2 * ((refinement : Rational) *
        (factor * ((1 / ((blocks * refinement : Nat) : Rational)) + 1) *
          (1 / ((blocks * refinement : Nat) : Rational)) ^ 3))) 0 blocks ≤
      endpointScale blocks factor / (refinement : Rational) :=
  (Affine.iterate_constant_forcing 2 _ blocks).trans_le
    ((Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (blockForcing_le blocks refinement positiveBlocks positiveRefinement factor factorNonnegative)
      (doublingResponse_nonnegative blocks)).trans_eq
        (by
          change (4 * factor / (refinement : Rational)) *
            Affine.iterate (fun _ => (2 : Rational)) (fun _ => 1) 0 blocks =
              (4 * Affine.iterate (fun _ => (2 : Rational)) (fun _ => 1) 0 blocks * factor) /
                (refinement : Rational)
          rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
          ring1))

/-- Compute one original bounded Selection paying the requested endpoint quadrance from fixed coarse data. -/
@[expose] def endpointSelection (blocks : Nat) (factor : Rational) (nonnegative : 0 ≤ factor)
    (request : AccuracyRequest) : Search.Selection (endpointScale blocks factor) 0 request.tolerance :=
  Search.Selection.build _ (endpointScale_nonnegative blocks factor nonnegative) 0 request.tolerance request.positive

/-- The whole selection is the original finite search factory on the same fixed endpoint scale and tolerance. -/
theorem endpointSelection_eq (blocks : Nat) (factor : Rational) (nonnegative : 0 ≤ factor)
    (request : AccuracyRequest) : endpointSelection blocks factor nonnegative request =
      Search.Selection.build _ (endpointScale_nonnegative blocks factor nonnegative) 0
        request.tolerance request.positive := rfl

/-- Every actual successful original Selection supplies a computed positive refinement paying the affine endpoint bound.

The natural refinement is the literal power four of its retained stage.
Its cast identifies the original quarter-radius. No desired endpoint
comparison or existential choice of a good fine count is supplied.
-/
theorem blockBound_lt (blocks : Nat) (positiveBlocks : 0 < blocks) (factor : Rational)
    (nonnegative : 0 ≤ factor) (request : AccuracyRequest)
    (selection : Search.Selection (endpointScale blocks factor) 0 request.tolerance) :
    Affine.iterate (fun _ => (2 : Rational))
      (fun _ => 2 * (((4 ^ selection.stage : Nat) : Rational) *
        (factor * ((1 / ((blocks * 4 ^ selection.stage : Nat) : Rational)) + 1) *
          (1 / ((blocks * 4 ^ selection.stage : Nat) : Rational)) ^ 3))) 0 blocks < request.tolerance := by
  have actual := blockBound_le blocks (4 ^ selection.stage) positiveBlocks (Nat.pow_pos (by decide)) factor nonnegative
  have same : endpointScale blocks factor / ((4 ^ selection.stage : Nat) : Rational) =
      Basic.quarterRadius (endpointScale blocks factor) selection.stage :=
    congrArg (fun denominator : Rational => endpointScale blocks factor / denominator)
      (Algebra.NatCast.pow (R := Rational) 4 selection.stage)
  exact actual.trans_lt ((same.trans selection.allowance_eq.symm).trans_lt selection.accurate)

end Purelib.Calculus.Linear.Euler

end
