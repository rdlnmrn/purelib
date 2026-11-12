module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling
public import Purelib.Approximation.Rational.Grid.Unit
public import Purelib.Data.Gaussian.Scale
import Purelib.Approximation.AccuracyRequest
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Algebra.NatCast
import Purelib.Tactic.Ring

/-! # One local parameter request on the original positive finite grid nodes

The literal unit-grid nodes and a Gaussian direction determine all absolute
offsets and their uniform local difference. The same local fourth-order
request is no larger than any positive node's absolute fourth-order request.
Their original positive AccuracyRequest owners therefore have an exact
minimum identity; no existing observation is assigned a smaller tolerance.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling

open Purelib
open Purelib.Algebra
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

/-- The uniform Gaussian parameter increment on the original rational unit grid. -/
@[expose] def gridIncrement (count : Nat) (direction : Canonical) : Canonical :=
  Scale.scale (1 / (count : Rational)) direction

/-- Read the actual absolute parameter offset at the SAME original bounded unit-grid node. -/
@[expose] def gridOffset (count : Nat) (index : Fin (count + 1)) (direction : Canonical) : Canonical :=
  Scale.scale (Grid.Unit.node count index) direction

/-- The SAME original first parameter-grid offset is exactly zero, without any Frame identification. -/
theorem gridOffset_zero (count : Nat) (direction : Canonical) :
    gridOffset count (0 : Fin (count + 1)) direction = 0 := by
  have node := Grid.Unit.node_zero (denominator := count) (0 : Fin (count + 1)) rfl
  have scaled := congrArg (fun value : Rational => Scale.scale value direction) node
  exact scaled.trans (by
    apply Purelib.Data.Gaussian.Basic.ext <;> change (0 : Rational) * _ = 0 <;> ring1)

/-- A positive grid count gives a positive original reciprocal width. -/
theorem gridWidth_positive (count : Nat) (positive : 0 < count) : 0 < (1 : Rational) / (count : Rational) :=
  Order.Field.div_pos_direct (by decide +kernel) (Cast.Order.natCast_pos_direct (n := count) positive)

/-- The SAME local reciprocal width is at most every original positive-node parameter. -/
theorem gridWidth_le_node (count : Nat) (positive : 0 < count) (index : Fin count) :
    (1 : Rational) / (count : Rational) ≤ Grid.Unit.node count index.succ := by
  have first : (1 : Rational) ≤ ((index.val + 1 : Nat) : Rational) :=
    Cast.Order.natCast_le_direct (m := 1) (n := index.val + 1) (Nat.succ_le_succ (Nat.zero_le index.val))
  have divided := Order.Field.divide_mono first (Cast.Order.natCast_pos_direct (n := count) positive)
  exact divided.trans_eq (Arithmetic.normalizedDiv_eq _ _).symm

/-- The local Gaussian increment is nonzero for an actual positive count and a moving direction. -/
theorem gridIncrement_nonzero (count : Nat) (positive : 0 < count) (direction : Canonical)
    (moving : direction ≠ 0) : gridIncrement count direction ≠ 0 := by
  have normPositive : 0 < Norm.Basic.normSq (gridIncrement count direction) :=
    (Order.Arithmetic.mul_pos_direct
      (Order.Arithmetic.pow_pos_direct (gridWidth_positive count positive) 2)
      (Norm.Basic.normSq_pos moving)).trans_eq (Scale.normSq_scale _ _).symm
  intro zero
  exact normPositive.ne' ((congrArg Norm.Basic.normSq zero).trans Norm.Basic.normSq_zero)

/-- Every actual positive grid-node offset is nonzero for the SAME moving direction. -/
theorem gridOffset_nonzero (count : Nat) (positive : 0 < count) (index : Fin count)
    (direction : Canonical) (moving : direction ≠ 0) : gridOffset count index.succ direction ≠ 0 := by
  have nodePositive := (gridWidth_positive count positive).trans_le (gridWidth_le_node count positive index)
  have normPositive : 0 < Norm.Basic.normSq (gridOffset count index.succ direction) :=
    (Order.Arithmetic.mul_pos_direct (Order.Arithmetic.pow_pos_direct nodePositive 2)
      (Norm.Basic.normSq_pos moving)).trans_eq (Scale.normSq_scale _ _).symm
  intro zero
  exact normPositive.ne' ((congrArg Norm.Basic.normSq zero).trans Norm.Basic.normSq_zero)

/-- Every original unit-grid offset pays the SAME original direction quadrance bound.

The proof includes both endpoints and permits a zero or negatively directed
Gaussian direction. Only the actual unit-node bounds and original scaling
norm law enter; no later patch or mesh-dependent minimum is used.
-/
theorem gridOffset_normSq_le (count : Nat) (positive : 0 < count) (index : Fin (count + 1))
    (direction : Canonical) : Norm.Basic.normSq (gridOffset count index direction) ≤ Norm.Basic.normSq direction := by
  have bounds := Grid.Unit.node_bounds positive index
  have power := Order.Arithmetic.pow_le_pow_direct bounds.1 bounds.2 2
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct power (Norm.Basic.normSq_nonneg direction)
  have upper : (1 : Rational) ^ 2 * Norm.Basic.normSq direction = Norm.Basic.normSq direction :=
    (congrArg (fun factor : Rational => factor * Norm.Basic.normSq direction)
      (show (1 : Rational) ^ 2 = 1 by decide +kernel)).trans (Field.one_mul _)
  exact (Scale.normSq_scale _ _).trans_le (scaled.trans_eq upper)

/-- The actual local increment quadrance is bounded by each original positive-node absolute offset quadrance. -/
theorem gridIncrement_normSq_le (count : Nat) (positive : 0 < count) (index : Fin count)
    (direction : Canonical) :
    Norm.Basic.normSq (gridIncrement count direction) ≤ Norm.Basic.normSq (gridOffset count index.succ direction) :=
  (Scale.normSq_scale _ _).trans_le
    ((Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Order.Arithmetic.pow_le_pow_direct (gridWidth_positive count positive).le
        (gridWidth_le_node count positive index) 2) (Norm.Basic.normSq_nonneg direction)).trans_eq
      (Scale.normSq_scale _ _).symm)

/-- Consecutive original grid offsets differ by precisely the SAME rational-width Gaussian increment. -/
theorem gridOffset_difference (count : Nat) (index : Fin count) (direction : Canonical) :
    gridOffset count index.succ direction - gridOffset count index.castSucc direction =
      gridIncrement count direction := by
  have difference : Grid.Unit.node count index.succ - Grid.Unit.node count index.castSucc =
      (1 : Rational) / (count : Rational) := by
    unfold Grid.Unit.node
    rewrite [Arithmetic.normalizedDiv_eq, Arithmetic.normalizedDiv_eq]
    change ((index.val + 1 : Nat) : Rational) / (count : Rational) -
      (index.val : Rational) / (count : Rational) = _
    rewrite [NatCast.add, Nat.cast_one]
    simp only [Field.div_eq_mul_inv_direct]
    ring1
  have affine : gridOffset count index.succ direction - gridOffset count index.castSucc direction =
      Scale.scale (Grid.Unit.node count index.succ - Grid.Unit.node count index.castSucc) direction := by
    apply Basic.ext <;>
      simp only [gridOffset, Scale.scale_re, Scale.scale_im, Basic.sub_re, Basic.sub_im] <;> ring1
  exact affine.trans (congrArg (fun factor : Rational => Scale.scale factor direction) difference)

/-- One genuine local fourth-order/spatial request has the SAME whole minimum with every positive absolute-node request.

The proof uses the actual grid fraction and original Gaussian scaling norm.
The index is a successor of an original Fin count, so node zero is excluded
constructively. Both nonzero facts are derived internally; constant direction
remains a separate case and is not silently passed to incrementRequest.
-/
theorem gridRequest_minimum (count : Nat) (positive : 0 < count) (index : Fin count)
    (direction : Canonical) (moving : direction ≠ 0) (spatial : AccuracyRequest) :
    (spatial.minimum (incrementRequest (gridIncrement count direction)
      (gridIncrement_nonzero count positive direction moving))).minimum
        (incrementRequest (gridOffset count index.succ direction)
          (gridOffset_nonzero count positive index direction moving)) =
      spatial.minimum (incrementRequest (gridIncrement count direction)
        (gridIncrement_nonzero count positive direction moving)) := by
  let common := spatial.minimum (incrementRequest (gridIncrement count direction)
    (gridIncrement_nonzero count positive direction moving))
  have fourth := Order.Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg (gridIncrement count direction))
    (gridIncrement_normSq_le count positive index direction) 2
  have paid : common.tolerance ≤
      (incrementRequest (gridOffset count index.succ direction)
        (gridOffset_nonzero count positive index direction moving)).tolerance :=
    (spatial.minimum_le_right (incrementRequest (gridIncrement count direction)
      (gridIncrement_nonzero count positive direction moving))).trans fourth
  apply AccuracyRequest.eq_of_tolerance_eq
  change min common.tolerance _ = common.tolerance
  exact Order.Basic.min_eq_left paid

end Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling

end
