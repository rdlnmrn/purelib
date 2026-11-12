module

public import Purelib.Algebra.Quadratic.Pair.Gaussian.Observation
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Shared generator precision for quadratic readings

One cached coefficient-quadrance ceiling can pay the visible radii of several
linear denotations sharing an original generator. The finite target reserves
half of an integration cell's allowance for that common generator reading.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Gaussian

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction

set_option genInjectivity false in
/-- A retained generator-refinement target computed from a coefficient-quadrance ceiling and local allowance.

The target is shared by all quadratic channels paid by the same ceiling.
Its denominator and positive target are computed once and retained with
their exact equations. -/
structure ReadingPrecision (ceiling allowance : Rational) where
  /-- The retained coefficient ceiling is nonnegative. -/
  nonnegative : 0 ≤ ceiling
  /-- The original local observation allowance is positive. -/
  positive : 0 < allowance
  /-- The cached positive denominator of the shared generator request. -/
  denominator : Rational
  /-- The denominator pays the actual quadratic reading-radius constants and coefficient ceiling. -/
  denominator_eq : denominator = 128 * (1 + ceiling)
  /-- The retained denominator is strictly positive. -/
  denominator_positive : 0 < denominator
  /-- The cached finite generator-refinement target. -/
  target : Rational
  /-- The target consumes this exact original allowance and retained denominator. -/
  target_eq : target = allowance / denominator
  /-- The actual cached target is strictly positive. -/
  target_positive : 0 < target

constructive_injectivity ReadingPrecision

namespace ReadingPrecision

/-- Compute one positive generator request for all channels under the retained coefficient ceiling. -/
@[expose] def build (ceiling allowance : Rational) (nonnegative : 0 ≤ ceiling)
    (positive : 0 < allowance) : ReadingPrecision ceiling allowance :=
  let denominator := 128 * (1 + ceiling)
  have denominatorPositive : 0 < denominator := Order.Arithmetic.mul_pos_direct
    (by decide +kernel) ((by decide : (0 : Rational) < 1).trans_le (le_add_of_nonneg_right nonnegative))
  let target := allowance / denominator
  ⟨nonnegative, positive, denominator, rfl, denominatorPositive, target, rfl,
    Order.Field.div_pos_direct positive denominatorPositive⟩

/-- Every retained coefficient below the shared ceiling spends at most half of the original allowance on root radius. -/
theorem payment {ceiling allowance : Rational} (precision : ReadingPrecision ceiling allowance)
    (coefficient : Canonical) (coefficient_le : Norm.Basic.normSq coefficient ≤ ceiling) :
    64 * Norm.Basic.normSq coefficient * precision.target ≤ allowance / 2 := by
  have enlarged : Norm.Basic.normSq coefficient ≤ 1 + ceiling :=
    coefficient_le.trans (le_add_of_nonneg_left (by decide : (0 : Rational) ≤ 1))
  have multiplied := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct enlarged precision.target_positive.le
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct multiplied
    (by decide +kernel : (0 : Rational) ≤ 64)
  have paid : precision.denominator * precision.target = allowance := by
    rewrite [precision.target_eq, Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne allowance precision.denominator precision.denominator_positive.ne'
  calc
    _ = 64 * (Norm.Basic.normSq coefficient * precision.target) := Fraction.Field.mul_assoc _ _ _
    _ ≤ 64 * ((1 + ceiling) * precision.target) := scaled
    _ = (128 * (1 + ceiling) * precision.target) / 2 := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct]
      have scalar : (128 : Rational) * (2 : Rational)⁻¹ = 64 := by decide +kernel
      calc
        _ = ((128 : Rational) * (2 : Rational)⁻¹) * ((1 + ceiling) * precision.target) := by
          rewrite [scalar]
          rfl
        _ = _ := by ring1
    _ = allowance / 2 := by rewrite [← precision.denominator_eq, paid]; rfl

end ReadingPrecision

end Purelib.Algebra.Quadratic.Pair.Gaussian

end
