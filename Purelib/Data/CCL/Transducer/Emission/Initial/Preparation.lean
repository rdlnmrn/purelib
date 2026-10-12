module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Sector.Budget
public import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
import Purelib.Data.CCL.Transducer.Emission.Low.Budget
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Productive progressive CCL output transducer

This is the finite-prefix controller for the redundant arithmetic layer.  A
loop mode represents a normalized progressive tail.  A residual mode is used
after a sector has been emitted but before equality with its representative
can be decided.  It either emits finite unary padding or, once apartness is
visible, changes to the exact normalized inverse chart.

The canonical terminating rational encoder is not changed.  This controller
only produces the progressive, potentially non-returning arithmetic word.
-/

namespace Purelib.Data.CCL.Transducer.Emission.Initial.Preparation

section
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
/-- Request the fixed positive initial radius-squared budget from the exact supplied process state. -/
def initialRefinedState (process :
  Approximation.Gaussian.Process) (state : process.State) :
    process.State :=
  process.refine state Emission.Initial.Budget.initialRadiusSq Emission.Initial.Budget.initialRadiusSq_pos

/-- The retained initial refinement has radius squared strictly below its exact initial budget. -/
theorem initialRefined_accurate (process :
  Approximation.Gaussian.Process) (state : process.State) :
    (process.ball (initialRefinedState process state)).radiusSq <
      Emission.Initial.Budget.initialRadiusSq :=
  process.accurate state Emission.Initial.Budget.initialRadiusSq Emission.Initial.Budget.initialRadiusSq_pos

/-- The retained initial refinement meets the larger uniform sector radius-squared budget. -/
theorem initialRefined_uniform (process :
  Approximation.Gaussian.Process) (state : process.State) :
    (process.ball (initialRefinedState process state)).radiusSq <
      Enclosure.Sector.Budget.uniformRadiusSq :=
  (initialRefined_accurate process state).trans
    Emission.Initial.Budget.initialRadiusSq_lt_uniform

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- An initial-budget ball with center squared norm below one bounds every possible value's squared norm by 43/40.

The bound applies to the same process state and its retained ball. A weighted norm estimate combines that center
condition with the exact radius-squared budget. -/
theorem candidate_norm_lt_low_unary_bound
    {process : Approximation.Gaussian.Process} {state : process.State}
    (accurate : (process.ball state).radiusSq < Emission.Initial.Budget.initialRadiusSq)
    (centerSmall : Data.Gaussian.Norm.Basic.normSq (process.ball state).center < 1)
    {value : Basic.Canonical} (possible : process.Possible state value) :
    Data.Gaussian.Norm.Basic.normSq value < 43 / 40 := by
  have decomposition :
      value = (value - (process.ball state).center) +
        (process.ball state).center := by
    apply Basic.ext <;>
      simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im] <;> ring1
  have weighted := Norm.Weighted.normSq_add_le_weighted
    (value - (process.ball state).center) (process.ball state).center
  have radiusScaled : 16 * (process.ball state).radiusSq <
      Enclosure.Sector.Budget.allowance / 10 :=
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (by decide) accurate).trans Emission.Initial.Budget.sixteen_mul_initial_lt_allowance_tenth
  have centerScaled : (16 / 15 : Fraction.Rational) *
      Data.Gaussian.Norm.Basic.normSq (process.ball state).center < (16 / 15) * 1 :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (by decide) centerSmall
  rw [decomposition]
  exact weighted.trans_lt (calc
    16 * Data.Gaussian.Norm.Basic.normSq (value - (process.ball state).center) +
          (16 / 15) * Data.Gaussian.Norm.Basic.normSq (process.ball state).center ≤
        16 * (process.ball state).radiusSq +
          (16 / 15) * Data.Gaussian.Norm.Basic.normSq (process.ball state).center :=
      add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (process.possible_inside possible) (by decide)) le_rfl
    _ < Enclosure.Sector.Budget.allowance / 10 +
        (16 / 15) * 1 :=
      Fraction.Order.Arithmetic.add_lt_add_direct radiusScaled centerScaled
    _ < Emission.Low.Budget.lowCenterSlack + (16 / 15) * 1 :=
      Fraction.Order.Arithmetic.add_lt_add_right_direct
        Emission.Low.Budget.allowance_tenth_lt_lowCenterSlack _
    _ < 43 / 40 := Emission.Low.Budget.lowUnary_budget)

/-- Gamma scaling sends every possible value of the retained accurate small-center ball below squared norm 43/20. -/
theorem scaled_candidate_norm_lt_low_upper
    {process : Approximation.Gaussian.Process} {state : process.State}
    (accurate : (process.ball state).radiusSq < Emission.Initial.Budget.initialRadiusSq)
    (centerSmall : Data.Gaussian.Norm.Basic.normSq (process.ball state).center < 1)
    {value : Basic.Canonical} (possible : process.Possible state value) :
    Data.Gaussian.Norm.Basic.normSq (Basic.Canonical.gamma * value) < 43 / 20 := by
  rw [Norm.Basic.normSq_mul, Constants.normSq_gamma]
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
    (by decide : (0 : Fraction.Rational) < 2)
    (candidate_norm_lt_low_unary_bound accurate centerSmall possible)
  have scaledIdentity : 2 * (43 / 40 : Fraction.Rational) = 43 / 20 := by
    calc
      2 * (43 / 40 : Fraction.Rational) = (2 * 43) / 40 := by
        rw [Fraction.Field.div_eq_mul_inv_direct,
          Fraction.Field.div_eq_mul_inv_direct]
        ring1
      _ = 43 / 20 := by
        apply Fraction.Field.div_eq_div_of_cross_mul
        · exact (Fraction.Cast.Order.natCast_pos_direct
            (n := 40) (by decide)).ne'
        · exact (Fraction.Cast.Order.natCast_pos_direct
            (n := 20) (by decide)).ne'
        · ring1
  exact scaled.trans_eq scaledIdentity

end

end Purelib.Data.CCL.Transducer.Emission.Initial.Preparation

end
