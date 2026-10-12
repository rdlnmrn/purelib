module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Enclosure.Sector.Budget
-- Exposed initial-budget proofs retain the original rational tenth certificates.
public import Purelib.Data.Rat.Bounds.Tenth
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

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

namespace Purelib.Data.CCL.Transducer.Emission.Initial.Budget

/-! ## Total initial-chart selection -/

open Purelib.Approximation.Gaussian in
open Purelib.Data.Rat in
/-- The exact initial enclosure radius-squared budget obtained by dividing the uniform sector budget by ten three times.
-/
def initialRadiusSq : Fraction.Rational :=
  ((Enclosure.Sector.Budget.uniformRadiusSq / 10) / 10) / 10

open Purelib.Approximation.Gaussian in
open Purelib.Data in
open Purelib.Data.Rat in
/-- The retained initial enclosure radius-squared budget is strictly positive. -/
theorem initialRadiusSq_pos : 0 <
  CCL.Transducer.Emission.Initial.Budget.initialRadiusSq := by
  unfold CCL.Transducer.Emission.Initial.Budget.initialRadiusSq
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Field.div_pos_direct
        Enclosure.Sector.Budget.uniformRadiusSq_pos (by decide))
      (by decide)) (by decide)

open Purelib.Approximation.Gaussian in
open Purelib.Data in
/-- The initial radius-squared budget is strictly below the uniform sector budget. -/
theorem initialRadiusSq_lt_uniform :
    CCL.Transducer.Emission.Initial.Budget.initialRadiusSq < Enclosure.Sector.Budget.uniformRadiusSq := by
  unfold CCL.Transducer.Emission.Initial.Budget.initialRadiusSq Enclosure.Sector.Budget.uniformRadiusSq
    Enclosure.Sector.Budget.allowance
  decide

open Purelib.Approximation.Gaussian in
open Purelib.Data in
open Purelib.Data.Rat in
/-- The initial radius-squared budget is strictly below one tenth of the uniform sector budget. -/
private theorem initialRadiusSq_lt_uniform_tenth :
    CCL.Transducer.Emission.Initial.Budget.initialRadiusSq <
      Enclosure.Sector.Budget.uniformRadiusSq / 10 := by
  let first := Enclosure.Sector.Budget.uniformRadiusSq / 10
  let second := first / 10
  have firstPositive : 0 < first :=
    Fraction.Order.Field.div_pos_direct
      Enclosure.Sector.Budget.uniformRadiusSq_pos Bounds.Tenth.ten_pos
  have secondPositive : 0 < second :=
    Fraction.Order.Field.div_pos_direct firstPositive Bounds.Tenth.ten_pos
  exact (Bounds.Tenth.div_ten_lt_self secondPositive).trans
    (Bounds.Tenth.div_ten_lt_self firstPositive)

open Purelib.Approximation.Gaussian in
open Purelib.Data.Rat in
/-- Sixteen times one tenth of the uniform radius-squared budget equals one tenth of the sector allowance. -/
private theorem sixteen_mul_uniform_tenth :
    16 * (Enclosure.Sector.Budget.uniformRadiusSq / 10) =
      Enclosure.Sector.Budget.allowance / 10 := by
  have sixteenDivOne : (16 / 1 : Fraction.Rational) = 16 :=
    calc
      (16 / 1 : Fraction.Rational) = (16 / 1) * 1 :=
        (Fraction.Field.mul_one_direct _).symm
      _ = 16 :=
        Fraction.Field.div_mul_cancel_of_ne 16 1 (by decide)
  have uniformTimesSixteen :
      Enclosure.Sector.Budget.uniformRadiusSq * 16 =
        Enclosure.Sector.Budget.allowance := by
    unfold Enclosure.Sector.Budget.uniformRadiusSq
    exact Fraction.Field.div_mul_cancel_of_ne
      Enclosure.Sector.Budget.allowance 16 (by decide)
  calc
    16 * (Enclosure.Sector.Budget.uniformRadiusSq / 10) =
        (Enclosure.Sector.Budget.uniformRadiusSq / 10) * 16 :=
      Fraction.Field.mul_comm _ _
    _ = (Enclosure.Sector.Budget.uniformRadiusSq / 10) *
        (16 / 1) := by rw [sixteenDivOne]
    _ = (Enclosure.Sector.Budget.uniformRadiusSq * 16) /
        (10 * 1) :=
      Fraction.Field.div_mul_div_direct _ _ _ _
    _ = Enclosure.Sector.Budget.allowance / 10 := by
      rw [uniformTimesSixteen,
        Fraction.Field.mul_one_direct]

open Purelib.Approximation.Gaussian in
open Purelib.Data in
open Purelib.Data.Rat in
/-- Sixteen times the initial radius-squared budget is strictly below one tenth of the sector allowance. -/
public theorem sixteen_mul_initial_lt_allowance_tenth :
    16 * CCL.Transducer.Emission.Initial.Budget.initialRadiusSq <
      Enclosure.Sector.Budget.allowance / 10 := by
  exact (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
    (by decide) CCL.Transducer.Emission.Initial.Budget.initialRadiusSq_lt_uniform_tenth).trans_eq
      CCL.Transducer.Emission.Initial.Budget.sixteen_mul_uniform_tenth

open Purelib.Approximation.Gaussian in
open Purelib.Data.Rat in
/-- The fixed sector allowance is strictly below one twenty-fifth. -/
public theorem allowance_lt_one_twenty_fifth :
    Enclosure.Sector.Budget.allowance < (1 / 25 : Fraction.Rational) := by
  unfold Enclosure.Sector.Budget.allowance
  decide

end Purelib.Data.CCL.Transducer.Emission.Initial.Budget

end
