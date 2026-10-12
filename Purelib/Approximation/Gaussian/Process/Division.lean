module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Division
public import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Request.Basic
public import Purelib.Approximation.Gaussian.Request.Division
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Request.Basic

open Purelib.Data.Rat

namespace Purelib.Approximation.Gaussian.Process

/-- Divide two stateful enclosure processes using the original denominator's
uniform apartness certificate.

Paired states retain both operand readings; refinement uses only their stored
centre bounds and the retained denominator lower quadrance. -/
@[expose] public def div (left right : Process) (apart : Process.Apart right) :
  Process where
  State := left.State × right.State
  ball state := (left.ball state.1).div (right.ball state.2)
    (Apart.atState apart state.2)
  Possible state value := ∃ x y : Data.Gaussian.Basic.Canonical,
    left.Possible state.1 x ∧ right.Possible state.2 y ∧ value = x / y
  witness state := by
    rcases left.witness state.1 with ⟨x, xPossible⟩
    rcases right.witness state.2 with ⟨y, yPossible⟩
    exact ⟨x / y, x, y, xPossible, yPossible, rfl⟩
  possible_inside := by
    rintro state value ⟨x, y, xPossible, yPossible, rfl⟩
    exact Enclosure.Ball.contains_div
      (Apart.atState apart state.2) (left.possible_inside xPossible)
      (right.possible_inside yPossible)
  refine state target positive :=
    -- As for multiplication, the target uses only the global bounds, so
    -- evaluating the two current balls here would be redundant finite work.
    let leftName := Name.centerOnly 0 left.centerBound
      left.centerBound_nonneg (by
        rw [Data.Gaussian.Norm.Basic.normSq_zero]
        exact left.centerBound_nonneg)
    let rightName := Name.centerOnly 0 right.centerBound
      right.centerBound_nonneg (by
        rw [Data.Gaussian.Norm.Basic.normSq_zero]
        exact right.centerBound_nonneg)
    let inputTarget := Name.divisionInputTarget
      leftName rightName apart.lowerSq target
    let inputPositive := Name.divisionInputTarget_pos
      leftName rightName apart.lowerSq apart.positive positive
    (left.refine state.1 inputTarget inputPositive,
      right.refine state.2 inputTarget inputPositive)
  refine_persists := by
    rintro state target positive value
      ⟨x, y, xPossible, yPossible, equal⟩
    exact ⟨x, y,
      left.refine_persists state.1 _ _ xPossible,
      right.refine_persists state.2 _ _ yPossible,
      equal⟩
  accurate := by
    intro state target positive
    let leftName := Name.centerOnly (left.ball state.1).center
      left.centerBound left.centerBound_nonneg (left.center_bounded state.1)
    let rightName := Name.centerOnly (right.ball state.2).center
      right.centerBound right.centerBound_nonneg (right.center_bounded state.2)
    apply Name.div_radius_lt leftName rightName apart.lowerSq apart.positive
    · exact positive
    · exact left.accurate state.1 _ _
    · exact right.accurate state.2 _ _
    · exact left.center_bounded _
    · exact right.center_bounded _
    · rfl
  centerBound := left.centerBound / apart.lowerSq
  centerBound_nonneg :=
    Fraction.Order.Field.div_nonneg_direct left.centerBound_nonneg
      apart.positive.le
  center_bounded := by
    intro state
    have centerLower : apart.lowerSq ≤ Data.Gaussian.Norm.Basic.normSq (right.ball state.2).center :=
      apart.lower state.2 (right.ball state.2).contains_center
    have centerPositive : 0 < Data.Gaussian.Norm.Basic.normSq (right.ball state.2).center :=
      apart.positive.trans_le centerLower
    have centerNonzero : (right.ball state.2).center ≠ 0 := by
      intro centerZero
      rw [centerZero, Data.Gaussian.Norm.Basic.normSq_zero] at centerPositive
      exact (lt_irrefl _ centerPositive).elim
    change Data.Gaussian.Norm.Basic.normSq
      ((left.ball state.1).center / (right.ball state.2).center) ≤
      left.centerBound / apart.lowerSq
    rw [Data.Gaussian.Field.normSq_div _ _ centerNonzero]
    calc
      Data.Gaussian.Norm.Basic.normSq (left.ball state.1).center *
          (Data.Gaussian.Norm.Basic.normSq (right.ball state.2).center)⁻¹ =
          Data.Gaussian.Norm.Basic.normSq (left.ball state.1).center /
            Data.Gaussian.Norm.Basic.normSq (right.ball state.2).center := rfl
      _ ≤ left.centerBound / Data.Gaussian.Norm.Basic.normSq (right.ball state.2).center := by
        apply (Fraction.Order.Field.div_le_iff_pos centerPositive).2
        calc
          Data.Gaussian.Norm.Basic.normSq (left.ball state.1).center ≤ left.centerBound :=
            left.center_bounded state.1
          _ = (left.centerBound / Data.Gaussian.Norm.Basic.normSq (right.ball state.2).center) *
              Data.Gaussian.Norm.Basic.normSq (right.ball state.2).center :=
            (Fraction.Field.div_mul_cancel_of_ne
              left.centerBound _ centerPositive.ne').symm
      _ ≤ left.centerBound / apart.lowerSq :=
        Fraction.Order.Field.div_le_div_of_nonneg_left_direct
          left.centerBound_nonneg apart.positive centerLower

end Purelib.Approximation.Gaussian.Process
