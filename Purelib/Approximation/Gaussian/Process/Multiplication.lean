module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Mul
public import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Request.Basic
public import Purelib.Approximation.Gaussian.Request.Multiplication
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Prelude
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Request.Basic

open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction.Order

/-!
# Multiplication of stateful Gaussian enclosure processes

Paired states retain both original operand readings and refinement procedures.
The shared request uses only stored centre bounds; it does not evaluate current
balls to recover those bounds.
-/

namespace Purelib.Approximation.Gaussian.Process

/-- Multiply two stateful enclosure processes using pairs of their original
states.

Possible products retain both operand readings; refinement computes a common
request solely from the stored global centre bounds. -/
@[expose] public def mul (left right : Process) : Process where
  State := left.State × right.State
  ball state := (left.ball state.1).mul (right.ball state.2)
  Possible state value := ∃ x y : Data.Gaussian.Basic.Canonical,
    left.Possible state.1 x ∧ right.Possible state.2 y ∧ value = x * y
  witness state := by
    rcases left.witness state.1 with ⟨x, xPossible⟩
    rcases right.witness state.2 with ⟨y, yPossible⟩
    exact ⟨x * y, x, y, xPossible, yPossible, rfl⟩
  possible_inside := by
    rintro state value ⟨x, y, xPossible, yPossible, rfl⟩
    exact Enclosure.Ball.contains_mul
      (left.possible_inside xPossible) (right.possible_inside yPossible)
  refine state target positive :=
    -- The input target depends only on the stored global centre bounds.
    -- Zero-centred names avoid evaluating both current balls merely to
    -- discard their centres when that target is computed.
    let leftName := Name.centerOnly 0 left.centerBound
      left.centerBound_nonneg (by
        rw [Data.Gaussian.Norm.Basic.normSq_zero]
        exact left.centerBound_nonneg)
    let rightName := Name.centerOnly 0 right.centerBound
      right.centerBound_nonneg (by
        rw [Data.Gaussian.Norm.Basic.normSq_zero]
        exact right.centerBound_nonneg)
    let inputTarget := Name.multiplicativeInputTarget leftName rightName target
    let inputPositive := Name.multiplicativeInputTarget_pos
      leftName rightName positive
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
    apply Name.mul_radius_lt leftName rightName
    · exact positive
    · exact left.accurate state.1 _ _
    · exact right.accurate state.2 _ _
    · exact left.center_bounded _
    · exact right.center_bounded _
  centerBound := left.centerBound * right.centerBound
  centerBound_nonneg :=
    Arithmetic.mul_nonneg_direct left.centerBound_nonneg
      right.centerBound_nonneg
  center_bounded := by
    intro state
    change Data.Gaussian.Norm.Basic.normSq
      ((left.ball state.1).center * (right.ball state.2).center) ≤
      left.centerBound * right.centerBound
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct
      (left.center_bounded state.1) (right.center_bounded state.2)
      (Data.Gaussian.Norm.Basic.normSq_nonneg _) left.centerBound_nonneg

end Purelib.Approximation.Gaussian.Process
