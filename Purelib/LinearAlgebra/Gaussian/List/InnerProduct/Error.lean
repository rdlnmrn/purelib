module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.List.Proximity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite error transport for progressive Taylor tables

The progressive higher-jet layer emits every displayed coefficient.  This
module transports those finitely many coefficient allowances through Horner
evaluation and through an explicit finite truncation.  The bounds are coarse
recursive rational expressions; no omitted infinite tail or formal power
series is introduced.
-/

namespace Purelib.LinearAlgebra.Gaussian.List.InnerProduct.Error

/-! ## Displayed finite-dimensional directional transport -/

set_option backward.match.sparseCases false in
/-- Evaluate the finite list dot product in the supplied Gaussian direction.

The recursion stops when either input list ends. -/
def directionalEval : List Data.Gaussian.Basic.Canonical →
  List Data.Gaussian.Basic.Canonical → Data.Gaussian.Basic.Canonical
  | coefficient :: coefficients, direction :: directions =>
      coefficient * direction + directionalEval coefficients
        directions
  | _, _ => 0

/-- Accumulate a rational error allowance weighted by the squared norms of the direction entries.

Each recursive step doubles the sum of the current weighted allowance and the retained tail budget. -/
def directionalErrorBudget : List
  Data.Gaussian.Basic.Canonical → Fraction.Rational → Fraction.Rational
  | [], _ => 0
  | direction :: directions, coefficientAllowance =>
      2 * (Data.Gaussian.Norm.Basic.normSq direction * coefficientAllowance +
        directionalErrorBudget directions coefficientAllowance)

/-- A nonnegative entrywise allowance gives a nonnegative directional error budget. -/
theorem directionalErrorBudget_nonneg : ∀ directions
    {coefficientAllowance : Fraction.Rational}, 0 ≤ coefficientAllowance →
      0 ≤ directionalErrorBudget directions coefficientAllowance
  | [], _coefficientAllowance, _nonnegative => Fraction.Order.Basic.le_refl 0
  | direction :: directions, coefficientAllowance, nonnegative =>
      Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (show (0 : Fraction.Rational) + 0 ≤ _ from Fraction.Order.Arithmetic.add_le_add_direct
          (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
            (Data.Gaussian.Norm.Basic.normSq_nonneg direction) nonnegative)
          (directionalErrorBudget_nonneg directions nonnegative))

/-- The directional dot-product error satisfies the recursively accumulated budget.

Both coefficient lists have the direction length and their corresponding entries satisfy the supplied closeness
allowance. -/
theorem directional_error_le : ∀ (actual displayed
  directions : List Data.Gaussian.Basic.Canonical)
    (coefficientAllowance : Fraction.Rational),
    actual.length = directions.length →
    displayed.length = directions.length →
    Data.Gaussian.List.Proximity.EntriesClose actual displayed coefficientAllowance →
      Data.Gaussian.Norm.Basic.normSq (directionalEval actual
        directions -
        directionalEval displayed directions) ≤
          directionalErrorBudget directions coefficientAllowance
  | [], [], [], coefficientAllowance, _actualLength, _displayedLength,
      _valid => by
      change Data.Gaussian.Norm.Basic.normSq ((0 : Data.Gaussian.Basic.Canonical) - 0) ≤ 0
      rewrite [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
      exact Fraction.Order.Basic.le_refl 0
  | [], [], _ :: _, coefficientAllowance, actualLength, displayedLength,
      valid => by
      change 0 = Nat.succ _ at actualLength
      exact False.elim (Nat.noConfusion actualLength)
  | [], _ :: _, directions, coefficientAllowance, actualLength,
      displayedLength, valid => by
      exact False.elim valid
  | _ :: _, [], directions, coefficientAllowance, actualLength,
      displayedLength, valid => by
      exact False.elim valid
  | actual :: actualTail, displayed :: displayedTail, [],
      coefficientAllowance, actualLength, displayedLength, valid => by
      change Nat.succ _ = 0 at actualLength
      exact False.elim (Nat.noConfusion actualLength)
  | actual :: actualTail, displayed :: displayedTail,
      direction :: directions, coefficientAllowance, actualLength,
      displayedLength, valid => by
      rcases valid with ⟨headClose, tailValid⟩
      have actualTailLength : actualTail.length = directions.length := by
        exact Nat.succ.inj actualLength
      have displayedTailLength : displayedTail.length = directions.length := by
        exact Nat.succ.inj displayedLength
      have identity :
          directionalEval (actual :: actualTail) (direction ::
            directions) -
              directionalEval (displayed :: displayedTail)
                (direction :: directions) =
            (actual - displayed) * direction +
              (directionalEval actualTail directions -
                directionalEval displayedTail directions) := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [directionalEval, Data.Gaussian.Basic.sub_re,
            Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
            Data.Gaussian.Basic.mul_re,
            Data.Gaussian.Basic.mul_im] <;> ring1
      rw [identity]
      calc
        Data.Gaussian.Norm.Basic.normSq ((actual - displayed) * direction +
            (directionalEval actualTail directions -
              directionalEval displayedTail directions)) ≤
          2 * (Data.Gaussian.Norm.Basic.normSq ((actual - displayed) * direction) +
            Data.Gaussian.Norm.Basic.normSq (directionalEval
              actualTail directions -
              directionalEval displayedTail directions)) :=
          Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
        _ = 2 * (Data.Gaussian.Norm.Basic.normSq direction * Data.Gaussian.Norm.Basic.normSq (actual -
          displayed) +
            Data.Gaussian.Norm.Basic.normSq (directionalEval
              actualTail directions -
              directionalEval displayedTail directions)) := by
          rw [Data.Gaussian.Norm.Basic.normSq_mul]
          ring1
        _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq direction * coefficientAllowance +
            directionalErrorBudget directions coefficientAllowance) := by
          apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
            (by decide)
          exact Fraction.Order.Arithmetic.add_le_add_direct
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              headClose (Data.Gaussian.Norm.Basic.normSq_nonneg direction))
            (directional_error_le actualTail displayedTail
              directions
              coefficientAllowance actualTailLength displayedTailLength
              tailValid)
        _ = directionalErrorBudget (direction :: directions)
            coefficientAllowance := rfl
end Purelib.LinearAlgebra.Gaussian.List.InnerProduct.Error

end
