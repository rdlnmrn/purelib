module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Polynomial.Ascending.Gaussian.Evaluation

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

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

namespace Purelib.Polynomial.Ascending.Gaussian.Truncation.Error

/-! ## Explicit finite truncation -/

/-- Quadrance budget for evaluating one displayed finite coefficient list. -/
def coefficientNormBudget : List Gaussian.Basic.Canonical
  → Fraction.Rational → Fraction.Rational
  | [], _ => 0
  | coefficient :: remaining, inputNormSq =>
      2 * (Data.Gaussian.Norm.Basic.normSq coefficient +
        inputNormSq * coefficientNormBudget remaining
          inputNormSq)

/-- The finite coefficient norm budget is nonnegative whenever the supplied input quadrance is nonnegative. -/
theorem coefficientNormBudget_nonneg : ∀ coefficients
  inputNormSq,
    0 ≤ inputNormSq → 0 ≤ coefficientNormBudget coefficients inputNormSq
  | [], inputNormSq, _inputNonnegative => le_rfl
  | coefficient :: remaining, inputNormSq, inputNonnegative =>
      Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg (Gaussian.Norm.Basic.normSq_nonneg coefficient)
          (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct inputNonnegative
            (coefficientNormBudget_nonneg remaining inputNormSq
              inputNonnegative)))

/-- The finite coefficient norm budget bounds the Gaussian Horner value's quadrance.

The recursive budget uses the squared norm of each retained coefficient and the supplied input's squared norm. -/
theorem eval_normSq_le : ∀ coefficients (input :
  Gaussian.Basic.Canonical),
    Data.Gaussian.Norm.Basic.normSq (Ascending.Gaussian.Evaluation.evalList coefficients input) ≤
      coefficientNormBudget coefficients (Data.Gaussian.Norm.Basic.normSq input)
  | [], input => by
      change Data.Gaussian.Norm.Basic.normSq (0 : Gaussian.Basic.Canonical) ≤ 0
      rw [Gaussian.Norm.Basic.normSq_zero]
  | coefficient :: remaining, input => by
      change Data.Gaussian.Norm.Basic.normSq (coefficient + input * Ascending.Gaussian.Evaluation.evalList remaining
        input) ≤ _
      calc
        Data.Gaussian.Norm.Basic.normSq (coefficient + input * Ascending.Gaussian.Evaluation.evalList remaining
          input) ≤
            2 * (Data.Gaussian.Norm.Basic.normSq coefficient +
              Data.Gaussian.Norm.Basic.normSq (input * Ascending.Gaussian.Evaluation.evalList remaining input)) :=
          Gaussian.Norm.Bounds.normSq_add_le_two _ _
        _ = 2 * (Data.Gaussian.Norm.Basic.normSq coefficient +
              Data.Gaussian.Norm.Basic.normSq input * Data.Gaussian.Norm.Basic.normSq
                (Ascending.Gaussian.Evaluation.evalList remaining input)) := by
          rw [Gaussian.Norm.Basic.normSq_mul]
        _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq coefficient +
              Data.Gaussian.Norm.Basic.normSq input *
                coefficientNormBudget remaining (Data.Gaussian.Norm.Basic.normSq
                  input)) := by
          apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
            (by decide)
          exact add_le_add le_rfl
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (eval_normSq_le remaining input)
                (Gaussian.Norm.Basic.normSq_nonneg input))
        _ = coefficientNormBudget (coefficient :: remaining)
            (Data.Gaussian.Norm.Basic.normSq input) := rfl

/-- Split the value of two concatenated coefficient blocks into the prefix value and shifted tail value.

The tail contribution is multiplied by the input to the retained prefix length. -/
theorem eval_append : ∀ (retained discarded : List
  Gaussian.Basic.Canonical)
    (input : Gaussian.Basic.Canonical),
    Ascending.Gaussian.Evaluation.evalList (retained ++ discarded) input =
      Ascending.Gaussian.Evaluation.evalList retained input + input ^ retained.length *
        Ascending.Gaussian.Evaluation.evalList discarded input
  | [], discarded, input => by
      change Ascending.Gaussian.Evaluation.evalList discarded input = 0 + 1 * Ascending.Gaussian.Evaluation.evalList
        discarded input
      rw [Gaussian.Basic.one_mul,
        Gaussian.Basic.zero_add]
  | coefficient :: remaining, discarded, input => by
      rw [List.cons_append]
      simp only [Ascending.Gaussian.Evaluation.evalList, List.length_cons]
      rw [eval_append remaining discarded input, pow_succ]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- Exact finite truncation error: only the explicitly discarded displayed
tail is charged.  There is no unmentioned infinite remainder. -/
theorem truncation_error_le (retained discarded : List
  Gaussian.Basic.Canonical)
    (input : Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (Ascending.Gaussian.Evaluation.evalList (retained ++ discarded) input -
      Ascending.Gaussian.Evaluation.evalList retained input) ≤
      Data.Gaussian.Norm.Basic.normSq (input ^ retained.length) *
        coefficientNormBudget discarded (Data.Gaussian.Norm.Basic.normSq input)
          := by
  rw [eval_append]
  have identity :
      Ascending.Gaussian.Evaluation.evalList retained input + input ^ retained.length *
        Ascending.Gaussian.Evaluation.evalList discarded input -
          Ascending.Gaussian.Evaluation.evalList retained input =
        input ^ retained.length * Ascending.Gaussian.Evaluation.evalList discarded input := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
        Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
  rw [identity, Gaussian.Norm.Basic.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (eval_normSq_le discarded input)
    (Gaussian.Norm.Basic.normSq_nonneg (input ^ retained.length))
end Purelib.Polynomial.Ascending.Gaussian.Truncation.Error

end
