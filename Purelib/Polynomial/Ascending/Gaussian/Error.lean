module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.List.Proximity
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

namespace Purelib.Polynomial.Ascending.Gaussian.Error

/-- Coarse Horner error budget for `count` coefficients, a common
coefficient allowance, and the displayed input quadrance. -/
def evaluationErrorBudget : Nat → Fraction.Rational →
  Fraction.Rational → Fraction.Rational
  | 0, _, _ => 0
  | count + 1, coefficientAllowance, inputNormSq =>
      2 * (coefficientAllowance +
        inputNormSq * evaluationErrorBudget count coefficientAllowance
          inputNormSq)

/-- The finite Horner error budget is nonnegative for nonnegative coefficient allowance and input quadrance. -/
theorem evaluationErrorBudget_nonneg : ∀ count
    {coefficientAllowance inputNormSq : Fraction.Rational},
    0 ≤ coefficientAllowance → 0 ≤ inputNormSq →
      0 ≤ evaluationErrorBudget count coefficientAllowance inputNormSq
  | 0, _coefficientAllowance, _inputNormSq, _coefficientNonnegative,
      _inputNonnegative => le_rfl
  | count + 1, coefficientAllowance, inputNormSq,
      coefficientNonnegative, inputNonnegative =>
      Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg coefficientNonnegative
          (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct inputNonnegative
            (evaluationErrorBudget_nonneg count coefficientNonnegative
              inputNonnegative)))

/-- Split the difference of two nonempty Gaussian Horner values into their head difference and input-scaled tail
difference. -/
private theorem eval_difference_cons (actual displayed :
  Gaussian.Basic.Canonical)
    (actualTail displayedTail : List Gaussian.Basic.Canonical) (input : Gaussian.Basic.Canonical) :
    Ascending.Gaussian.Evaluation.evalList (actual :: actualTail) input -
        Ascending.Gaussian.Evaluation.evalList (displayed :: displayedTail) input =
      (actual - displayed) +
        input * (Ascending.Gaussian.Evaluation.evalList actualTail input - Ascending.Gaussian.Evaluation.evalList
          displayedTail input) := by
  apply Gaussian.Basic.ext <;>
    simp only [Ascending.Gaussian.Evaluation.evalList, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- Finite coefficient allowances compute a rational allowance for the
evaluated Taylor table. -/
theorem eval_error_le : ∀ (actual displayed : List
  Gaussian.Basic.Canonical)
    (input : Gaussian.Basic.Canonical) (coefficientAllowance : Fraction.Rational),
    Gaussian.List.Proximity.EntriesClose actual displayed coefficientAllowance →
      Data.Gaussian.Norm.Basic.normSq (Ascending.Gaussian.Evaluation.evalList actual input -
        Ascending.Gaussian.Evaluation.evalList displayed input) ≤
        evaluationErrorBudget actual.length coefficientAllowance
          (Data.Gaussian.Norm.Basic.normSq input)
  | [], [], input, coefficientAllowance, _valid => by
      change Data.Gaussian.Norm.Basic.normSq ((0 : Gaussian.Basic.Canonical) - 0) ≤ 0
      rw [Gaussian.Basic.sub_self, Gaussian.Norm.Basic.normSq_zero]
  | [], _ :: _, input, coefficientAllowance, valid => by
      exact False.elim valid
  | _ :: _, [], input, coefficientAllowance, valid => by
      exact False.elim valid
  | actual :: actualTail, displayed :: displayedTail, input,
      coefficientAllowance, valid => by
      rcases valid with ⟨headClose, tailValid⟩
      rw [eval_difference_cons]
      calc
        Data.Gaussian.Norm.Basic.normSq
            ((actual - displayed) +
              input * (Ascending.Gaussian.Evaluation.evalList actualTail input - Ascending.Gaussian.Evaluation.evalList
                displayedTail input)) ≤
          2 * (Data.Gaussian.Norm.Basic.normSq (actual - displayed) +
            Data.Gaussian.Norm.Basic.normSq (input *
              (Ascending.Gaussian.Evaluation.evalList actualTail input - Ascending.Gaussian.Evaluation.evalList
                displayedTail input))) :=
          Gaussian.Norm.Bounds.normSq_add_le_two _ _
        _ = 2 * (Data.Gaussian.Norm.Basic.normSq (actual - displayed) +
            Data.Gaussian.Norm.Basic.normSq input *
              Data.Gaussian.Norm.Basic.normSq (Ascending.Gaussian.Evaluation.evalList actualTail input -
                Ascending.Gaussian.Evaluation.evalList displayedTail input)) := by
          rw [Gaussian.Norm.Basic.normSq_mul]
        _ ≤ 2 * (coefficientAllowance +
            Data.Gaussian.Norm.Basic.normSq input *
              evaluationErrorBudget actualTail.length coefficientAllowance
                (Data.Gaussian.Norm.Basic.normSq input)) := by
          apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
            (by decide)
          exact add_le_add headClose
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (eval_error_le actualTail displayedTail input
                coefficientAllowance tailValid)
              (Gaussian.Norm.Basic.normSq_nonneg input))
        _ = evaluationErrorBudget (actual :: actualTail).length
            coefficientAllowance (Data.Gaussian.Norm.Basic.normSq input) := rfl
end Purelib.Polynomial.Ascending.Gaussian.Error

end
