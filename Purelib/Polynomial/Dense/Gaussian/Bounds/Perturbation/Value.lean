module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.List.Proximity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Data.Gaussian

/-!
# Finite high-to-low Horner perturbation budgets

The original recursive budget retains one coefficientwise quadrance bound and
one input quadrance bound. Direct scalar and paired-list certificates compare
the same ordered finite Horner evaluations and their original coefficient counts.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Value

/-- Split the difference of two Horner evaluations into leading and tail terms.

The tails must have the same length, so their leading coefficients multiply the same power of the input. -/
private theorem evalCoeffs_sub_expansion
    (left right : Gaussian.Basic.Canonical) (leftTail rightTail : List Gaussian.Basic.Canonical)
    (input : Gaussian.Basic.Canonical) (tailLength : leftTail.length = rightTail.length) :
    Dense.Basic.DensePolynomial.evalCoeffs input
        (left :: leftTail) -
      Dense.Basic.DensePolynomial.evalCoeffs input
        (right :: rightTail) =
      (left - right) * input ^ leftTail.length +
        (Dense.Basic.DensePolynomial.evalCoeffs input leftTail -
          Dense.Basic.DensePolynomial.evalCoeffs input
            rightTail) := by
  rw [Dense.Basic.DensePolynomial.evalCoeffs_cons_expansion,
    Dense.Basic.DensePolynomial.evalCoeffs_cons_expansion,
    tailLength]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- Coarse square-root-free Horner perturbation budget for `count`
high-to-low coefficients, one coefficientwise quadrance bound, and one input
quadrance bound. -/
@[expose] public def hornerPerturbationBudget : Nat → Fraction.Rational → Fraction.Rational → Fraction.Rational
  | 0, _, _ => 0
  | count + 1, coefficientBound, inputNormSq =>
      2 * (coefficientBound * inputNormSq ^ count +
        Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget count coefficientBound
          inputNormSq)

/-- The perturbation budget is monotone in a nonnegative input quadrance bound.

The common coefficient perturbation bound is also assumed nonnegative. -/
public theorem hornerPerturbationBudget_mono_input : ∀ count
    {coefficientBound small large : Fraction.Rational},
    0 ≤ coefficientBound → 0 ≤ small → small ≤ large →
      Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget count coefficientBound small ≤
        Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget count coefficientBound large
  | 0, _coefficientBound, _small, _large, _coefficientNonnegative,
      _smallNonnegative, _order => le_rfl
  | count + 1, coefficientBound, small, large, coefficientNonnegative,
      smallNonnegative, order => by
      apply Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
        (by decide)
      exact add_le_add
        (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Purelib.Data.Rat.Fraction.Order.Arithmetic.pow_le_pow_direct smallNonnegative order
            count)
          coefficientNonnegative)
        (Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget_mono_input count
          coefficientNonnegative
          smallNonnegative order)

/-- Nonnegative coefficient and input bounds give a nonnegative Horner perturbation budget.

Every retained coefficient bound and input quadrance bound is nonnegative.
The original finite recurrence preserves nonnegativity through each
power, sum and doubled scalar contribution. -/
public theorem hornerPerturbationBudget_nonneg : ∀ count
    {coefficientBound inputNormSq : Fraction.Rational},
    0 ≤ coefficientBound → 0 ≤ inputNormSq →
      0 ≤ Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget count coefficientBound inputNormSq
  | 0, _coefficientBound, _inputNormSq, _coefficientNonnegative,
      _inputNonnegative => le_rfl
  | count + 1, coefficientBound, inputNormSq, coefficientNonnegative,
      inputNonnegative =>
      Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg
          (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
            coefficientNonnegative
            (Purelib.Data.Rat.Fraction.Order.Arithmetic.pow_nonneg_direct inputNonnegative
              count))
          (Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget_nonneg count
            coefficientNonnegative
            inputNonnegative))

/-- A nonempty coefficient list and positive coefficient bound give a positive budget.

Only nonnegativity is required of the input quadrance bound. -/
public theorem hornerPerturbationBudget_pos_of_count_pos : ∀ count
    {coefficientBound inputNormSq : Fraction.Rational},
    0 < count → 0 < coefficientBound → 0 ≤ inputNormSq →
      0 < Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget count coefficientBound inputNormSq := by
  intro count
  induction count with
  | zero =>
      intro _ _ countPositive _ _
      exact (Nat.not_lt_zero 0 countPositive).elim
  | succ count inductionHypothesis =>
      intro coefficientBound inputNormSq _countPositive coefficientPositive inputNonnegative
      have powerNonnegative :=
        Fraction.Order.Arithmetic.pow_nonneg_direct inputNonnegative count
      cases count with
      | zero =>
          have readback :
              2 * (coefficientBound * inputNormSq ^ 0 + 0) =
                (2 : Fraction.Rational) * coefficientBound := by ring1
          change 0 < 2 * (coefficientBound * inputNormSq ^ 0 + 0)
          rewrite [readback]
          exact Fraction.Order.Arithmetic.mul_pos_direct (by decide) coefficientPositive
      | succ remaining =>
          have tailPositive := inductionHypothesis
            (Nat.zero_lt_succ remaining) coefficientPositive inputNonnegative
          exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
            (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
              (Fraction.Order.Arithmetic.mul_nonneg_direct
                coefficientPositive.le powerNonnegative) tailPositive)

/-- The Horner budget is exactly linear in its common coefficientwise
quadrance bound. -/
public theorem hornerPerturbationBudget_scale : ∀ count
    (factor coefficientBound inputNormSq : Fraction.Rational),
    Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget count (factor * coefficientBound) inputNormSq =
      factor *
        Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget count coefficientBound inputNormSq
  | 0, factor, coefficientBound, inputNormSq => by
      change (0 : Fraction.Rational) = factor * 0
      rw [Fraction.Field.mul_zero_direct]
  | count + 1, factor, coefficientBound, inputNormSq => by
      change
        2 * ((factor * coefficientBound) * inputNormSq ^ count +
          Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget count (factor * coefficientBound)
            inputNormSq) =
          factor *
            (2 * (coefficientBound * inputNormSq ^ count +
              Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget count coefficientBound inputNormSq))
      rw [Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget_scale count factor
        coefficientBound
        inputNormSq]
      ring1

set_option backward.match.sparseCases false in
/-- Componentwise coefficient quadrance controls the exact dense Horner
evaluation difference.

The lists retain corresponding entries and the same coefficientwise
squared-distance bound. Their equal finite shapes align the original
Horner powers, and the displayed recurrence bounds that exact evaluation difference. -/
public theorem normSq_evalCoeffs_sub_le : ∀ (left right : List Gaussian.Basic.Canonical)
    (input : Gaussian.Basic.Canonical) (coefficientBound : Fraction.Rational),
    Gaussian.List.Proximity.CoefficientsClose left right coefficientBound →
      Data.Gaussian.Norm.Basic.normSq
          (Dense.Basic.DensePolynomial.evalCoeffs input left -
            Dense.Basic.DensePolynomial.evalCoeffs input right) ≤
        Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget left.length coefficientBound
          (Data.Gaussian.Norm.Basic.normSq input)
  | [], [], input, coefficientBound, _close => by
      change Data.Gaussian.Norm.Basic.normSq ((0 : Gaussian.Basic.Canonical) - 0) ≤ 0
      rewrite [Gaussian.Basic.sub_self, Gaussian.Norm.Basic.normSq_zero]
      exact Fraction.Order.Basic.le_refl 0
  | [], _ :: _, input, coefficientBound, close => by
      exact close.elim
  | _ :: _, [], input, coefficientBound, close => by
      exact close.elim
  | left :: leftTail, right :: rightTail, input, coefficientBound, close => by
      rcases close with ⟨headClose, tailClose⟩
      have tailLength : leftTail.length = rightTail.length := by
        clear headClose
        induction leftTail generalizing rightTail with
        | nil =>
            cases rightTail with
            | nil => exact Eq.refl 0
            | cons rightHead rightRest => exact tailClose.elim
        | cons leftHead leftRest inductionHypothesis =>
            cases rightTail with
            | nil => exact tailClose.elim
            | cons rightHead rightRest =>
                exact congrArg Nat.succ
                  (inductionHypothesis rightRest tailClose.2)
      rw [Dense.Gaussian.Bounds.Perturbation.Value.evalCoeffs_sub_expansion left right leftTail rightTail input
        tailLength]
      calc
        Data.Gaussian.Norm.Basic.normSq
            ((left - right) * input ^ leftTail.length +
              (Dense.Basic.DensePolynomial.evalCoeffs input
                  leftTail -
                Dense.Basic.DensePolynomial.evalCoeffs input
                  rightTail)) ≤
            2 *
              (Data.Gaussian.Norm.Basic.normSq ((left - right) * input ^ leftTail.length) +
                Data.Gaussian.Norm.Basic.normSq
                  (Dense.Basic.DensePolynomial.evalCoeffs input
                      leftTail -
                    Dense.Basic.DensePolynomial.evalCoeffs input
                      rightTail)) :=
          Norm.Bounds.normSq_add_le_two _ _
        _ = 2 *
            (Data.Gaussian.Norm.Basic.normSq (left - right) * Data.Gaussian.Norm.Basic.normSq input ^
              leftTail.length +
              Data.Gaussian.Norm.Basic.normSq
                (Dense.Basic.DensePolynomial.evalCoeffs input
                    leftTail -
                  Dense.Basic.DensePolynomial.evalCoeffs input
                    rightTail)) := by
          rw [Gaussian.Norm.Basic.normSq_mul, Power.normSq_pow]
        _ ≤ 2 *
            (coefficientBound * Data.Gaussian.Norm.Basic.normSq input ^ leftTail.length +
              Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget leftTail.length coefficientBound
                (Data.Gaussian.Norm.Basic.normSq input)) := by
          apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
            (by decide)
          exact add_le_add
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              headClose
              (Fraction.Order.Arithmetic.pow_nonneg_direct
                (Gaussian.Norm.Basic.normSq_nonneg input) leftTail.length))
            (Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Value.normSq_evalCoeffs_sub_le leftTail rightTail
              input coefficientBound
              tailClose)
        _ = Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget (left :: leftTail).length
            coefficientBound (Data.Gaussian.Norm.Basic.normSq input) := rfl

end Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Value
