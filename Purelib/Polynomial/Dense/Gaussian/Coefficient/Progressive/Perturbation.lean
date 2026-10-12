module

import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Bounds
import Purelib.Data.Gaussian.List.Proximity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Perturbation
import Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Value
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Dense.Gaussian.Extensionality
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic

/-!
# Exact perturbations between retained coefficient readings

Exact polynomial differences retain the original monic coefficient readings.
Their ordered channel certificates and rational allowances give uniform
evaluation budgets throughout the same supplied box.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Geometry.Rational

open Purelib.Data.Gaussian

/-- Exact finite difference polynomial for one simultaneous refinement.

The difference retains the original table and its same-request refined
polynomial. Both polynomial readings use their original coefficient lists. -/
@[expose] public def refinementPerturbation (table : CoefficientTable)
    (target : Fraction.Rational) (positive : 0 < target) : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  (table.refine target positive).polynomial - table.polynomial

/-- Adding the refinement perturbation recovers the refined monic polynomial.

Normalization of the refined coefficient list gives exact polynomial equality. -/
public theorem polynomial_add_refinementPerturbation
    (table : CoefficientTable) (target : Fraction.Rational)
    (positive : 0 < target) :
    table.polynomial + table.refinementPerturbation target positive =
      (table.refine target positive).polynomial := by
  exact Dense.Gaussian.Extensionality.add_sub_left_eq_of_normalized table.polynomial
    (table.refine target positive).polynomial
    (table.refine target positive).polynomial_normalized

/-- Uniform Horner bound between any two accurate readings of the same
channel table.

The two ordered channel lists have allowances below the same positive
target. Their original coefficient proximity bounds the evaluation
difference uniformly throughout the supplied rational box. -/
public theorem polynomial_eval_sub_le_of_sameChannels
    (left right : CoefficientTable) (target : Fraction.Rational)
    (positive : 0 < target)
    (same : CoefficientTable.SameChannels left.entries right.entries)
    (leftSmall : CoefficientTable.AllowancesLt left.entries target)
    (rightSmall : CoefficientTable.AllowancesLt right.entries target)
    (box : Box) {input : Gaussian.Basic.Canonical} (inside : box.Contains input) :
    Data.Gaussian.Norm.Basic.normSq (left.polynomial.eval input - right.polynomial.eval input) ≤
      left.refinementEvaluationBound target box := by
  have close := CoefficientTable.values_close_of_sameChannels same leftSmall rightSmall
  have coefficientNonnegative : 0 ≤ 8 * target :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) positive.le
  have monicClose := Gaussian.List.Proximity.monicCoefficientsClose coefficientNonnegative close
  change Data.Gaussian.Norm.Basic.normSq
      (Dense.Basic.DensePolynomial.evalCoeffs input
          (1 :: left.values) -
        Dense.Basic.DensePolynomial.evalCoeffs input
          (1 :: right.values)) ≤
    Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget (left.degree + 1) (8 * target)
      box.normSqBound
  simpa only [List.length_cons, left.values_length] using
    Dense.Gaussian.Bounds.Box.Perturbation.normSq_evalCoeffs_sub_le_onBox
      (1 :: left.values) (1 :: right.values) (8 * target)
      coefficientNonnegative box inside monicClose

/-- The exact monic polynomial assembled after a simultaneous coefficient
refinement differs from the preceding monic reading by no more than the
computed uniform Horner budget anywhere in the displayed box.

The current allowances are below the supplied positive target. The original
common-request refinement then bounds the two monic readings uniformly
throughout the displayed box by their retained Horner budget. -/
public theorem polynomial_eval_sub_refine_le_onBox
    (table : CoefficientTable) (target : Fraction.Rational)
    (positive : 0 < target)
    (currentSmall : CoefficientTable.AllowancesLt table.entries target)
    (box : Box) {input : Gaussian.Basic.Canonical} (inside : box.Contains input) :
    Data.Gaussian.Norm.Basic.normSq
        (table.polynomial.eval input -
          (table.refine target positive).polynomial.eval input) ≤
      table.refinementEvaluationBound target box := by
  have close := table.values_close_refine target positive currentSmall
  have coefficientNonnegative : 0 ≤ 8 * target :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) positive.le
  have monicClose := Gaussian.List.Proximity.monicCoefficientsClose coefficientNonnegative close
  change Data.Gaussian.Norm.Basic.normSq
      (Dense.Basic.DensePolynomial.evalCoeffs input
          (1 :: table.values) -
        Dense.Basic.DensePolynomial.evalCoeffs input
          (1 :: (table.refine target positive).values)) ≤
    Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget (table.degree + 1) (8 * target)
      box.normSqBound
  simpa only [List.length_cons, table.values_length] using
    Dense.Gaussian.Bounds.Box.Perturbation.normSq_evalCoeffs_sub_le_onBox
      (1 :: table.values) (1 :: (table.refine target positive).values)
      (8 * target) coefficientNonnegative box inside monicClose

/-- Exact difference polynomial between two finite readings of the same
progressive coefficient channels.

The difference is exactly the second monic reading minus the first. Both
readings retain their original coefficient lists and displayed polynomial
constructions. -/
@[expose] public def readingPerturbation (left right : CoefficientTable) : (Dense.Basic.DensePolynomial
  Gaussian.Basic.Canonical) :=
  right.polynomial - left.polynomial

/-- Adding a reading perturbation recovers the second monic reading.

The equality uses the original normalized coefficient lists without changing their channels. -/
public theorem polynomial_add_readingPerturbation
    (left right : CoefficientTable) :
    left.polynomial + CoefficientTable.readingPerturbation left right = right.polynomial :=
  Dense.Gaussian.Extensionality.add_sub_left_eq_of_normalized left.polynomial right.polynomial
    right.polynomial_normalized

/-- Bound the evaluation of a perturbation between two readings of the same channels.

Both readings must meet the same positive allowance target; the bound is uniform throughout the supplied box. -/
public theorem readingPerturbation_eval_le_onBox
    (left right : CoefficientTable) (target : Fraction.Rational)
    (positive : 0 < target)
    (same : CoefficientTable.SameChannels left.entries right.entries)
    (leftSmall : CoefficientTable.AllowancesLt left.entries target)
    (rightSmall : CoefficientTable.AllowancesLt right.entries target)
    (box : Box) {input : Gaussian.Basic.Canonical} (inside : box.Contains input) :
    Data.Gaussian.Norm.Basic.normSq ((CoefficientTable.readingPerturbation left right).eval input) ≤
      left.refinementEvaluationBound target box := by
  rw [CoefficientTable.readingPerturbation,
    Dense.Basic.DensePolynomial.eval_sub]
  have reversed :
      right.polynomial.eval input - left.polynomial.eval input =
        -(left.polynomial.eval input - right.polynomial.eval input) := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im] <;> ring1
  rw [reversed, Gaussian.Norm.Basic.normSq_neg]
  exact CoefficientTable.polynomial_eval_sub_le_of_sameChannels left right target positive
    same leftSmall rightSmall box inside

/-- Bound the polynomial change caused by simultaneous coefficient refinement.

If the current allowances meet the positive target, the refinement evaluation budget bounds the squared norm of the
perturbation throughout the box. -/
public theorem refinementPerturbation_eval_le_onBox
    (table : CoefficientTable) (target : Fraction.Rational)
    (positive : 0 < target)
    (currentSmall : CoefficientTable.AllowancesLt table.entries target)
    (box : Box) {input : Gaussian.Basic.Canonical} (inside : box.Contains input) :
    Data.Gaussian.Norm.Basic.normSq ((table.refinementPerturbation target positive).eval input) ≤
      table.refinementEvaluationBound target box := by
  rw [CoefficientTable.refinementPerturbation,
    Dense.Basic.DensePolynomial.eval_sub]
  have reversed :
      (table.refine target positive).polynomial.eval input -
          table.polynomial.eval input =
        -(table.polynomial.eval input -
          (table.refine target positive).polynomial.eval input) := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im] <;> ring1
  rw [reversed, Gaussian.Norm.Basic.normSq_neg]
  exact table.polynomial_eval_sub_refine_le_onBox target positive currentSmall
    box inside

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable
