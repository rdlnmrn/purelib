module

import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Gaussian.List.Proximity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Derivative
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Derivative
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Value
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
public import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Bounds.Horner
import Purelib.Polynomial.Dense.Evaluation

/-!
# Refinement bounds for retained coherent coefficient tables

The finite monic coefficient count and retained box quadrance determine
evaluation and derivative refinement budgets and their target-independent
scales. Ordered channel and allowance certificates compare the same readings.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-- Uniform derivative-evaluation budget between two sufficiently accurate
readings of the same coefficient channels.

The finite perturbation recurrence uses the monic coefficient count, eight
times the supplied allowance target and the retained box quadrance bound.
Its slope component bounds derivative evaluation differences. -/
@[expose] public def refinementDerivativeBound (table : CoefficientTable)
    (target : Fraction.Rational) (box : Box) : Fraction.Rational :=
  (Dense.Gaussian.Bounds.Perturbation.Derivative.coefficientPerturbationBounds (table.degree + 1) (8 * target)
    box.normSqBound).slope

/-- The coefficientwise automatic-Horner estimate, specialized to the
derivatives of two monic readings.

Both retained coefficient readings have the same ordered channels and
allowances strictly below the positive target. Their derivative evaluations
are compared at the same input inside the displayed box. -/
public theorem derivative_eval_sub_le_of_sameChannels
    (left right : CoefficientTable) (target : Fraction.Rational)
    (positive : 0 < target)
    (same : CoefficientTable.SameChannels left.entries right.entries)
    (leftSmall : CoefficientTable.AllowancesLt left.entries target)
    (rightSmall : CoefficientTable.AllowancesLt right.entries target)
    (box : Box) {input : Gaussian.Basic.Canonical} (inside : box.Contains input) :
    Data.Gaussian.Norm.Basic.normSq
        ((Dense.Gaussian.GCD.derivative left.polynomial).eval input -
          (Dense.Gaussian.GCD.derivative right.polynomial).eval input) ≤
      left.refinementDerivativeBound target box := by
  have close := CoefficientTable.values_close_of_sameChannels same leftSmall rightSmall
  have coefficientNonnegative : 0 ≤ 8 * target :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) positive.le
  have monicClose := Gaussian.List.Proximity.monicCoefficientsClose coefficientNonnegative close
  have bounds := Dense.Gaussian.Bounds.Perturbation.Derivative.normSq_evalDerivative_sub_le
    (1 :: left.values) (1 :: right.values) input (8 * target)
      box.normSqBound monicClose (box.normSq_le_normSqBound inside)
      coefficientNonnegative box.normSqBound_nonneg
  simp only [Dense.Gaussian.GCD.derivative]
  rw [Dense.Derivative.eval_derivative,
    Dense.Derivative.eval_derivative]
  change Data.Gaussian.Norm.Basic.normSq
      ((Dense.Derivative.evalDerivativeCoeffs input
        (1 :: left.values)).2 -
       (Dense.Derivative.evalDerivativeCoeffs input
        (1 :: right.values)).2) ≤ _
  simpa only [CoefficientTable.refinementDerivativeBound, List.length_cons,
    left.values_length] using bounds.2

/-- Coefficient multiplying a common allowance target in the automatic
derivative perturbation estimate.

The finite perturbation recurrence retains the monic coefficient count and
box quadrance bound, with coefficient error eight. Its slope component
is the scale for the corresponding derivative refinement budget. -/
@[expose] public def refinementDerivativeScale (table : CoefficientTable)
    (box : Box) : Fraction.Rational :=
  (Dense.Gaussian.Bounds.Perturbation.Derivative.coefficientPerturbationBounds (table.degree + 1) 8
    box.normSqBound).slope

/-- The derivative refinement budget equals the allowance target times its box-dependent scale.

The supplied target multiplies the fixed coefficient error eight.
Homogeneity of the same finite perturbation recurrence identifies its slope
with that target times the retained derivative scale. -/
public theorem refinementDerivativeBound_eq_target_mul_scale
    (table : CoefficientTable) (target : Fraction.Rational) (box : Box) :
    table.refinementDerivativeBound target box =
      target * table.refinementDerivativeScale box := by
  rw [CoefficientTable.refinementDerivativeBound, CoefficientTable.refinementDerivativeScale]
  have coefficientOrder : (8 : Fraction.Rational) * target = target * 8 := by ring1
  rw [coefficientOrder,
    Dense.Gaussian.Bounds.Perturbation.Derivative.coefficientPerturbationBounds_scale (table.degree + 1) target 8
      box.normSqBound]

/-- The derivative refinement scale computed for a coefficient table and box is nonnegative.

The recurrence starts from nonnegative coefficient error eight and the
nonnegative retained box quadrance bound. Its slope component preserves
those nonnegative inputs. -/
public theorem refinementDerivativeScale_nonneg (table : CoefficientTable)
    (box : Box) : 0 ≤ table.refinementDerivativeScale box :=
  (Dense.Gaussian.Bounds.Perturbation.Derivative.coefficientPerturbationBounds_nonneg (table.degree + 1)
    (by decide) box.normSqBound_nonneg).2

/-- Uniform box-evaluation budget for one simultaneous coefficient-table
refinement.

The finite Horner budget uses the monic coefficient count, eight times the
supplied allowance target and the same retained box quadrance bound. -/
@[expose] public def refinementEvaluationBound (table : CoefficientTable)
    (target : Fraction.Rational) (box : Box) : Fraction.Rational :=
  Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget (table.degree + 1) (8 * target)
    box.normSqBound

/-- Two readings of the same coefficient channels have identical evaluation budgets for the same target and box.

The ordered channel certificate identifies the two coefficient counts.
The same target and box therefore give the same finite Horner budget. -/
public theorem refinementEvaluationBound_eq_of_sameChannels
    (left right : CoefficientTable)
    (same : CoefficientTable.SameChannels left.entries right.entries)
    (target : Fraction.Rational) (box : Box) :
    left.refinementEvaluationBound target box =
      right.refinementEvaluationBound target box := by
  unfold CoefficientTable.refinementEvaluationBound
  rw [CoefficientTable.degree_eq_of_sameChannels same]

/-- A positive allowance target gives a nonnegative evaluation refinement budget.

The positive target gives a nonnegative coefficient error eight times
that target. The retained box quadrance is nonnegative, so the finite
Horner recurrence preserves a nonnegative budget. -/
public theorem refinementEvaluationBound_nonneg (table : CoefficientTable)
    {target : Fraction.Rational} (positive : 0 < target) (box : Box) :
    0 ≤ table.refinementEvaluationBound target box :=
  Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget_nonneg (table.degree + 1)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) positive.le)
    box.normSqBound_nonneg

/-- Positive coefficient multiplying the requested allowance target in the
uniform Horner perturbation budget on one box.

The finite Horner recurrence retains the monic coefficient count and box
quadrance bound while fixing coefficient error at eight. Its result is the
scale of the evaluation refinement budget. -/
@[expose] public def refinementEvaluationScale (table : CoefficientTable)
    (box : Box) : Fraction.Rational :=
  Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget (table.degree + 1) 8 box.normSqBound

/-- The evaluation refinement budget equals the allowance target times its box-dependent scale.

Homogeneity of the same finite Horner recurrence separates the supplied
allowance target from its fixed coefficient error eight and retained box
quadrance bound. -/
public theorem refinementEvaluationBound_eq_target_mul_scale
    (table : CoefficientTable) (target : Fraction.Rational) (box : Box) :
    table.refinementEvaluationBound target box =
      target * table.refinementEvaluationScale box := by
  rw [CoefficientTable.refinementEvaluationBound, CoefficientTable.refinementEvaluationScale]
  have coefficientOrder : (8 : Fraction.Rational) * target = target * 8 := by ring1
  rw [coefficientOrder,
    Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget_scale (table.degree + 1) target 8
      box.normSqBound]

/-- The evaluation refinement scale depends only on the retained coefficient channels and box.

The ordered channel certificate retains the same coefficient count in
both readings. Applying the same finite Horner recurrence to that count
and box gives an equal scale. -/
public theorem refinementEvaluationScale_eq_of_sameChannels
    (left right : CoefficientTable)
    (same : CoefficientTable.SameChannels left.entries right.entries) (box : Box) :
    left.refinementEvaluationScale box =
      right.refinementEvaluationScale box := by
  unfold CoefficientTable.refinementEvaluationScale
  rw [CoefficientTable.degree_eq_of_sameChannels same]

/-- The evaluation refinement scale is positive because the monic coefficient table has positive length.

The monic coefficient count is a natural successor. Its strictly positive
count, positive coefficient error eight and nonnegative box quadrance
give a positive finite Horner budget. -/
public theorem refinementEvaluationScale_pos (table : CoefficientTable)
    (box : Box) : 0 < table.refinementEvaluationScale box :=
  Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget_pos_of_count_pos (table.degree + 1)
    (Nat.zero_lt_succ table.degree) (by decide) box.normSqBound_nonneg

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable
