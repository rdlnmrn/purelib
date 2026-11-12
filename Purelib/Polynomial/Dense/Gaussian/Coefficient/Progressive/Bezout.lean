module

import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Perturbation
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Bezout
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic

open Purelib.Data.Rat.Fraction.Order

/-!
# Bézout bounds for retained coefficient readings

The original reference Bézout factors retain their exact identity and
box majorants. Shared coefficient readings transport that identity with
explicit evaluation and derivative budgets and a positive rational target.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Geometry.Rational

open Purelib.Data.Gaussian

/-- Linear coefficient-allowance scale for the error in transporting one
reference Bézout identity to another reading.

The original reference Bézout factors retain their evaluation majorants
on the supplied box. These multiply the same evaluation and derivative
refinement scales before their original doubled sum is formed. -/
@[expose] public def bezoutPerturbationScale
    (table : CoefficientTable)
    (squarefree : Squarefree.Basic.SquarefreeCertificate table.polynomial)
    (box : Box) : Fraction.Rational :=
  2 *
    (Bounds.Box.denseEvalNormMajorant squarefree.left box *
        table.refinementEvaluationScale box +
      Bounds.Box.denseEvalNormMajorant squarefree.right box *
        table.refinementDerivativeScale box)

/-- The exact reference Bézout identity remains an approximate identity for
every sufficiently accurate reading of the same channels.

Both original ordered channel tables meet the same positive allowance
target. The reference factors and their exact Bézout identity bound the
second reading residual throughout the supplied box. -/
public theorem approximateBezout_error_le
    (left right : CoefficientTable)
    (squarefree : Squarefree.Basic.SquarefreeCertificate left.polynomial)
    (box : Box) (target : Fraction.Rational) (positive : 0 < target)
    (same : SameChannels left.entries right.entries)
    (leftSmall : AllowancesLt left.entries target)
    (rightSmall : AllowancesLt right.entries target)
    {point : Basic.Canonical} (inside : box.Contains point) :
    Norm.Basic.normSq
        (1 - (squarefree.left.eval point * right.polynomial.eval point +
          squarefree.right.eval point *
            (GCD.derivative right.polynomial).eval point)) ≤
      target * left.bezoutPerturbationScale squarefree box := by
  let leftValue := squarefree.left.eval point
  let rightValue := squarefree.right.eval point
  let valueDifference :=
    left.polynomial.eval point - right.polynomial.eval point
  let derivativeDifference :=
    (GCD.derivative left.polynomial).eval point -
      (GCD.derivative right.polynomial).eval point
  have identity :
      1 - (leftValue * right.polynomial.eval point + rightValue *
          (GCD.derivative right.polynomial).eval point) =
        leftValue * valueDifference + rightValue * derivativeDifference := by
    have reference := squarefree.identity point
    dsimp only [leftValue, rightValue, valueDifference, derivativeDifference]
    rw [reference]
    apply Basic.ext <;>
      simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im,
        Basic.mul_re, Basic.mul_im] <;> ring1
  have leftMajorant :=
    Bounds.Box.normSq_eval_le_denseEvalNormMajorant
      squarefree.left inside
  have rightMajorant :=
    Bounds.Box.normSq_eval_le_denseEvalNormMajorant
      squarefree.right inside
  have valueBound := left.polynomial_eval_sub_le_of_sameChannels right target
    positive same leftSmall rightSmall box inside
  have derivativeBound := left.derivative_eval_sub_le_of_sameChannels right
    target positive same leftSmall rightSmall box inside
  have valueProduct : Norm.Basic.normSq leftValue * Norm.Basic.normSq
    valueDifference ≤
      Bounds.Box.denseEvalNormMajorant squarefree.left box *
        left.refinementEvaluationBound target box :=
    Arithmetic.mul_le_mul_direct leftMajorant valueBound
      (Norm.Basic.normSq_nonneg valueDifference)
      (Bounds.Box.denseEvalNormMajorant_pos
        squarefree.left box).le
  have derivativeProduct :
      Norm.Basic.normSq rightValue * Norm.Basic.normSq derivativeDifference ≤
        Bounds.Box.denseEvalNormMajorant squarefree.right box *
          left.refinementDerivativeBound target box :=
    Arithmetic.mul_le_mul_direct rightMajorant derivativeBound
      (Norm.Basic.normSq_nonneg derivativeDifference)
      (Bounds.Box.denseEvalNormMajorant_pos
        squarefree.right box).le
  rw [identity]
  calc
    Norm.Basic.normSq (leftValue * valueDifference + rightValue * derivativeDifference) ≤
        2 * (Norm.Basic.normSq (leftValue * valueDifference) +
          Norm.Basic.normSq (rightValue * derivativeDifference)) :=
      Norm.Bounds.normSq_add_le_two _ _
    _ = 2 * (Norm.Basic.normSq leftValue * Norm.Basic.normSq valueDifference +
          Norm.Basic.normSq rightValue * Norm.Basic.normSq derivativeDifference) :=
            by
      rw [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
    _ ≤ 2 *
        (Bounds.Box.denseEvalNormMajorant squarefree.left box *
            left.refinementEvaluationBound target box +
          Bounds.Box.denseEvalNormMajorant squarefree.right box *
            left.refinementDerivativeBound target box) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct valueProduct derivativeProduct) (by decide)
    _ = target * left.bezoutPerturbationScale squarefree box := by
      rw [left.refinementEvaluationBound_eq_target_mul_scale,
        left.refinementDerivativeBound_eq_target_mul_scale]
      unfold bezoutPerturbationScale
      ring1

/-- The combined evaluation and derivative perturbation scale is strictly positive.

The reference evaluation majorants are positive, the evaluation scale is
positive and the derivative scale is nonnegative. Their original doubled
sum is therefore strictly positive. -/
public theorem bezoutPerturbationScale_pos
    (table : CoefficientTable)
    (squarefree : Squarefree.Basic.SquarefreeCertificate table.polynomial)
    (box : Box) : 0 < table.bezoutPerturbationScale squarefree box := by
  have leftProductPositive : 0 <
      Bounds.Box.denseEvalNormMajorant squarefree.left box *
        table.refinementEvaluationScale box :=
    Arithmetic.mul_pos_direct
      (Bounds.Box.denseEvalNormMajorant_pos squarefree.left box)
      (table.refinementEvaluationScale_pos box)
  have rightProductNonnegative : 0 ≤
      Bounds.Box.denseEvalNormMajorant squarefree.right box *
        table.refinementDerivativeScale box :=
    Arithmetic.mul_nonneg_direct
      (Bounds.Box.denseEvalNormMajorant_pos
        squarefree.right box).le
      (table.refinementDerivativeScale_nonneg box)
  exact Arithmetic.mul_pos_direct (by decide)
    (Arithmetic.add_pos_of_pos_of_nonneg_direct leftProductPositive rightProductNonnegative)

/-- A reference-computed target making the complete approximate-Bézout
error at most `1/16`, without any square-root choice.

The target divides one by sixteen times the original positive Bézout
perturbation scale. It retains the same reference factors and rational box. -/
@[expose] public def bezoutStabilityTarget
    (table : CoefficientTable)
    (squarefree : Squarefree.Basic.SquarefreeCertificate table.polynomial)
    (box : Box) : Fraction.Rational :=
  1 / (16 * table.bezoutPerturbationScale squarefree box)

/-- The stability target times its retained perturbation scale is at most one sixteenth.

The retained positive perturbation scale cancels its occurrence in the
original rational target. The resulting product is bounded by the exact
one-sixteenth threshold. -/
public theorem bezoutStabilityTarget_mul_scale_le
    (table : CoefficientTable)
    (squarefree : Squarefree.Basic.SquarefreeCertificate table.polynomial)
    (box : Box) :
    table.bezoutStabilityTarget squarefree box *
        table.bezoutPerturbationScale squarefree box ≤
      (1 / 16 : Fraction.Rational) := by
  let scale := table.bezoutPerturbationScale squarefree box
  have scalePositive : 0 < scale :=
    table.bezoutPerturbationScale_pos squarefree box
  apply (Field.le_div_iff_pos
    (show (0 : Fraction.Rational) < 16 by decide)).mpr
  calc
    (table.bezoutStabilityTarget squarefree box * scale) * 16 =
        table.bezoutStabilityTarget squarefree box * (16 * scale) := by ring1
    _ = 1 := Fraction.Field.div_mul_cancel_of_ne 1
      (16 * scale)
      (ne_of_gt (Arithmetic.mul_pos_direct
        (by decide) scalePositive))
    _ ≤ 1 := Basic.le_refl _

/-- The coefficient table's Bézout stability target is strictly positive.

The original reference factors and box give a strictly positive scale.
The reciprocal target retains that scale and is strictly positive. -/
public theorem bezoutStabilityTarget_pos
    (table : CoefficientTable)
    (squarefree : Squarefree.Basic.SquarefreeCertificate table.polynomial)
    (box : Box) : 0 < table.bezoutStabilityTarget squarefree box :=
  Field.div_pos_direct (by decide)
    (Arithmetic.mul_pos_direct (by decide)
      (table.bezoutPerturbationScale_pos squarefree box))

/-- Construct robust derivative separation for an admitted reading from one
fixed exact reference Bézout certificate.

The two readings have the same ordered channels and meet the reference
Bézout target. The original approximate-identity builder retains both
reference factors, the second polynomial and the same rational box. -/
@[expose] public def robustDerivativeSeparation
    (left right : CoefficientTable)
    (squarefree : Squarefree.Basic.SquarefreeCertificate left.polynomial)
    (box : Box)
    (same : SameChannels left.entries right.entries)
    (leftSmall : AllowancesLt left.entries
      (left.bezoutStabilityTarget squarefree box))
    (rightSmall : AllowancesLt right.entries
      (left.bezoutStabilityTarget squarefree box)) :
    Derivative.Separation.Basic.Certificate right.polynomial box :=
  Derivative.Separation.Bezout.ofApproximateBezout right.polynomial
    squarefree.left squarefree.right box (by
      intro point inside
      exact (left.approximateBezout_error_le right squarefree box
        (left.bezoutStabilityTarget squarefree box)
        (left.bezoutStabilityTarget_pos squarefree box) same leftSmall
        rightSmall inside).trans
          (left.bezoutStabilityTarget_mul_scale_le squarefree box))

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable
