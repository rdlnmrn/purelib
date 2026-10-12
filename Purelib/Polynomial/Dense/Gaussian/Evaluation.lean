module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Tactic.Ring

/-!
# Gaussian Horner evaluation

The original dense polynomial and coefficient list retain their descending
order. Appending a coefficient performs exactly one further Horner step,
with the original fold accumulator and Gaussian arithmetic.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation

open Purelib.Data
open Purelib.Polynomial

/-- High-to-low Horner evaluation of a finite coefficient list.

This specialization retains the generic dense evaluator and its original
coefficient order, with canonical Gaussian coordinates as the scalar carrier. -/
@[expose] public def evalCoeffs (point : Gaussian.Basic.Canonical)
    (coefficients : List Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  Dense.Basic.DensePolynomial.evalCoeffs point coefficients

/-- High-to-low Horner evaluation of a dense Gaussian polynomial.

The original polynomial supplies its stored coefficient list directly to
its evaluator; this wrapper does not normalize or construct another list. -/
@[expose] public def eval (polynomial : Basic.GaussianCanonical.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  polynomial.eval point

/-- Removing leading zero coefficients does not change Gaussian evaluation.

Normalization and evaluation use the same original polynomial coefficients,
and the generic normalization certificate supplies the displayed equality. -/
public theorem eval_normalize (polynomial : Basic.GaussianCanonical.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) :
    eval (Dense.Gaussian.Basic.normalize polynomial) point = eval polynomial point :=
  Dense.Basic.DensePolynomial.eval_normalize polynomial point

/-- Appending one coefficient performs one Horner step after the original fold.

Structural recursion carries the original accumulator through each coefficient.
The tail fold is retained unchanged, including its original coefficient order. -/
private theorem foldl_append_singleton
    (point : Gaussian.Basic.Canonical) (coefficients : List Gaussian.Basic.Canonical)
    (accumulator coefficient : Gaussian.Basic.Canonical) :
    (coefficients ++ [coefficient]).foldl
        (fun value next => value * point + next) accumulator =
      coefficients.foldl (fun value next => value * point + next)
          accumulator * point + coefficient := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change (tail ++ [coefficient]).foldl
        (fun value next => value * point + next) (accumulator * point + head) =
        tail.foldl (fun value next => value * point + next)
          (accumulator * point + head) * point + coefficient
      exact inductionHypothesis (accumulator * point + head)

/-- Appending a trailing zero multiplies Gaussian coefficient evaluation by the point.

The original coefficient fold ends with one further Horner step whose added
coefficient is zero; the direct Gaussian zero-addition law removes that term. -/
public theorem evalCoeffs_append_zero
    (point : Gaussian.Basic.Canonical) (coefficients : List Gaussian.Basic.Canonical) :
    evalCoeffs point (coefficients ++ [0]) = evalCoeffs point coefficients * point :=
  (foldl_append_singleton point coefficients 0 0).trans
    (Gaussian.Basic.add_zero _)

/-- Appending one Gaussian coefficient multiplies the previous value by the point and adds that coefficient.

This is the original dense evaluator with accumulator zero. The final Horner
step follows the exact original fold rather than a function-extensionality
certificate for appending arbitrary lists. -/
public theorem evalCoeffs_append_singleton
    (point : Gaussian.Basic.Canonical) (coefficients : List Gaussian.Basic.Canonical)
    (trailing : Gaussian.Basic.Canonical) :
    Dense.Basic.DensePolynomial.evalCoeffs point (coefficients ++ [trailing]) =
      Dense.Basic.DensePolynomial.evalCoeffs point coefficients * point + trailing :=
  foldl_append_singleton point coefficients 0 trailing

/-- The Gaussian coordinate polynomial evaluates to the input point.

The stored coefficients are one and zero, so the two original Horner steps
reduce to multiplication by one followed by addition of zero. -/
@[simp] public theorem coordinatePolynomial_eval (point : Gaussian.Basic.Canonical) :
    Dense.Gaussian.Basic.coordinatePolynomial.eval point = point := by
  unfold Dense.Gaussian.Basic.coordinatePolynomial Dense.Basic.DensePolynomial.eval
    Dense.Basic.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The Gaussian constant-one polynomial evaluates to one.

The original single coefficient is one. Starting the Horner accumulator at
zero therefore leaves the constant coefficient independently of the point. -/
@[simp] public theorem constantOnePolynomial_eval (point : Gaussian.Basic.Canonical) :
    Dense.Gaussian.Basic.constantOnePolynomial.eval point = 1 := by
  unfold Dense.Gaussian.Basic.constantOnePolynomial Dense.Basic.DensePolynomial.eval
    Dense.Basic.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

end Purelib.Polynomial.Dense.Gaussian.Evaluation
