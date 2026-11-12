module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.Fold
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Replicate
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Algebra.Ring.Defs

/-!
# Positive Gaussian coordinate powers

The retained recursive multiplication program starts at the original coordinate
polynomial. Its coefficient, evaluation, nonzero and degree certificates keep
that original program and the same descending coefficient spines.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Power.Coordinate

open Purelib.Data
open Purelib.Polynomial

/-- Compute the positive coordinate power Z^(n+1) by finite multiplication.

The original zero-index polynomial is Z. Every successor multiplies the
retained previous polynomial by that same original coordinate polynomial. -/
@[expose] public def coordinatePositivePower : Nat → Basic.CanonicalCoefficients.CoefficientPolynomial
  | 0 => Monomial.Coordinate.coordinatePolynomial
  | n + 1 => Coordinate.coordinatePositivePower n *
    Monomial.Coordinate.coordinatePolynomial

section
/-- Folding zero coefficients after Z retains the exact leading-one monomial table.

The original polynomial accumulator is shifted once at every retained zero
coefficient. The leading-one normalization test keeps that entire coefficient spine. -/
private theorem fold_coordinate_zeros (n : Nat) :
    (List.replicate n (0 : Gaussian.Basic.Canonical)).foldl
      (fun value a => Basic.DensePolynomial.shift 1 value +
        Basic.DensePolynomial.scale a Monomial.Coordinate.coordinatePolynomial)
      Monomial.Coordinate.coordinatePolynomial =
        ⟨(1 : Gaussian.Basic.Canonical) :: List.replicate (n + 1) 0⟩ := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rewrite [List.Replicate.replicate_add n 1 (0 : Gaussian.Basic.Canonical),
        List.Fold.foldl_append, inductionHypothesis]
      change (Basic.DensePolynomial.shift 1
        (⟨(1 : Gaussian.Basic.Canonical) :: List.replicate (n + 1) 0⟩ :
          Basic.CanonicalCoefficients.CoefficientPolynomial) +
        Basic.DensePolynomial.scale 0
          Monomial.Coordinate.coordinatePolynomial) = _
      rewrite [Basic.DensePolynomial.scale_zero_left,
        Basic.DensePolynomial.add_zero_normalize,
        Basic.DensePolynomial.normalize_shift]
      rewrite [Basic.DensePolynomial.shift,
        if_neg (show (⟨(1 : Gaussian.Basic.Canonical) :: List.replicate (n + 1) 0⟩ :
          Basic.CanonicalCoefficients.CoefficientPolynomial).isZero ≠ true from by
          change (((1 : Gaussian.Basic.Canonical) :: List.replicate (n + 1) 0).dropWhile
            (fun value => decide (value = 0))).isEmpty ≠ true
          rewrite [List.DropWhile.cons_of_false
            (fun value : Gaussian.Basic.Canonical => decide (value = 0))
            1 (List.replicate (n + 1) 0) (by decide)]
          exact Bool.noConfusion)]
      apply Basic.DensePolynomial.ext
      change (((1 : Gaussian.Basic.Canonical) :: List.replicate (n + 1) 0).dropWhile
        (fun value => decide (value = 0))) ++ List.replicate 1 0 =
        1 :: List.replicate (n + 1 + 1) 0
      rewrite [List.DropWhile.cons_of_false
        (fun value : Gaussian.Basic.Canonical => decide (value = 0))
        1 (List.replicate (n + 1) 0) (by decide)]
      rewrite [List.cons_append]
      exact congrArg (List.cons (1 : Gaussian.Basic.Canonical))
        (List.Replicate.replicate_add (n + 1) 1 0).symm
end

/-- The positive coordinate power has one followed by exactly n+1 zero coefficients.

The original multiplication fold preserves the leading coefficient and appends
one zero at each successor, with no change of coefficient order. -/
public theorem coordinatePositivePower_coeffs (n : Nat) :
    (coordinatePositivePower n).coeffs =
      (1 : Gaussian.Basic.Canonical) :: List.replicate (n + 1) 0 := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [coordinatePositivePower]
      rw [show coordinatePositivePower n =
          ⟨(1 : Gaussian.Basic.Canonical) :: List.replicate (n + 1) 0⟩ by
        apply Basic.DensePolynomial.ext
        exact inductionHypothesis]
      change (List.foldl
        (fun value a => Basic.DensePolynomial.shift 1 value + Basic.DensePolynomial.scale a
          Monomial.Coordinate.coordinatePolynomial)
        0 ((1 : Gaussian.Basic.Canonical) :: List.replicate (n + 1) 0)).coeffs = _
      simp only [List.foldl_cons, Basic.DensePolynomial.shift_zero, Basic.DensePolynomial.scale_one_left,
        Basic.DensePolynomial.zero_add_normalize]
      exact congrArg (fun polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial => polynomial.coeffs)
        (fold_coordinate_zeros (n + 1))

/-- The positive coordinate-power program evaluates to the input raised to n+1.

Each original multiplication step evaluates to multiplication by the same input
point; scalar power recursion therefore follows the original program. -/
public theorem coordinatePositivePower_eval (n : Nat) (z : Gaussian.Basic.Canonical) :
    (coordinatePositivePower n).eval z = z ^ (n + 1) := by
  induction n with
  | zero =>
      change Monomial.Coordinate.coordinatePolynomial.eval z = z ^ 1
      exact (Monomial.Coordinate.coordinatePolynomial_eval z).trans
        (pow_one z).symm
  | succ n inductionHypothesis =>
      rewrite [coordinatePositivePower, Basic.DensePolynomial.eval_mul,
        inductionHypothesis, Monomial.Coordinate.coordinatePolynomial_eval]
      exact (pow_succ z (n + 1)).symm

/-- Every positive coordinate power is a nonzero Gaussian polynomial.

The original coordinate factor is nonzero, and the finite multiplication
nonzero certificate retains that fact through each recursive power. -/
public theorem coordinatePositivePower_isZero_false (n : Nat) :
    (coordinatePositivePower n).isZero = false := by
  induction n with
  | zero => exact Monomial.Coordinate.coordinatePolynomial_isZero_false
  | succ n inductionHypothesis =>
      rw [coordinatePositivePower]
      exact Basic.DensePolynomial.isZero_mul_eq_false inductionHypothesis
        Monomial.Coordinate.coordinatePolynomial_isZero_false

/-- The positive coordinate power indexed by n has degree n+1.

Each original nonzero coordinate multiplication adds its retained degree one
to the degree of the preceding original polynomial. -/
public theorem coordinatePositivePower_natDegree (n : Nat) :
    (coordinatePositivePower n).natDegree = n + 1 := by
  induction n with
  | zero => exact Monomial.Coordinate.coordinatePolynomial_natDegree
  | succ n inductionHypothesis =>
      rewrite [coordinatePositivePower,
        Basic.DensePolynomial.natDegree_mul (coordinatePositivePower_isZero_false
          n)
          Monomial.Coordinate.coordinatePolynomial_isZero_false,
        inductionHypothesis, Monomial.Coordinate.coordinatePolynomial_natDegree]
      exact Eq.refl _

end Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
