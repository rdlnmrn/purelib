module
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Comparison
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Antiderivative
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Bounds
import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate (DensePrimitive)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

public section

/-!
# Primitive Taylor control from a coefficient derivative bound

Two finite segment estimates turn any checked derivative ceiling into a
quadratic remainder bound. The intermediate Horner remainder is used only
in the erased proof, not as the requested executable ceiling.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate.DensePrimitive

/-- A coefficient derivative ceiling controls the primitive remainder on
the whole box. It need not come from the coefficient-list Horner ceiling.

A uniform derivative ceiling on the box bounds the same primitive increment relative to its retained linear term. -/
theorem increment_bound_of_derivative {coefficient : Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (primitive : DensePrimitive coefficient box) {start finish :
      Gaussian.Basic.Canonical}
    (startInside : box.Contains start) (finishInside : box.Contains finish)
    (bound : Fraction.Rational) (nonnegative : 0 ≤ bound)
    (bounded : ∀ point, box.Contains point → Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative
      coefficient).eval point) ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (primitive.value.eval finish - primitive.value.eval start - coefficient.eval
      start * (finish - start)) ≤
      4 * bound * Data.Gaussian.Norm.Basic.normSq (finish - start) ^ 2 := open Purelib in by
  let linear : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) := ⟨[coefficient.eval start, 0]⟩
  have linearDerivative (point : Gaussian.Basic.Canonical) :
      (Dense.Gaussian.GCD.derivative linear).eval point =
        (DensePolynomial.constant (coefficient.eval start)).eval point := by
    rw [Dense.Gaussian.GCD.derivative, Dense.Derivative.eval_derivative,
      DensePolynomial.eval_constant]
    simp only [linear, Dense.Derivative.evalDerivativeCoeffs, List.foldl_cons, List.foldl_nil,
      Dense.Derivative.evalDerivativeStep, Gaussian.Basic.zero_mul, _root_.zero_add, _root_.add_zero,
      -eq_self, -iff_self]
    rfl
  let comparison : DensePrimitive (DensePolynomial.constant
    (coefficient.eval start)) box :=
    { value := linear
      derivative_eq := linearDerivative
      remainderBound := Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound linear box
      remainderBound_nonnegative := (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos _ _).le
      increment_bound := by
        intro first last firstInside lastInside
        have bound := Dense.Gaussian.Bounds.Box.Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound linear
          lastInside firstInside
        rw [linearDerivative] at bound
        exact bound }
  have gap (parameter : Fraction.Rational) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
      Data.Gaussian.Norm.Basic.normSq (coefficient.eval (Affine.line start (finish - start) parameter) -
        1 * (DensePolynomial.constant (coefficient.eval start)).eval
          (Affine.line start (finish - start) parameter)) ≤
      2 * bound * Data.Gaussian.Norm.Basic.normSq (finish - start) := by
    rw [_root_.one_mul, DensePolynomial.eval_constant]
    have estimate := Dense.Gaussian.Derivative.Bounds.eval_sub_eval_le_of_derivative_bound coefficient startInside
      (Box.contains_line startInside finishInside inside) bound bounded
    have distance := Affine.normSq_line_sub start (finish - start) parameter 0
    have parameterSubZero : parameter - (0 : Fraction.Rational) = parameter := by ring1
    rw [Affine.line_zero, parameterSubZero] at distance
    rw [distance] at estimate
    apply estimate.trans
    have squared : parameter ^ 2 ≤ (1 : Fraction.Rational) := by
      simpa only [_root_.one_pow] using Fraction.Order.Arithmetic.pow_le_pow_direct inside.1 inside.2 2
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squared
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide : (0 : Fraction.Rational) ≤ 2) nonnegative)
        (Gaussian.Norm.Basic.normSq_nonneg (finish - start)))
    simpa only [Fraction.Field.mul_assoc, Fraction.Field.mul_one_direct] using scaled
  have estimate := Dense.Gaussian.Primitive.Segment.Comparison.DensePrimitive.difference_increment_le primitive
    comparison 1 start (finish - start) Gaussian.Norm.Basic.normSq_one
    (⟨0, 1, by decide⟩ : Data.Rat.Interval.Bounds) (fun _ inside =>
      Box.contains_line startInside finishInside inside)
    (fun _ inside => Box.contains_line startInside finishInside inside)
    (2 * bound * Data.Gaussian.Norm.Basic.normSq (finish - start)) gap (first := 1) (last := 0) ⟨by decide, le_rfl⟩
      ⟨le_rfl, by decide⟩
  rw [Affine.line_zero, Affine.line_one, _root_.one_mul] at estimate
  have linearEval (point : Gaussian.Basic.Canonical) : linear.eval point = coefficient.eval start * point := by
    change (0 * point + coefficient.eval start) * point + 0 = _
    rw [Gaussian.Basic.zero_mul, _root_.zero_add,
      _root_.add_zero]
  change Data.Gaussian.Norm.Basic.normSq (_ - _ - (linear.eval finish - linear.eval start)) ≤ _ at estimate
  rw [linearEval, linearEval, ← mul_sub] at estimate
  have oneSubZero : (1 : Fraction.Rational) - 0 = 1 := by decide
  exact estimate.trans_eq (by rw [oneSubZero, _root_.one_pow]; ring1)

/-- Compute the antiderivative once and retain the supplied derivative
ceiling. The hypothetical Horner remainder appears only in the erased proof.
Zero derivative bounds produce an exactly zero Taylor allowance.

The retained antiderivative and derivative ceiling determine the same quadratic remainder allowance; no auxiliary Horner
ceiling is stored. -/
@[expose] def ofDerivativeBound (coefficient : Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Box)
    (bound : Fraction.Rational) (nonnegative : 0 ≤ bound)
    (bounded : ∀ point, box.Contains point → Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative
      coefficient).eval point) ≤ bound) :
    DensePrimitive coefficient box where
  value := Dense.Gaussian.Antiderivative.denseAntiderivative coefficient
  derivative_eq := Dense.Gaussian.Antiderivative.denseAntiderivative_derivative coefficient
  remainderBound := 4 * bound
  remainderBound_nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative
  increment_bound := fun firstInside lastInside =>
    (DensePrimitive.ofPolynomial coefficient box).increment_bound_of_derivative
      firstInside lastInside bound nonnegative bounded

end Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate.DensePrimitive

end
