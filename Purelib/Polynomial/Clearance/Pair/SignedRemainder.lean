module
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Polynomial.Clearance.Pair.Basic
public import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Evaluation
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Purelib.Algebra.Semiring.Normalization
import Purelib.Algebra.Ring.Multiplication
import Purelib.Algebra.Group.Negation

namespace Purelib.Polynomial.Clearance.Pair.Basic

open Purelib
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Bounds
open Purelib.Polynomial
open Purelib.Algebra.Semiring
open Purelib.Algebra.Ring

/-- Finite quotient majorant used when transporting clearance through one
signed Euclidean step.

The original quotient polynomial is retained from the exact Euclidean
division result. Its interval square majorant is enlarged by one and
doubled without selecting another quotient or interval. -/
@[expose] public def Certificate.signedStepMajorant (p q : Dense.Rational.Basic.CoordinatePolynomial) (interval :
  Data.Rat.Interval.Bounds) : Fraction.Rational :=
  2 * (Dense.Rational.Bounds.Horner.evalSqBound (Dense.Basic.DensePolynomial.divMod p q).quotient interval + 1)

/-- The finite quotient majorant used by a signed Euclidean step is strictly positive.

The retained finite quotient majorant is nonnegative. Adding one and
multiplying by the original positive factor two makes its bound strict. -/
public theorem Certificate.signedStepMajorant_pos (p q : Dense.Rational.Basic.CoordinatePolynomial) (interval :
  Data.Rat.Interval.Bounds) :
    0 < Certificate.signedStepMajorant p q interval := by
  have innerPositive : 0 < Dense.Rational.Bounds.Horner.evalSqBound (Dense.Basic.DensePolynomial.divMod p q).quotient
    interval + 1 := by
    calc
      0 < 1 := by decide
      _ ≤ Dense.Rational.Bounds.Horner.evalSqBound (Dense.Basic.DensePolynomial.divMod p q).quotient interval + 1 :=
        add_le_add (Dense.Rational.Bounds.Horner.evalSqBound_nonneg _ _) (le_refl 1)
  exact Order.Arithmetic.mul_pos_direct (by decide) innerPositive

/-- A pointwise sum-of-squares clearance transports constructively through
one signed Euclidean step.  No polynomial gcd or root enumeration is used.

The original Euclidean remainder is negated while the retained quotient
majorant divides the positive clearance bound. The original signed-step
evaluation identity transports the pointwise sum-of-squares certificate. -/
@[expose] public def Certificate.signedStep {p q : Dense.Rational.Basic.CoordinatePolynomial} {interval :
  Data.Rat.Interval.Bounds}
    (certificate : Clearance.Pair.Basic.Certificate p q interval) :
    Clearance.Pair.Basic.Certificate q (-((Dense.Basic.DensePolynomial.divMod p q).remainder)) interval where
  bound := certificate.bound / Certificate.signedStepMajorant p q interval
  positive := Order.Field.div_pos_direct certificate.positive
    (Certificate.signedStepMajorant_pos p q interval)
  lower := by
    intro x inside
    let next := -((Dense.Basic.DensePolynomial.divMod p q).remainder)
    let quotientBound := Dense.Rational.Bounds.Horner.evalSqBound (Dense.Basic.DensePolynomial.divMod p q).quotient
      interval
    let qValue := q.eval x
    let nextValue := next.eval x
    have quotientBoundNonnegative : 0 ≤ quotientBound :=
      Dense.Rational.Bounds.Horner.evalSqBound_nonneg _ _
    have quotientSqBound : (Dense.Basic.DensePolynomial.divMod p q).quotient.eval x ^ 2 ≤
        quotientBound := Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound _ interval inside
    have productSqBound :
        (qValue * (Dense.Basic.DensePolynomial.divMod p q).quotient.eval x) ^ 2 ≤
          qValue ^ 2 * quotientBound := by
      rw [Normalization.product_pow qValue ((Dense.Basic.DensePolynomial.divMod p q).quotient.eval x) 2]
      exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        quotientSqBound
        (Order.Arithmetic.sq_nonneg_direct qValue)
    have pSqBound : p.eval x ^ 2 ≤
        2 * (qValue ^ 2 * quotientBound + nextValue ^ 2) := by
      have step := Dense.Rational.SignedRemainder.Evaluation.signedStep_eval_identity p q x
      change p.eval x =
        qValue * (Dense.Basic.DensePolynomial.divMod p q).quotient.eval x - nextValue at step
      rw [step]
      calc
        (qValue * (Dense.Basic.DensePolynomial.divMod p q).quotient.eval x - nextValue) ^ 2 =
            (qValue * (Dense.Basic.DensePolynomial.divMod p q).quotient.eval x + -nextValue) ^ 2 := by
          ring1
        _ ≤ 2 * ((qValue * (Dense.Basic.DensePolynomial.divMod p q).quotient.eval x) ^ 2 +
              (-nextValue) ^ 2) := Purelib.Data.Rat.Bounds.Square.add_sq_le_two _ _
        _ ≤ 2 * (qValue ^ 2 * quotientBound + nextValue ^ 2) :=
          Square.twice_le_twice (by
            have negativeSquare : (-nextValue) ^ 2 = nextValue ^ 2 := by
              rw [pow_two, pow_two, Multiplication.neg_mul_neg]
            rw [negativeSquare]
            exact add_le_add productSqBound (le_refl (nextValue ^ 2)))
    have sumBound : p.eval x ^ 2 + qValue ^ 2 ≤
        (qValue ^ 2 + nextValue ^ 2) *
          Certificate.signedStepMajorant p q interval := by
      calc
        p.eval x ^ 2 + qValue ^ 2 ≤
            2 * (qValue ^ 2 * quotientBound + nextValue ^ 2) +
              qValue ^ 2 := add_le_add pSqBound (le_refl _)
        _ ≤ (qValue ^ 2 + nextValue ^ 2) *
              Certificate.signedStepMajorant p q interval := by
          apply Order.Arithmetic.le_of_sub_nonneg_direct
          calc
            0 ≤ qValue ^ 2 + 2 * quotientBound * nextValue ^ 2 :=
              add_nonneg (Order.Arithmetic.sq_nonneg_direct qValue)
                (Order.Arithmetic.mul_nonneg_direct
                  (Order.Arithmetic.mul_nonneg_direct (by decide)
                    quotientBoundNonnegative)
                  (Order.Arithmetic.sq_nonneg_direct nextValue))
            _ = (qValue ^ 2 + nextValue ^ 2) *
                  Certificate.signedStepMajorant p q interval -
                (2 * (qValue ^ 2 * quotientBound + nextValue ^ 2) +
                  qValue ^ 2) := by
              dsimp only [Certificate.signedStepMajorant]
              ring1
    apply (Order.Field.div_le_iff_pos
      (Certificate.signedStepMajorant_pos p q interval)).2
    exact (certificate.lower x inside).trans sumBound

end Purelib.Polynomial.Clearance.Pair.Basic
