module
import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Bounds.InverseScale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Tactic.Ring

/-!
# Derivative quadrance separation from Bezout identities

The original Gaussian polynomials and cofactors retain their exact or
approximate identity on the same rational box. Computed box majorants
and scaled reciprocals supply quantitative residual and lower bounds.
-/

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

namespace Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Bezout

open Purelib.Data.Rat.Bounds

/-- The conservative residual scale used by an approximate displayed
Bézout identity.

The original left polynomial and ambient box supply a positive computed
value majorant. Its reciprocal scaled by sixteen determines the same
residual threshold for the original approximate identity. -/
@[expose] public def approximateThreshold (left : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (ambient : Box) : Fraction.Rational :=
  1 / (16 * Dense.Gaussian.Bounds.Box.denseEvalNormMajorant left ambient)

/-- The conservative derivative margin used by an approximate displayed
Bézout identity.

The original right polynomial and ambient box supply a positive computed
value majorant. Its reciprocal scaled by sixteen determines the retained
lower derivative margin for the original approximate identity. -/
@[expose] public def approximateMargin (right : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (ambient : Box) : Fraction.Rational :=
  1 / (16 * Dense.Gaussian.Bounds.Box.denseEvalNormMajorant right ambient)

/-- The approximate Bezout residual threshold is positive on every supplied box.

The original left polynomial has a positive value majorant on the
retained ambient box. Its product with sixteen is positive, so the
displayed reciprocal threshold is also positive. -/
public theorem approximateThreshold_pos (left : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (ambient : Box) : 0 < Dense.Gaussian.Derivative.Separation.Bezout.approximateThreshold left ambient
      := by
  apply Fraction.Order.Field.div_pos_direct (by decide)
  exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos left ambient)

/-- The approximate Bezout derivative margin is positive on every supplied box.

The original right polynomial has a positive value majorant on the
retained ambient box. Its product with sixteen is positive, so the
displayed reciprocal derivative margin is also positive. -/
public theorem approximateMargin_pos (right : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (ambient : Box) : 0 < Dense.Gaussian.Derivative.Separation.Bezout.approximateMargin right ambient :=
      by
  apply Fraction.Order.Field.div_pos_direct (by decide)
  exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos right ambient)

/-- The retained approximate Bezout identity forces derivative quadrance above the computed margin.

The original point lies in the retained ambient box and its polynomial
quadrance satisfies the displayed threshold. The retained identity error
is at most one sixteenth; bounding both original cofactor products by
one sixteenth forces the derivative quadrance above the computed margin. -/
public theorem approximateMargin_le
    (p left right : Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box)
    (approximateIdentity : ∀ {z : Gaussian.Basic.Canonical}, ambient.Contains z →
      Data.Gaussian.Norm.Basic.normSq
        (1 - (left.eval z * p.eval z + right.eval z *
          (Dense.Gaussian.GCD.derivative p).eval z)) ≤
        (1 / 16 : Fraction.Rational))
    {z : Gaussian.Basic.Canonical} (inside : ambient.Contains z)
    (small : Data.Gaussian.Norm.Basic.normSq (p.eval z) ≤
      Dense.Gaussian.Derivative.Separation.Bezout.approximateThreshold left ambient) :
    Dense.Gaussian.Derivative.Separation.Bezout.approximateMargin right ambient ≤
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative p).eval z) := open Purelib in by
  let leftMajorant := Dense.Gaussian.Bounds.Box.denseEvalNormMajorant left ambient
  let rightMajorant := Dense.Gaussian.Bounds.Box.denseEvalNormMajorant right ambient
  let threshold := Dense.Gaussian.Derivative.Separation.Bezout.approximateThreshold left ambient
  let margin := Dense.Gaussian.Derivative.Separation.Bezout.approximateMargin right ambient
  have leftMajorantPositive : 0 < leftMajorant :=
    Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos left ambient
  have rightMajorantPositive : 0 < rightMajorant :=
    Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos right ambient
  let leftValue := left.eval z
  let rightValue := right.eval z
  let value := p.eval z
  let derivativeValue := (Dense.Gaussian.GCD.derivative p).eval z
  let error := 1 - (leftValue * value + rightValue * derivativeValue)
  have leftBound : Data.Gaussian.Norm.Basic.normSq leftValue ≤ leftMajorant :=
    Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant left inside
  have rightBound : Data.Gaussian.Norm.Basic.normSq rightValue ≤ rightMajorant :=
    Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant right inside
  have errorBound : Data.Gaussian.Norm.Basic.normSq error ≤ (1 / 16 : Fraction.Rational) := by
    exact approximateIdentity inside
  by_cases marginBound : margin ≤ Data.Gaussian.Norm.Basic.normSq derivativeValue
  · exact marginBound
  · have derivativeBound : Data.Gaussian.Norm.Basic.normSq derivativeValue ≤ margin :=
      (lt_of_not_ge marginBound).le
    have leftProduct : Data.Gaussian.Norm.Basic.normSq leftValue * Data.Gaussian.Norm.Basic.normSq value ≤
        leftMajorant * threshold :=
      Fraction.Order.Arithmetic.mul_le_mul_direct leftBound small
        (Gaussian.Norm.Basic.normSq_nonneg value) leftMajorantPositive.le
    have rightProduct : Data.Gaussian.Norm.Basic.normSq rightValue * Data.Gaussian.Norm.Basic.normSq
      derivativeValue ≤
        rightMajorant * margin :=
      Fraction.Order.Arithmetic.mul_le_mul_direct rightBound derivativeBound
        (Gaussian.Norm.Basic.normSq_nonneg derivativeValue) rightMajorantPositive.le
    have leftScaled : leftMajorant * threshold ≤
        (1 / 16 : Fraction.Rational) :=
      InverseScale.majorant_mul_scaled_inverse_le leftMajorantPositive
    have rightScaled : rightMajorant * margin ≤
        (1 / 16 : Fraction.Rational) :=
      InverseScale.majorant_mul_scaled_inverse_le rightMajorantPositive
    have pairNorm := Gaussian.Norm.Bounds.normSq_add_le_two
      (leftValue * value) (rightValue * derivativeValue)
    have pairBound :
        Data.Gaussian.Norm.Basic.normSq (leftValue * value + rightValue * derivativeValue) ≤
          (1 / 4 : Fraction.Rational) := by
      calc
        Data.Gaussian.Norm.Basic.normSq (leftValue * value + rightValue * derivativeValue) ≤
            2 * (Data.Gaussian.Norm.Basic.normSq (leftValue * value) +
              Data.Gaussian.Norm.Basic.normSq (rightValue * derivativeValue)) := pairNorm
        _ = 2 * (Data.Gaussian.Norm.Basic.normSq leftValue * Data.Gaussian.Norm.Basic.normSq value +
              Data.Gaussian.Norm.Basic.normSq rightValue * Data.Gaussian.Norm.Basic.normSq derivativeValue) :=
                by
          rw [Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul]
        _ ≤ 2 * ((1 / 16 : Fraction.Rational) + 1 / 16) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add (leftProduct.trans leftScaled)
              (rightProduct.trans rightScaled)) (by decide)
        _ = 1 / 4 := by decide
    have totalNorm := Gaussian.Norm.Bounds.normSq_add_le_two
      (leftValue * value + rightValue * derivativeValue) error
    have identity :
        1 = (leftValue * value + rightValue * derivativeValue) + error := by
      dsimp only [error]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
          Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;>
        ring1
    have totalBound :
        Data.Gaussian.Norm.Basic.normSq
            ((leftValue * value + rightValue * derivativeValue) + error) ≤
          (5 / 8 : Fraction.Rational) := by
      calc
        Data.Gaussian.Norm.Basic.normSq
            ((leftValue * value + rightValue * derivativeValue) + error) ≤
            2 *
            (Data.Gaussian.Norm.Basic.normSq (leftValue * value + rightValue * derivativeValue) +
              Data.Gaussian.Norm.Basic.normSq error) := totalNorm
        _ ≤ 2 * ((1 / 4 : Fraction.Rational) + 1 / 16) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add pairBound errorBound) (by decide)
        _ = 5 / 8 := by decide
    have impossible : (1 : Fraction.Rational) ≤ 5 / 8 := by
      calc
        (1 : Fraction.Rational) =
            Data.Gaussian.Norm.Basic.normSq
              ((leftValue * value + rightValue * derivativeValue) +
                error) := by
          rw [← identity, Gaussian.Norm.Basic.normSq_one]
        _ ≤ 5 / 8 := totalBound
    exact ((show ¬ ((1 : Fraction.Rational) ≤ 5 / 8) by decide)
      impossible).elim

/-- Construct a derivative-separation certificate from a uniformly bounded approximate Bezout identity.

The original polynomial, cofactors and ambient box index the certificate.
The supplied identity-error bound and computed positive reciprocal scales
provide its retained threshold, margin and quantitative lower proof. -/
@[expose] public def ofApproximateBezout
    (p left right : Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box)
    (approximateIdentity : ∀ {z : Gaussian.Basic.Canonical}, ambient.Contains z →
      Data.Gaussian.Norm.Basic.normSq
        (1 - (left.eval z * p.eval z + right.eval z *
          (Dense.Gaussian.GCD.derivative p).eval z)) ≤
        (1 / 16 : Fraction.Rational)) :
    Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient where
  threshold := Dense.Gaussian.Derivative.Separation.Bezout.approximateThreshold left ambient
  threshold_pos := Dense.Gaussian.Derivative.Separation.Bezout.approximateThreshold_pos left ambient
  margin := Dense.Gaussian.Derivative.Separation.Bezout.approximateMargin right ambient
  margin_pos := Dense.Gaussian.Derivative.Separation.Bezout.approximateMargin_pos right ambient
  lower := Dense.Gaussian.Derivative.Separation.Bezout.approximateMargin_le p left right ambient approximateIdentity

/-- Construct derivative separation from the original exact squarefree Bezout certificate.

The original squarefree certificate retains both cofactors and their
exact Bezout identity for the same polynomial. Its zero identity error
satisfies the approximate construction with the same displayed box and
computed reciprocal threshold and derivative margin. -/
@[expose] public def ofSquarefree
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (squarefree :
      Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (ambient : Box) : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient :=
  Dense.Gaussian.Derivative.Separation.Bezout.ofApproximateBezout p squarefree.left squarefree.right ambient (by
    intro z _inside
    rw [squarefree.identity z]
    simp only [Gaussian.Basic.sub_self, Gaussian.Norm.Basic.normSq_zero]
    exact (show (0 : Fraction.Rational) ≤ 1 / 16 by decide))

end Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Bezout
