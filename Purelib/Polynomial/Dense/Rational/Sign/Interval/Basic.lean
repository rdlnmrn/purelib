module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Data.Rat.Interval.Radius
import Purelib.Data.Rat.Sign.Products
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Strict polynomial signs on rational intervals

The retained polynomial inputs and interval bounds determine the certificate
indices. Each certificate retains its actual samples, signed chains and branch evidence.
-/

namespace Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic

open Purelib
open Purelib.Polynomial
open Purelib.Data.Rat

@[expose] public section

set_option genInjectivity false in
/-- Proof-bearing finite strict-sign certificate.

The retained sample lies in the interval, and its squared value exceeds the
Lipschitz error bound throughout that interval. -/
structure Certificate (p : Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds)
  where
  /-- The rational sample at which the polynomial sign is certified. -/ sample : Fraction.Rational
  /-- The retained sample belongs to the closed interval. -/ sampleInside : interval.Contains sample
  /-- The squared sample value strictly exceeds the interval Lipschitz error bound. -/ margin :
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p interval *
      Data.Rat.Interval.Radius.sampleRadiusSq interval sample < p.eval sample ^ 2

constructive_injectivity Certificate

end

end Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic

namespace Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic.Certificate

open Purelib
open Purelib.Polynomial
open Purelib.Data.Rat

/-- Every value in the interval has the same strict sign as the sample value.

The retained squared margin excludes both a zero value and a sign change from the sample. -/
public theorem eval_mul_sample_pos {p : Dense.Rational.Basic.CoordinatePolynomial} {interval :
  Data.Rat.Interval.Bounds}
    (certificate : Dense.Rational.Sign.Interval.Basic.Certificate p interval) {x : Fraction.Rational}
    (inside : interval.Contains x) :
    0 < p.eval x * p.eval certificate.sample := by
  have difference := Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le p interval inside certificate.sampleInside
  have radius := Data.Rat.Interval.Radius.sub_sq_le_sampleRadiusSq interval
    (sample := certificate.sample) (x := x) inside
  have slopeNonnegative := (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg p interval).2
  have scaledRadius :
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p interval *
          (x - certificate.sample) ^ 2 ≤
        Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p interval *
          Data.Rat.Interval.Radius.sampleRadiusSq interval certificate.sample :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      radius slopeNonnegative
  exact Data.Rat.Sign.Products.mul_pos_of_sub_sq_lt_sq
    (difference.trans_lt (scaledRadius.trans_lt certificate.margin))

/-- Polynomial values at any two points of the certified interval have positive product.

Both points belong to the retained interval. Their signs agree with the same
nonzero sample value, so their product is strictly positive. -/
public theorem eval_mul_pos {p : Dense.Rational.Basic.CoordinatePolynomial} {interval :
  Data.Rat.Interval.Bounds}
    (certificate : Dense.Rational.Sign.Interval.Basic.Certificate p interval) {x y : Fraction.Rational}
    (xInside : interval.Contains x) (yInside : interval.Contains y) :
    0 < p.eval x * p.eval y := by
  have xSample := certificate.eval_mul_sample_pos xInside
  have ySample := certificate.eval_mul_sample_pos yInside
  rcases lt_trichotomy (p.eval certificate.sample) 0 with
      sampleNegative | sampleZero | samplePositive
  · have xNegative : p.eval x < 0 := by
      rcases lt_trichotomy (p.eval x) 0 with xNegative | xZero | xPositive
      · exact xNegative
      · rw [xZero, zero_mul] at xSample
        exact (lt_irrefl 0 xSample).elim
      · have productNegative :=
          Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
            xPositive sampleNegative
        exact (lt_asymm xSample productNegative).elim
    have yNegative : p.eval y < 0 := by
      rcases lt_trichotomy (p.eval y) 0 with yNegative | yZero | yPositive
      · exact yNegative
      · rw [yZero, zero_mul] at ySample
        exact (lt_irrefl 0 ySample).elim
      · have productNegative :=
          Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
            yPositive sampleNegative
        exact (lt_asymm ySample productNegative).elim
    exact Fraction.Order.Arithmetic.mul_pos_of_neg_of_neg_direct
      xNegative yNegative
  · rw [sampleZero, mul_zero] at xSample
    exact (lt_irrefl 0 xSample).elim
  · have xPositive : 0 < p.eval x := by
      rcases lt_trichotomy (p.eval x) 0 with xNegative | xZero | xPositive
      · have productNegative :=
          Fraction.Order.Arithmetic.mul_neg_of_neg_of_pos_direct
            xNegative samplePositive
        exact (lt_asymm xSample productNegative).elim
      · rw [xZero, zero_mul] at xSample
        exact (lt_irrefl 0 xSample).elim
      · exact xPositive
    have yPositive : 0 < p.eval y := by
      rcases lt_trichotomy (p.eval y) 0 with yNegative | yZero | yPositive
      · have productNegative :=
          Fraction.Order.Arithmetic.mul_neg_of_neg_of_pos_direct
            yNegative samplePositive
        exact (lt_asymm ySample productNegative).elim
      · rw [yZero, zero_mul] at ySample
        exact (lt_irrefl 0 ySample).elim
      · exact yPositive
    exact Fraction.Order.Arithmetic.mul_pos_direct xPositive yPositive

/-- The polynomial does not vanish at any point of the certified interval.

Interval membership and the retained strict squared margin exclude a zero
value at the supplied point. -/
public theorem eval_ne_zero {p : Dense.Rational.Basic.CoordinatePolynomial} {interval :
  Data.Rat.Interval.Bounds}
    (certificate : Dense.Rational.Sign.Interval.Basic.Certificate p interval) {x : Fraction.Rational}
    (inside : interval.Contains x) : p.eval x ≠ 0 := by
  intro zero
  have positive := certificate.eval_mul_sample_pos inside
  rw [zero, zero_mul] at positive
  exact (lt_irrefl 0 positive).elim

/-- The lower and upper endpoint values have positive product.

Both endpoints belong to the retained closed interval, so the strict sample
margin gives a positive product of their polynomial values. -/
public theorem endpoint_stable {p : Dense.Rational.Basic.CoordinatePolynomial} {interval :
  Data.Rat.Interval.Bounds}
    (certificate : Dense.Rational.Sign.Interval.Basic.Certificate p interval) :
    0 < p.eval interval.lower * p.eval interval.upper :=
  certificate.eval_mul_pos ⟨le_rfl, interval.valid⟩ ⟨interval.valid, le_rfl⟩

/-- A strict-sign interval certificate implies the polynomial zero test is false.

The retained sample supplies an explicit nonzero evaluation, which rules
out the polynomial zero test. -/
public theorem polynomial_nonzero {p : Dense.Rational.Basic.CoordinatePolynomial} {interval :
  Data.Rat.Interval.Bounds}
    (certificate : Dense.Rational.Sign.Interval.Basic.Certificate p interval) : p.isZero = false :=
  Dense.Basic.DensePolynomial.isZero_false_of_eval_ne
    (certificate.eval_ne_zero certificate.sampleInside)

end Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic.Certificate
