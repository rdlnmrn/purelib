module
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Bounds.InverseScale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

/-!
# Quadrance separation for a retained coprime pair

The original Gaussian polynomials and cofactors retain their exact or
approximate identity on the same rational box. Computed box majorants
and scaled reciprocals supply quantitative residual and lower bounds.
-/

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

namespace Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Box

open Purelib.Data.Rat.Bounds

/-- Residual threshold for the left member of a displayed Bézout pair.

The original left cofactor of the retained coprimality certificate supplies
its computed box value majorant. The threshold is the reciprocal of
sixteen times that same positive majorant. -/
@[expose] public def leftThreshold
    {p q : Basic.CanonicalCoefficients.CoefficientPolynomial} (coprime :
      Dense.Gaussian.Coprime.Basic.CoprimeCertificate p q)
    (ambient : Box) : Fraction.Rational :=
  1 / (16 * Dense.Gaussian.Bounds.Box.denseEvalNormMajorant coprime.left ambient)

/-- Positive squared-norm margin forced on the right member once the left
residual is below `leftThreshold`.

The original right cofactor of the retained coprimality certificate supplies
its computed box value majorant. The margin is the reciprocal of sixteen
times that same positive majorant. -/
@[expose] public def rightMargin
    {p q : Basic.CanonicalCoefficients.CoefficientPolynomial} (coprime :
      Dense.Gaussian.Coprime.Basic.CoprimeCertificate p q)
    (ambient : Box) : Fraction.Rational :=
  1 / (16 * Dense.Gaussian.Bounds.Box.denseEvalNormMajorant coprime.right ambient)

/-- The residual threshold obtained from the positive left Bezout-cofactor majorant is positive.

The computed majorant of the original left cofactor is positive.
Multiplication by sixteen retains positivity, so its displayed reciprocal
gives a positive residual threshold on the original box. -/
public theorem leftThreshold_pos
    {p q : Basic.CanonicalCoefficients.CoefficientPolynomial} (coprime :
      Dense.Gaussian.Coprime.Basic.CoprimeCertificate p q)
    (ambient : Box) : 0 < Dense.Gaussian.Coprime.Bounds.Box.leftThreshold coprime ambient := by
  apply Fraction.Order.Field.div_pos_direct (by decide)
  exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos coprime.left ambient)

/-- The forced right-value margin obtained from the positive right Bezout-cofactor majorant is positive.

The computed majorant of the original right cofactor is positive.
Multiplication by sixteen retains positivity, so its displayed reciprocal
gives a positive right-value margin on the original box. -/
public theorem rightMargin_pos
    {p q : Basic.CanonicalCoefficients.CoefficientPolynomial} (coprime :
      Dense.Gaussian.Coprime.Basic.CoprimeCertificate p q)
    (ambient : Box) : 0 < Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime ambient := by
  apply Fraction.Order.Field.div_pos_direct (by decide)
  exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos coprime.right ambient)

/-- The finite Bézout identity gives a uniform right-value margin wherever
the displayed left residual is sufficiently small.

The retained Bezout identity uses the original pair of polynomials and
cofactors at the same contained point. Their original box majorants and
reciprocal scales force the right quadrance above its margin whenever
the left quadrance is below the supplied residual threshold. -/
public theorem rightMargin_le_of_left_small
    {p q : Basic.CanonicalCoefficients.CoefficientPolynomial} (coprime :
      Dense.Gaussian.Coprime.Basic.CoprimeCertificate p q)
    (ambient : Box) {z : Gaussian.Basic.Canonical} (inside : ambient.Contains z)
    (small : Data.Gaussian.Norm.Basic.normSq (p.eval z) ≤ Dense.Gaussian.Coprime.Bounds.Box.leftThreshold coprime
      ambient) :
    Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime ambient ≤ Data.Gaussian.Norm.Basic.normSq (q.eval z) :=
      open Purelib in by
  let leftMajorant := Dense.Gaussian.Bounds.Box.denseEvalNormMajorant coprime.left ambient
  let rightMajorant := Dense.Gaussian.Bounds.Box.denseEvalNormMajorant coprime.right ambient
  let leftValue := coprime.left.eval z
  let rightValue := coprime.right.eval z
  let pValue := p.eval z
  let qValue := q.eval z
  have leftMajorantPositive : 0 < leftMajorant :=
    Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos coprime.left ambient
  have rightMajorantPositive : 0 < rightMajorant :=
    Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos coprime.right ambient
  have leftBound : Data.Gaussian.Norm.Basic.normSq leftValue ≤ leftMajorant :=
    Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant coprime.left inside
  have rightBound : Data.Gaussian.Norm.Basic.normSq rightValue ≤ rightMajorant :=
    Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant coprime.right inside
  by_cases marginBound : Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime ambient ≤
    Data.Gaussian.Norm.Basic.normSq qValue
  · exact marginBound
  · have qBound : Data.Gaussian.Norm.Basic.normSq qValue ≤ Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime
      ambient :=
      (lt_of_not_ge marginBound).le
    have leftProduct : Data.Gaussian.Norm.Basic.normSq leftValue * Data.Gaussian.Norm.Basic.normSq pValue ≤
        leftMajorant * Dense.Gaussian.Coprime.Bounds.Box.leftThreshold coprime ambient :=
      Fraction.Order.Arithmetic.mul_le_mul_direct leftBound small
        (Gaussian.Norm.Basic.normSq_nonneg pValue) leftMajorantPositive.le
    have rightProduct : Data.Gaussian.Norm.Basic.normSq rightValue * Data.Gaussian.Norm.Basic.normSq qValue ≤
        rightMajorant * Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime ambient :=
      Fraction.Order.Arithmetic.mul_le_mul_direct rightBound qBound
        (Gaussian.Norm.Basic.normSq_nonneg qValue) rightMajorantPositive.le
    have leftScaled : leftMajorant * Dense.Gaussian.Coprime.Bounds.Box.leftThreshold coprime ambient ≤
        (1 / 16 : Fraction.Rational) := by
      exact InverseScale.majorant_mul_scaled_inverse_le leftMajorantPositive
    have rightScaled : rightMajorant * Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime ambient ≤
        (1 / 16 : Fraction.Rational) := by
      exact InverseScale.majorant_mul_scaled_inverse_le rightMajorantPositive
    have sumNorm := Gaussian.Norm.Bounds.normSq_add_le_two
      (leftValue * pValue) (rightValue * qValue)
    have bezout : 1 = leftValue * pValue + rightValue * qValue :=
      coprime.identity z
    have impossible : (1 : Fraction.Rational) ≤ 1 / 4 := by
      calc
        (1 : Fraction.Rational) =
            Data.Gaussian.Norm.Basic.normSq (leftValue * pValue + rightValue * qValue) := by
          rw [← bezout, Gaussian.Norm.Basic.normSq_one]
        _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (leftValue * pValue) +
              Data.Gaussian.Norm.Basic.normSq (rightValue * qValue)) := sumNorm
        _ = 2 * (Data.Gaussian.Norm.Basic.normSq leftValue * Data.Gaussian.Norm.Basic.normSq pValue +
              Data.Gaussian.Norm.Basic.normSq rightValue * Data.Gaussian.Norm.Basic.normSq qValue) := by
          rw [Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul]
        _ ≤ 2 * ((1 / 16 : Fraction.Rational) + 1 / 16) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add (leftProduct.trans leftScaled)
              (rightProduct.trans rightScaled)) (by decide)
        _ = 1 / 4 := by decide
    exact ((show ¬ ((1 : Fraction.Rational) ≤ 1 / 4) by decide)
      impossible).elim

end Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Box
