module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coefficients.Tail
public import Purelib.Polynomial.Dense.Gaussian.Evaluation.Norm.Weighted

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic

/-!
# Retained coefficient square majorants

Finite coefficient readbacks retain their original polynomials and interval
data. Their exact rational majorants provide positive radius or clearance
bounds without changing the underlying coefficient computations.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Polynomial

/-- Coefficient weight for all slots below the normalized leading degree.

The original degree multiplies the weighted squared norms of the exact
retained lower-coefficient tail in reverse order. Neither the tail nor its
coefficient order is replaced by this readback. -/
@[expose] public def denseLowerCoefficientWeight (p : Basic.CanonicalCoefficients.CoefficientPolynomial) :
  Fraction.Rational :=
  (p.natDegree : Fraction.Rational) *
    Dense.Gaussian.Evaluation.Norm.Weighted.weightedNormSum (Dense.Gaussian.Coefficients.Tail.lowerCoefficients
      p).reverse 0

/-- The weighted contribution of all coefficients below the leading term is nonnegative.

The degree cast is nonnegative and the original finite weighted norm
sum is nonnegative. Direct rational multiplication preserves both
retained factors in the displayed product. -/
public theorem denseLowerCoefficientWeight_nonneg (p : Basic.CanonicalCoefficients.CoefficientPolynomial) :
    0 ≤ denseLowerCoefficientWeight p := by
  exact Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le p.natDegree))
    (Dense.Gaussian.Evaluation.Norm.Weighted.weightedNormSum_nonneg _ 0)

/-- Compute a coefficient-derived rational square radius with lower bound one.

The original lower-coefficient weight is divided by the leading
coefficient quadrance, then increased by one. Its maximum with one
retains an explicit positive rational radius. -/
@[expose] public def denseLargeSquareRadius (p : Basic.CanonicalCoefficients.CoefficientPolynomial) : Fraction.Rational
  :=
  max 1 (denseLowerCoefficientWeight p / Data.Gaussian.Norm.Basic.normSq p.leadingCoeff + 1)

/-- The coefficient-computed large-square radius is at least one.

The original radius takes the maximum of one and its coefficient
quotient plus one. The same rational maximum therefore retains one
as a lower bound. -/
public theorem one_le_denseLargeSquareRadius (p : Basic.CanonicalCoefficients.CoefficientPolynomial) :
    1 ≤ denseLargeSquareRadius p :=
  Order.Basic.le_max_left _ _

/-- The coefficient-computed large-square radius is strictly positive.

The retained coefficient radius is at least one. The strict rational
comparison between zero and one makes that same radius positive. -/
public theorem denseLargeSquareRadius_pos (p : Basic.CanonicalCoefficients.CoefficientPolynomial) :
    0 < denseLargeSquareRadius p :=
  (by decide : (0 : Fraction.Rational) < 1).trans_le
    (one_le_denseLargeSquareRadius p)

end Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
