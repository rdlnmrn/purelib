module
import Purelib.Data.Rat.Interval.Radius
import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Sign.Basic
import Purelib.Data.Rat.Sign.Jump
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs.Neutral
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-!
# Endpoint size bounds for nonzero resolved Cauchy events

The original signed-remainder certificate forces a nonpositive endpoint
product. Retained finite Horner and Lipschitz bounds control the endpoint
square and every supplied parameter in the same cell.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution
public section
open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial

/-- A nonzero resolved Cauchy event forces the displayed denominator to
have opposite signs, or to vanish, at the two rational endpoints.  This is
the finite sign-crossing fact needed for quantitative event approximation;
it does not introduce a zero of the denominator between the endpoints. -/
theorem denominator_endpoint_mul_nonpos_of_index_ne_zero
    {R S : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (resolution : Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution R S interval)
    (indexNonzero : Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 R S
      interval.lower interval.upper ≠ 0) :
    S.eval interval.lower * S.eval interval.upper ≤ 0 := by
  cases resolution with
  | neutral denominator chain =>
      exact (indexNonzero chain.cauchyIndex2_eq_zero).elim
  | numerator certificate tail =>
      by_contra productNotNonpositive
      have productPositive :
          0 < S.eval interval.lower * S.eval interval.upper :=
        lt_of_not_ge productNotNonpositive
      have denominatorSigns :
          Data.Rat.Sign.Basic.sign (S.eval interval.lower) = Data.Rat.Sign.Basic.sign (S.eval interval.upper) :=
        Data.Rat.Sign.Basic.sign_eq_of_mul_pos productPositive
      have numeratorSigns :
          Data.Rat.Sign.Basic.sign (R.eval interval.lower) = Data.Rat.Sign.Basic.sign (R.eval interval.upper) :=
        Data.Rat.Sign.Basic.sign_eq_of_mul_pos certificate.endpoint_stable
      apply indexNonzero
      rw [Dense.Rational.CauchyIndex.Events.Signs.Neutral.cauchyIndex2_eq_firstJumps_of_neutralTail
        certificate.polynomial_nonzero tail]
      unfold Data.Rat.Sign.Jump.signJump
      rw [denominatorSigns, numeratorSigns]
      ring1

/-- The lower-endpoint denominator value of a nonzero resolved event is
quadratically small in the displayed cell width, with a coefficient obtained
by the existing finite Horner scan.

The scalar transport retains the original factor, box and boundary witness. Its winding identity uses the same retained
nonzero constant and factor values. -/
theorem denominator_lower_eval_sq_le
    {R S : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (resolution : Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution R S interval)
    (indexNonzero : Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 R S
      interval.lower interval.upper ≠ 0) :
    S.eval interval.lower ^ 2 ≤
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound S interval *
        (interval.upper - interval.lower) ^ 2 := by
  have product :=
    resolution.denominator_endpoint_mul_nonpos_of_index_ne_zero indexNonzero
  have endpoint :=
    Purelib.Data.Rat.Bounds.Square.left_sq_le_sub_sq_of_mul_nonpos
    product
  have difference := Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le S interval
    (⟨le_rfl, interval.valid⟩ : interval.Contains interval.lower)
    (⟨interval.valid, le_rfl⟩ : interval.Contains interval.upper)
  calc
    S.eval interval.lower ^ 2 ≤
        (S.eval interval.lower - S.eval interval.upper) ^ 2 := endpoint
    _ ≤ Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound S interval *
        (interval.lower - interval.upper) ^ 2 := difference
    _ = Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound S interval *
        (interval.upper - interval.lower) ^ 2 := by
      ring1

/-- Every displayed parameter in a nonzero resolved event has a denominator
residual bounded by four times the finite Horner coefficient times width
squared.  The statement is uniform over the whole rational cell and does not
select or complete a root.

The scalar transport retains the original factor, box and boundary witness. Its winding identity uses the same retained
nonzero constant and factor values. -/
theorem denominator_eval_sq_le
    {R S : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (resolution : Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution R S interval)
    (indexNonzero : Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 R S
      interval.lower interval.upper ≠ 0)
    (parameter : Fraction.Rational) (inside : interval.Contains parameter) :
    S.eval parameter ^ 2 ≤
      4 * Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound S interval *
        (interval.upper - interval.lower) ^ 2 := by
  let lipschitz :=
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound S interval
  let widthSq := (interval.upper - interval.lower) ^ 2
  let scale := lipschitz * widthSq
  change S.eval parameter ^ 2 ≤ 4 * lipschitz * widthSq
  have lowerBound : S.eval interval.lower ^ 2 ≤ scale := by
    simpa only [lipschitz, widthSq, scale] using
      resolution.denominator_lower_eval_sq_le indexNonzero
  have difference := Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le S interval
    inside (⟨le_rfl, interval.valid⟩ : interval.Contains interval.lower)
  have distance : (parameter - interval.lower) ^ 2 ≤
      Data.Rat.Interval.Radius.sampleRadiusSq interval interval.lower :=
    Data.Rat.Interval.Radius.sub_sq_le_sampleRadiusSq
      (sample := interval.lower) interval inside
  have lipschitzNonnegative : 0 ≤ lipschitz := by
    simpa only [lipschitz] using
      (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg S interval).2
  have scaledDistance :
      lipschitz * (parameter - interval.lower) ^ 2 ≤ scale := by
    calc
      lipschitz * (parameter - interval.lower) ^ 2 ≤
          lipschitz *
            Data.Rat.Interval.Radius.sampleRadiusSq interval interval.lower :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distance
          lipschitzNonnegative
      _ = scale := by
        rw [Data.Rat.Interval.Radius.sampleRadiusSq_lower_eq_widthSq]
  have differenceBound :
      (S.eval parameter - S.eval interval.lower) ^ 2 ≤ scale :=
    difference.trans scaledDistance
  have sumBound :
      S.eval interval.lower ^ 2 +
          (S.eval parameter - S.eval interval.lower) ^ 2 ≤
        scale + scale :=
    add_le_add lowerBound differenceBound
  have doubled :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound
      (show (0 : Fraction.Rational) ≤ 2 by decide)
  calc
    S.eval parameter ^ 2 =
        (S.eval interval.lower +
          (S.eval parameter - S.eval interval.lower)) ^ 2 := by ring1
    _ ≤ 2 * (S.eval interval.lower ^ 2 +
          (S.eval parameter - S.eval interval.lower) ^ 2) :=
      Purelib.Data.Rat.Bounds.Square.add_sq_le_two _ _
    _ ≤ 2 * (scale + scale) := doubled
    _ = 4 * lipschitz * widthSq := by
      dsimp only [scale]
      ring1

end
end Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution
