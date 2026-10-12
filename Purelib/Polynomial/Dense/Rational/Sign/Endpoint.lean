module
public import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Bounds.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Data.Rat.Interval.Radius
import Purelib.Data.Rat.Fraction.Order.PositiveMul
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

namespace Purelib.Polynomial.Dense.Rational.Sign.Endpoint

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational

/-- Positive squared radius which fixes the sign of one coordinate relative
to a displayed endpoint, unless that endpoint coordinate is exactly zero.

An exact zero endpoint value uses the original constant one. Otherwise
its squared value is divided by one plus the retained root-interval
Lipschitz coefficient, without replacing either original input. -/
@[expose] public def endpointStabilityRadiusSq
    (p : Dense.Rational.Basic.CoordinatePolynomial) (root : Data.Rat.Interval.Bounds) (endpoint : Fraction.Rational) :
      Fraction.Rational :=
  if p.eval endpoint = 0 then 1
  else p.eval endpoint ^ 2 /
    (Bounds.Lipschitz.denseEvalSqLipschitzBound p root + 1)

/-- The coefficient-computed endpoint stability radius is strictly positive.

In the nonzero branch, the endpoint square is positive and the
coefficient is nonnegative. Adding the original constant one makes
its displayed denominator positive; the zero branch retains one. -/
public theorem endpointStabilityRadiusSq_pos
    (p : Dense.Rational.Basic.CoordinatePolynomial) (root : Data.Rat.Interval.Bounds) (endpoint : Fraction.Rational) :
    0 < endpointStabilityRadiusSq p root endpoint := by
  unfold endpointStabilityRadiusSq
  split
  · decide
  · rename_i nonzero
    apply Fraction.Order.Field.div_pos_direct
    · exact Fraction.Order.Arithmetic.exact_rational_sq_pos nonzero
    · calc
        0 < 1 := by decide
        _ ≤ Bounds.Lipschitz.denseEvalSqLipschitzBound p root + 1 :=
          add_le_add (Bounds.Lipschitz.denseHornerSqBounds_nonneg p root).2 (le_refl 1)

/-- Construct a strict sign certificate from a displayed nonzero endpoint and its squared radius bound.

The displayed endpoint is retained as the certificate sample. Its
original membership and shared endpoint radius combine with the same
root Lipschitz bound to certify its strict local margin. -/
@[expose] public def endpointSignCertificateOfRadiusSq
    {p : Dense.Rational.Basic.CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds} {endpoint :
      Fraction.Rational}
    (refines : interval.Refines root)
    (atEndpoint : endpoint = interval.lower ∨ endpoint = interval.upper)
    (nonzero : p.eval endpoint ≠ 0)
    (radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      endpointStabilityRadiusSq p root endpoint) :
    Sign.Interval.Basic.Certificate p interval := by
  have endpointInside : interval.Contains endpoint := by
    rcases atEndpoint with rfl | rfl
    · exact ⟨le_rfl, interval.valid⟩
    · exact ⟨interval.valid, le_rfl⟩
  have endpointRadius : Interval.Radius.sampleRadiusSq interval endpoint =
      Interval.Radius.sampleRadiusSq interval interval.lower := by
    rcases atEndpoint with rfl | rfl
    · rfl
    · exact Interval.Radius.sampleRadiusSq_upper_eq_lower interval
  have rootCoefficientNonnegative :
      0 ≤ Bounds.Lipschitz.denseEvalSqLipschitzBound p root :=
    (Bounds.Lipschitz.denseHornerSqBounds_nonneg p root).2
  have localCoefficientLe :
      Bounds.Lipschitz.denseEvalSqLipschitzBound p interval ≤
        Bounds.Lipschitz.denseEvalSqLipschitzBound p root :=
    Bounds.Lipschitz.denseEvalSqLipschitzBound_le_of_refines p refines
  have radiusNonnegative :
      0 ≤ Interval.Radius.sampleRadiusSq interval endpoint :=
    (Fraction.Order.Arithmetic.sq_nonneg_direct
      (interval.lower - endpoint)).trans (Fraction.Order.Basic.le_max_left _ _)
  have radiusBelow : Interval.Radius.sampleRadiusSq interval endpoint <
      p.eval endpoint ^ 2 /
        (Bounds.Lipschitz.denseEvalSqLipschitzBound p root + 1) := by
    rw [endpointRadius]
    simpa only [endpointStabilityRadiusSq, if_neg nonzero] using radius
  have rootMargin : Bounds.Lipschitz.denseEvalSqLipschitzBound p root *
      Interval.Radius.sampleRadiusSq interval endpoint < p.eval endpoint ^ 2 :=
    Data.Rat.Bounds.Scale.coefficient_mul_lt_of_radius_lt_div_add_one
      rootCoefficientNonnegative radiusNonnegative radiusBelow
  exact
    { sample := endpoint
      sampleInside := endpointInside
      margin :=
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          localCoefficientLe radiusNonnegative).trans_lt rootMargin }

/-- The oriented endpoint values have either a zero start or a strictly positive product.

A zero starting value is permitted explicitly. Otherwise the positive
product retains agreement of the original starting and stopping
coordinate signs without selecting a new sample. -/
@[expose] public def EndpointStable (p : Dense.Rational.Basic.CoordinatePolynomial) (start stop : Fraction.Rational) :
  Prop
  :=
  p.eval start = 0 ∨ 0 < p.eval start * p.eval stop

/-- A sufficiently small refined interval preserves the starting endpoint sign.

Either the starting value is zero or the two endpoint values have positive product; either orientation of the retained
interval is allowed. -/
public theorem endpointStable_of_refined_radiusSq
    {p : Dense.Rational.Basic.CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds} {start stop :
      Fraction.Rational}
    (refines : interval.Refines root)
    (orientation :
      (start = interval.lower ∧ stop = interval.upper) ∨
      (start = interval.upper ∧ stop = interval.lower))
    (radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      endpointStabilityRadiusSq p root start) :
    EndpointStable p start stop := by
  by_cases zero : p.eval start = 0
  · exact Or.inl zero
  · have atEndpoint : start = interval.lower ∨
        start = interval.upper := orientation.elim
          (fun ordered => Or.inl ordered.1)
          (fun reversed => Or.inr reversed.1)
    let certificate := endpointSignCertificateOfRadiusSq
      refines atEndpoint zero radius
    apply Or.inr
    rcases orientation with ordered | reversed
    · rw [ordered.1, ordered.2]
      exact certificate.endpoint_stable
    · rw [reversed.1, reversed.2]
      rw [Fraction.Field.mul_comm]
      exact certificate.endpoint_stable

end Purelib.Polynomial.Dense.Rational.Sign.Endpoint
