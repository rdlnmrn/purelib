module

public import Purelib.Data.Rat.Interval.Radius
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached polynomial pair sample bounds

A lower-endpoint Gaussian observation and two finite Lipschitz bounds determine a proposed quadrance floor. The sample,
variation budget and radius remain cached for the same polynomial pair and interval.
-/

namespace Purelib.Polynomial.Clearance.Pair.Sample

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial

set_option genInjectivity false in
/-- Cached sample-and-variation data for two rational polynomials on an interval.

The lower-endpoint sample, combined squared Lipschitz bound, squared radius and proposed quadrance floor retain their
exact construction equalities. A nonpositive floor supplies no positive clearance. -/
public structure Certificate (realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial)
  (parameters : Data.Rat.Interval.Bounds) where
  /-- The retained Gaussian value of the pair at the lower endpoint. -/ sample : Gaussian.Basic.Canonical
  /-- The sample contains exactly the two lower-endpoint evaluations. -/ sample_eq : sample = ⟨realPolynomial.eval
    parameters.lower, imagPolynomial.eval parameters.lower⟩
  /-- The retained combined squared Lipschitz coefficient. -/ slopeBound : Fraction.Rational
  /-- The slope bound is the sum of both polynomial Lipschitz bounds. -/ slopeBound_eq : slopeBound =
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound realPolynomial parameters +
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound imagPolynomial parameters
  /-- The retained squared parameter radius about the lower endpoint. -/ radiusSq : Fraction.Rational
  /-- The radius is exactly the interval's lower-endpoint sample radius. -/ radiusSq_eq : radiusSq =
    Data.Rat.Interval.Radius.sampleRadiusSq parameters parameters.lower
  /-- The proposed uniform lower bound on pair evaluation quadrance. -/ normFloor : Fraction.Rational
  /-- The floor is half the sample quadrance minus the bounded variation. -/ normFloor_eq : normFloor =
    Data.Gaussian.Norm.Basic.normSq sample / 2 - slopeBound * radiusSq

constructive_injectivity Certificate

/-- Compute the lower-endpoint sample and retain its variation-based quadrance floor.

The initial leaf is constructed for the supplied source and interval. Refinement then consumes the fixed depth budget
and retains its actual certificate tree. -/
@[expose] public def prepare (realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial)
  (parameters : Data.Rat.Interval.Bounds) :
    Clearance.Pair.Sample.Certificate realPolynomial imagPolynomial parameters :=
  let sample : Gaussian.Basic.Canonical := ⟨realPolynomial.eval parameters.lower, imagPolynomial.eval parameters.lower⟩
  let slopeBound := Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound realPolynomial parameters +
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound imagPolynomial parameters
  let radiusSq := Data.Rat.Interval.Radius.sampleRadiusSq parameters parameters.lower
  { sample, sample_eq := rfl, slopeBound, slopeBound_eq := rfl, radiusSq, radiusSq_eq := rfl
    normFloor := Data.Gaussian.Norm.Basic.normSq sample / 2 - slopeBound * radiusSq, normFloor_eq := rfl }

namespace Certificate

variable {realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial} {parameters :
  Data.Rat.Interval.Bounds}

/-- The combined squared Lipschitz bound is nonnegative.

Both finite squared-Lipschitz bounds are nonnegative. The retained combined slope is their exact sum. -/
public theorem slopeBound_nonnegative (certificate : Clearance.Pair.Sample.Certificate realPolynomial imagPolynomial
  parameters) :
    0 ≤ certificate.slopeBound := by
  rw [certificate.slopeBound_eq]
  exact add_nonneg (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg _ _).2
    (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg _ _).2

/-- The cached sample-and-variation floor bounds pair evaluation quadrance throughout the interval.

The enclosure or sample certificates bound the same two polynomial values on the supplied interval. The retained floor
readback combines those bounds without changing either coordinate. -/
public theorem normFloor_le (certificate : Clearance.Pair.Sample.Certificate realPolynomial imagPolynomial parameters)
    {parameter : Fraction.Rational} (inside : parameters.Contains parameter) :
    certificate.normFloor ≤ realPolynomial.eval parameter ^ 2 + imagPolynomial.eval parameter ^ 2 := by
  let value : Gaussian.Basic.Canonical := ⟨realPolynomial.eval parameter, imagPolynomial.eval parameter⟩
  have startInside : parameters.Contains parameters.lower := ⟨le_rfl, parameters.valid⟩
  have difference : Data.Gaussian.Norm.Basic.normSq (certificate.sample - value) ≤
      certificate.slopeBound * (parameters.lower - parameter) ^ 2 := by
    rw [certificate.sample_eq, certificate.slopeBound_eq]
    have bound := add_le_add
      (Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le realPolynomial parameters startInside inside)
      (Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le imagPolynomial parameters startInside inside)
    calc
      _ ≤ _ := bound
      _ = _ := by ring1
  have radius : (parameters.lower - parameter) ^ 2 ≤ certificate.radiusSq := by
    rw [certificate.radiusSq_eq]
    calc
      _ = (parameter - parameters.lower) ^ 2 := by ring1
      _ ≤ _ := Data.Rat.Interval.Radius.sub_sq_le_sampleRadiusSq parameters inside
  have movement := difference.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radius certificate.slopeBound_nonnegative)
  have lower := Gaussian.Norm.Bounds.half_normSq_sub_le_normSq_sub certificate.sample (certificate.sample - value)
  have cancel : certificate.sample - (certificate.sample - value) = value := by ring1
  rw [cancel] at lower
  rw [certificate.normFloor_eq]
  exact (Fraction.Order.Arithmetic.sub_le_sub_left_direct movement _).trans lower

end Certificate

/-- Read a retained sample floor, using zero when no sample certificate is supplied.

An absent certificate reads zero. A present certificate projects its retained quadrance floor, without rebuilding its
source or cached observations. -/
@[expose] public def optionalNorm {realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial}
  {parameters : Data.Rat.Interval.Bounds} :
    Option (Clearance.Pair.Sample.Certificate realPolynomial imagPolynomial parameters) → Fraction.Rational
  | none => 0
  | some certificate => certificate.normFloor

/-- The optional sample floor bounds pair evaluation quadrance even when the certificate is absent.

Zero is bounded by the two nonnegative coordinate squares when no certificate is supplied. A present result transports
its retained uniform quadrance bound. -/
public theorem optionalNorm_le {realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial}
  {parameters : Data.Rat.Interval.Bounds}
    (certificate : Option (Clearance.Pair.Sample.Certificate realPolynomial imagPolynomial parameters))
    {parameter : Fraction.Rational} (inside : parameters.Contains parameter) :
    Clearance.Pair.Sample.optionalNorm certificate ≤ realPolynomial.eval parameter ^ 2 + imagPolynomial.eval parameter ^
      2 := by
  cases certificate with
  | none =>
    exact add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct _) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  | some certificate => exact certificate.normFloor_le inside

end Purelib.Polynomial.Clearance.Pair.Sample
