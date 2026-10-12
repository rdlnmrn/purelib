module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Sign.Basic
public import Purelib.Data.Rat.Sign.Jump
public import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic
import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Data.Rat.Interval.Radius
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Signed Euclidean steps on rational intervals

The retained polynomial inputs and interval bounds determine the certificate
indices. Each certificate retains its actual samples, signed chains and branch evidence.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step

open Purelib
open Purelib.Polynomial
open Purelib.Data.Rat

@[expose] public section

set_option genInjectivity false in
/-- One locally resolved signed Euclidean step.

The sample and both squared margins certify the first member and the
negated division remainder. Their negative sampled product fixes opposite
outer signs while retaining the displayed division inputs. -/
structure SignedStepCellCertificate
    (p q : Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) where
  /-- The common rational sample for the two outer chain members. -/ sample : Fraction.Rational
  /-- The common sample lies in the certified interval. -/ sampleInside : interval.Contains sample
  /-- The first polynomial has a strict squared sign margin at the sample. -/ leftMargin :
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p interval *
      Data.Rat.Interval.Radius.sampleRadiusSq interval sample < p.eval sample ^ 2
  /-- The negated division remainder has a strict squared sign margin at the sample. -/ rightMargin :
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound (-((Dense.Basic.DensePolynomial.divMod p q).remainder))
      interval *
        Data.Rat.Interval.Radius.sampleRadiusSq interval sample <
      (-((Dense.Basic.DensePolynomial.divMod p q).remainder)).eval sample ^ 2
  /-- The two outer polynomial values have opposite strict signs at the sample. -/ outerOpposite :
    p.eval sample * (-((Dense.Basic.DensePolynomial.divMod p q).remainder)).eval sample < 0

constructive_injectivity SignedStepCellCertificate

end

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step.SignedStepCellCertificate

open Purelib
open Purelib.Polynomial
open Purelib.Data.Rat

/-- Extract the retained strict-sign certificate for the first polynomial.

The extracted certificate retains the same sample, interval membership
and left margin from the signed-step certificate. -/
@[expose] public def leftCertificate {p q : Dense.Rational.Basic.CoordinatePolynomial} {interval :
  Data.Rat.Interval.Bounds}
    (certificate : Dense.Rational.SignedRemainder.Signs.Step.SignedStepCellCertificate p q interval) :
    Dense.Rational.Sign.Interval.Basic.Certificate p interval where
  sample := certificate.sample
  sampleInside := certificate.sampleInside
  margin := certificate.leftMargin

/-- Extract the retained strict-sign certificate for the negated division remainder.

The extracted certificate retains the same sample, interval membership
and right margin for the exact negated remainder of the displayed division. -/
@[expose] public def rightCertificate {p q : Dense.Rational.Basic.CoordinatePolynomial} {interval :
  Data.Rat.Interval.Bounds}
    (certificate : Dense.Rational.SignedRemainder.Signs.Step.SignedStepCellCertificate p q interval) :
    Dense.Rational.Sign.Interval.Basic.Certificate (-((Dense.Basic.DensePolynomial.divMod p q).remainder)) interval
      where
  sample := certificate.sample
  sampleInside := certificate.sampleInside
  margin := certificate.rightMargin

/-- The two outer chain values have opposite signs throughout the interval.

Their individual strict-sign certificates transport the sampled negative product to every interval point. -/
public theorem outer_mul_neg {p q : Dense.Rational.Basic.CoordinatePolynomial} {interval :
  Data.Rat.Interval.Bounds}
    (certificate : Dense.Rational.SignedRemainder.Signs.Step.SignedStepCellCertificate p q interval)
    {t : Fraction.Rational} (inside : interval.Contains t) :
    p.eval t * (-((Dense.Basic.DensePolynomial.divMod p q).remainder)).eval t < 0 := by
  have leftStable := certificate.leftCertificate.eval_mul_sample_pos inside
  have rightStable := certificate.rightCertificate.eval_mul_sample_pos inside
  change 0 < p.eval t * p.eval certificate.sample at leftStable
  change 0 < (-((Dense.Basic.DensePolynomial.divMod p q).remainder)).eval t *
    (-((Dense.Basic.DensePolynomial.divMod p q).remainder)).eval certificate.sample at rightStable
  apply Data.Rat.Sign.Basic.sign_eq_neg_one_iff.mp
  rw [Data.Rat.Sign.Basic.sign_mul, Data.Rat.Sign.Basic.sign_eq_of_mul_pos leftStable,
    Data.Rat.Sign.Basic.sign_eq_of_mul_pos rightStable, ← Data.Rat.Sign.Basic.sign_mul,
    Data.Rat.Sign.Basic.sign_of_neg certificate.outerOpposite]

/-- The two adjacent sign jumps in the signed step sum to two.

Opposite outer signs make this sum independent of the middle polynomial value, even when that value is zero. -/
public theorem local_jump_sum {p q : Dense.Rational.Basic.CoordinatePolynomial} {interval :
  Data.Rat.Interval.Bounds}
    (certificate : Dense.Rational.SignedRemainder.Signs.Step.SignedStepCellCertificate p q interval)
    {t : Fraction.Rational} (inside : interval.Contains t) :
    Data.Rat.Sign.Jump.signJump (p.eval t) (q.eval t) +
        Data.Rat.Sign.Jump.signJump (q.eval t) ((-((Dense.Basic.DensePolynomial.divMod p q).remainder)).eval t) = 2 :=
  Data.Rat.Sign.Jump.signJump_add_signJump_of_outer_mul_neg
    (certificate.outer_mul_neg inside)

/-- The total jump across the signed triple agrees at the two interval endpoints.

The two outer members have opposite signs throughout the interval. Each
endpoint therefore has the same total of the two adjacent sign jumps. -/
public theorem endpoint_cancellation {p q : Dense.Rational.Basic.CoordinatePolynomial} {interval :
  Data.Rat.Interval.Bounds}
    (certificate : Dense.Rational.SignedRemainder.Signs.Step.SignedStepCellCertificate p q interval) :
    Data.Rat.Sign.Jump.signJump (p.eval interval.lower) (q.eval interval.lower) +
        Data.Rat.Sign.Jump.signJump (q.eval interval.lower)
          ((-((Dense.Basic.DensePolynomial.divMod p q).remainder)).eval interval.lower) =
      Data.Rat.Sign.Jump.signJump (p.eval interval.upper) (q.eval interval.upper) +
        Data.Rat.Sign.Jump.signJump (q.eval interval.upper)
          ((-((Dense.Basic.DensePolynomial.divMod p q).remainder)).eval interval.upper) := by
  rw [certificate.local_jump_sum ⟨le_rfl, interval.valid⟩,
    certificate.local_jump_sum ⟨interval.valid, le_rfl⟩]

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step.SignedStepCellCertificate
