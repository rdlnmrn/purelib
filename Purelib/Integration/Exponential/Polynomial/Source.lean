module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
public import Purelib.Approximation.Gaussian.Exponential.Taylor.Integral
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Polynomial.Ascending.Gaussian.Integral
public import Purelib.Integration.Polynomial.Gaussian.Segment.Basic
import Purelib.Tactic.Ring

/-!
# Retained finite exponential selection and observations

The original ordered geometry, positive-stride requests and polynomial depth
remain attached to their cached values and exact scalar readback certificates.
-/

public section
namespace Purelib.Integration.Exponential.Polynomial.Source

open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Polynomial
open Purelib.Polynomial

/-- The unit segment equipped with the retained finite Taylor polynomial at the supplied depth.

The source endpoints are zero and one. Its stored polynomial is the finite Taylor polynomial at the supplied depth. -/
@[expose] def source (depth : Nat) : Gaussian.Segment.Basic.PolynomialSegment :=
  ⟨0, 1, Exponential.Taylor.Integral.polynomial depth⟩

/-- The Taylor source segment's affine point is the exact Gaussian embedding of its rational parameter.

The unit source displacement is one, so its rational affine parameter reads back to the same Gaussian scalar embedding.
-/
theorem source_point (depth : Nat) (value : Fraction.Rational) :
    (source depth).point value = RationalEmbedding.parameter value := by
  change 0 + (1 - 0 : Basic.Canonical) * RationalEmbedding.parameter value = RationalEmbedding.parameter value
  ring1

/-- The Taylor source integral is the next-depth Horner sample at one minus one.

The exact finite Taylor polynomial supplies the integral readback; the retained unit source displacement leaves that
scalar sample unchanged. -/
theorem source_integral (depth : Nat) :
    (source depth).integralSample = Exponential.Horner.Sample.sample 1 (depth + 1) - 1 :=
      by
  change (1 - 0 : Basic.Canonical) *
    Ascending.Gaussian.Integral.definiteIntegral (Exponential.Taylor.Integral.polynomial depth)
      0 1 = _
  have unitDisplacement : (1 - 0 : Basic.Canonical) = 1 := by ring1
  rw [unitDisplacement, _root_.one_mul, Exponential.Taylor.Integral.integral_polynomial]

end Purelib.Integration.Exponential.Polynomial.Source
end
