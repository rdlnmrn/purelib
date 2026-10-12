module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Exponential.Taylor.Integral
import Purelib.Polynomial.Ascending.Gaussian.Integral
public import Purelib.Polynomial.Ascending.Gaussian.Restriction.Basic
import Purelib.Polynomial.Ascending.Gaussian.Restriction.Integral

open Purelib

open Purelib.Approximation.Gaussian.Exponential.Taylor

open Purelib.Polynomial.Ascending.Gaussian

open Purelib.Polynomial.Ascending.Gaussian.Restriction

section
@[expose] public section

/-!
# Exact integration and finite reading bounds for exponential polynomials

`polynomial n` has degree `n+1`, matching the existing finite Horner sample
at index `n`.  Its integral has the next sample index.  All statements concern
displayed coefficient lists and rational points, not a completed exponential.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Taylor.Integral.Restriction

/-- Transport to a displayed subinterval uses the generated affine restriction and exactly one geometric Jacobian. -/
theorem restricted_integral (index : Nat)
  (start finish : Data.Gaussian.Basic.Canonical) :
    (finish - start) * Integral.definiteIntegral (Restriction.Basic.restrict (Integral.polynomial index) start finish) 0
      1 =
      Integral.definiteIntegral (Integral.polynomial index) start finish :=
  Integral.definiteIntegral_restrict _ start finish

end Purelib.Approximation.Gaussian.Exponential.Taylor.Integral.Restriction

end
