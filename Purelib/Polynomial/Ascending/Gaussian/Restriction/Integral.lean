module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Basic
public import Purelib.Polynomial.Ascending.Gaussian.Integral

import Purelib.Polynomial.Ascending.Gaussian.Affine
import Purelib.Polynomial.Ascending.Gaussian.Affine.Integral
public import Purelib.Polynomial.Ascending.Gaussian.Restriction.Basic
import Purelib.Tactic.Ring

import Purelib.Algebra.Ring.Multiplication

/-!
# Exact integrals of Gaussian polynomial restrictions

Affine unit-parameter substitution transports a retained polynomial interval
by its original endpoint displacement. The exact finite identities include
repeated and reversed endpoints without analytic change-of-variables assumptions.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Restriction.Integral

open Purelib.Data
open Purelib.Polynomial
open Purelib.Algebra

public section
open Purelib.Data.Gaussian.Basic.Canonical

/-- Transport the exact unit-parameter integral by its retained endpoint displacement.

Affine substitution maps zero and one to the supplied source endpoints.
Multiplication by their displacement accounts for orientation exactly once,
including coincident endpoints, without dividing by that displacement. -/
theorem definiteIntegral_restrict (polynomial : CoefficientPolynomial) (start finish :
  Gaussian.Basic.Canonical) :
    (finish - start) * Ascending.Gaussian.Integral.definiteIntegral (Ascending.Gaussian.Restriction.Basic.restrict
      polynomial start finish) 0 1 =
      Ascending.Gaussian.Integral.definiteIntegral polynomial start finish := by
  have transported := Ascending.Gaussian.Affine.Integral.definiteIntegral_affine polynomial start (finish - start) 0 1
  have leftEndpoint : start + (finish - start) * 0 = start := by ring1
  have rightEndpoint : start + (finish - start) * 1 = finish := by ring1
  rw [leftEndpoint, rightEndpoint] at transported
  exact transported

/-- Reversing the unit parameter leaves its exact polynomial integral unchanged.

The reversed endpoint displacement supplies the sign of the oriented source
integral. Negation cancellation transports the finite endpoint-evaluation identity. -/
theorem definiteIntegral_reverse_parameter (polynomial : CoefficientPolynomial) :
    Ascending.Gaussian.Integral.definiteIntegral (Ascending.Gaussian.Restriction.Basic.reverse polynomial) 0 1 =
      Ascending.Gaussian.Integral.definiteIntegral polynomial 0 1 := by
  have transported := definiteIntegral_restrict polynomial 1 0
  rw [Ascending.Gaussian.Integral.definiteIntegral_reverse polynomial 0 1] at transported
  change (0 - 1 : Gaussian.Basic.Canonical) * Ascending.Gaussian.Integral.definiteIntegral
    (Ascending.Gaussian.Restriction.Basic.reverse polynomial) 0 1 =
    -Ascending.Gaussian.Integral.definiteIntegral polynomial 0 1 at transported
  have negative : (0 - 1 : Gaussian.Basic.Canonical) = -1 := by ring1
  rw [negative, Ring.Multiplication.neg_mul, _root_.one_mul] at transported
  exact neg_inj.mp transported

end

end Purelib.Polynomial.Ascending.Gaussian.Restriction.Integral
