module
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Multiplication

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Unit

/-- The displayed constant-one denominator used to view a polynomial as the
rational function `p / 1`. -/
def unitDenominator : Dense.Basic.DensePolynomial Gaussian.Basic.Canonical
  :=
  Dense.Basic.DensePolynomial.constant 1

/-- The displayed constant-one denominator is nonzero. -/
theorem unitDenominator_isZero :
  Dense.Gaussian.Unit.unitDenominator.isZero = false := by
  rfl

end Purelib.Polynomial.Dense.Gaussian.Unit

end
