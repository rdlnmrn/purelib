module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Unit
public import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Build
public import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Basic

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

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

namespace Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Build

/-- Compute every distinct root site of `p`, its multiplicity, and its
productive CCL interface by running the finite RFAP construction on `p / 1`. -/
def isolate (p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
    Multiplicity.CCL.Polynomial.Basic.Result p :=
  ArgumentPrinciple.CCL.Build.prove p Dense.Gaussian.Unit.unitDenominator Dense.Gaussian.Unit.unitDenominator_isZero

end Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Build

end
