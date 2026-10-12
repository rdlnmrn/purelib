module
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Unit
public import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic

open Purelib.Polynomial

open Purelib.RationalFunctions

section
public section

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

namespace Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Basic

/-- The nonzero-polynomial branch of the root-stream construction. -/
abbrev NonzeroResult (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :=
  ArgumentPrinciple.CCL.Basic.NonzeroResult p Dense.Gaussian.Unit.unitDenominator

/-- Total result.  The zero polynomial remains an explicit outcome because it
does not have a finite list of isolated root sites. -/
abbrev Result (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :=
  ArgumentPrinciple.CCL.Basic.Result p Dense.Gaussian.Unit.unitDenominator

end Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Basic

end
