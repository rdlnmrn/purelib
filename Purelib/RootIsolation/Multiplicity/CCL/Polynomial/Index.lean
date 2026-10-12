module
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Basic
import Purelib.RootIsolation.Multiplicity.Side.Index
public import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Index
import Purelib.Polynomial.Dense.Gaussian.Unit
import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic
import Purelib.RationalFunctions.ArgumentPrinciple.General
import Purelib.RationalFunctions.Reduction.Basic
import Purelib.RationalFunctions.Reduction.Nonzero

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

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

namespace Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Index
namespace NonzeroResult

/-- Finite dependent index of every exact root or higher root-approximation
track of a nonzero polynomial. -/
abbrev RootIndex {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
  Multiplicity.CCL.Polynomial.Basic.NonzeroResult p) :=
  (ArgumentPrinciple.CCL.Basic.NonzeroResult.ZeroIndex result)

/-- Displayed finite list of all root-site indices. -/
@[expose] def rootIndices {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
  Multiplicity.CCL.Polynomial.Basic.NonzeroResult p) :
    List (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result) :=
  Multiplicity.Side.Index.sideIndices result.rfap.numeratorSites

/-- Every root-site index occurs in the displayed finite index list. -/
theorem mem_rootIndices
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) : index ∈
      (Multiplicity.CCL.Polynomial.Index.NonzeroResult.rootIndices result) :=
  Multiplicity.Side.Index.mem_sideIndices
    result.rfap.numeratorSites index

/-- Algebraic multiplicity of one distinct exact or higher root site. -/
@[expose] def rootMultiplicity
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) : Nat :=
  Multiplicity.Side.Index.sideMultiplicity
    result.rfap.numeratorSites index
end NonzeroResult

end Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Index

end
