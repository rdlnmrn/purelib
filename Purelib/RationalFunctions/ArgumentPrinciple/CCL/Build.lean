module
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic
import Purelib.RationalFunctions.ArgumentPrinciple.General
import Purelib.RootIsolation.Multiplicity.Side.CCL.Basic

section
@[expose] public section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace Purelib.RationalFunctions.ArgumentPrinciple.CCL.Build

open Purelib.Polynomial in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
/-- Compute the finite rational-function result once and attach CCL observations to its retained sites.

Preserve the explicit zero-numerator outcome. For a nonzero result, construct the numerator and denominator CCL families
using the exact side results returned by that computation. -/
def prove
    (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false) :
    ArgumentPrinciple.CCL.Basic.Result numerator denominator := by
  match ArgumentPrinciple.General.prove numerator denominator denominatorNonzero with
  | .zeroNumerator numeratorZero denominatorNonzero =>
      exact .zeroNumerator numeratorZero denominatorNonzero
  | .nonzero rfap =>
      exact .nonzero
        { rfap := rfap
          numeratorCCL := Multiplicity.Side.CCL.Basic.sideCCL rfap.numeratorSites
          denominatorCCL := Multiplicity.Side.CCL.Basic.sideCCL rfap.denominatorSites }

end Purelib.RationalFunctions.ArgumentPrinciple.CCL.Build

end
