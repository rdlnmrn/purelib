module
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic
import Purelib.RationalFunctions.ArgumentPrinciple.General
import Purelib.RootIsolation.Multiplicity.Side.CCL.Basic

open Purelib.Data.Rat.Fraction (Rational)

section
public section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace Purelib.RationalFunctions.ArgumentPrinciple.CCL.Build

open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RationalFunctions
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

/-- Attach CCL observations to the same retained original rational-function site result.

The zero-numerator branch remains explicit. A nonzero result keeps the actual
reduction and both original multiplicity families; their CCL observations are
indexed by those same retained sides, without another isolation computation.
-/
@[expose] def fromResult {numerator denominator : CoefficientPolynomial} :
    ArgumentPrinciple.General.Result numerator denominator → ArgumentPrinciple.CCL.Basic.Result numerator denominator
  | .zeroNumerator numeratorZero denominatorNonzero => .zeroNumerator numeratorZero denominatorNonzero
  | .nonzero rfap =>
      .nonzero
        { rfap := rfap
          numeratorCCL := Multiplicity.Side.CCL.Basic.sideCCL rfap.numeratorSites
          denominatorCCL := Multiplicity.Side.CCL.Basic.sideCCL rfap.denominatorSites }

/-- Compute the finite rational-function result once and attach CCL observations to its retained sites. -/
@[expose] def prove (numerator denominator : CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false) (request : Option Rational := none) :
    ArgumentPrinciple.CCL.Basic.Result numerator denominator :=
  fromResult (ArgumentPrinciple.General.prove numerator denominator denominatorNonzero request)

/-- A complete original site-result readback preserves the complete original CCL result. -/
theorem fromResult_eq_prove (numerator denominator : CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (result : ArgumentPrinciple.General.Result numerator denominator)
    {request : Option Rational}
    (same : result = ArgumentPrinciple.General.prove numerator denominator denominatorNonzero request) :
    fromResult result = prove numerator denominator denominatorNonzero request :=
  congrArg fromResult same

/-- The absent event request preserves the complete original rational-function result and CCL attachments. -/
theorem prove_none (numerator denominator : CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false) :
    prove numerator denominator denominatorNonzero none =
      fromResult (ArgumentPrinciple.General.prove numerator denominator denominatorNonzero) := rfl

end Purelib.RationalFunctions.ArgumentPrinciple.CCL.Build

namespace Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic.Result

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation

/-- Exact original Newton origins together with the original complete CCL attachment constructors.

The attachment equalities preserve the actual retained numerical boxes and
all dependent context indices. Numerical origin alone would not identify an
independently supplied CCL adapter on the same polynomial.
-/
@[expose] def NewtonOrigins {numerator denominator : CoefficientPolynomial} : Result numerator denominator → Prop
  | .zeroNumerator _ _ => True
  | .nonzero result =>
      (ArgumentPrinciple.General.Result.nonzero result.rfap).NewtonOrigins ∧
        result.numeratorCCL = Multiplicity.Side.CCL.Basic.sideCCL result.rfap.numeratorSites ∧
          result.denominatorCCL = Multiplicity.Side.CCL.Basic.sideCCL result.rfap.denominatorSites

end Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic.Result

namespace Purelib.RationalFunctions.ArgumentPrinciple.CCL.Build

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

/-- The original CCL constructor retains both same numerical track origins and the complete original attachment data. -/
theorem prove_newtonOrigins (numerator denominator : CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false) (request : Option Rational) :
    (prove numerator denominator denominatorNonzero request).NewtonOrigins := by
  have origin := ArgumentPrinciple.General.prove_newtonOrigins numerator denominator denominatorNonzero request
  unfold prove
  cases computed : ArgumentPrinciple.General.prove numerator denominator denominatorNonzero request with
  | zeroNumerator => exact True.intro
  | nonzero result =>
      rewrite [computed] at origin
      exact ⟨origin, rfl, rfl⟩

end Purelib.RationalFunctions.ArgumentPrinciple.CCL.Build

end
