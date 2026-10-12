module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RationalFunctions.ArgumentPrinciple.General
public import Purelib.RootIsolation.Multiplicity.Side.CCL.Basic

section
public section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic

open Purelib.Polynomial in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
set_option genInjectivity false in
/-- A retained rational-function argument-principle result with CCL observations for both site families.

The original result owns all zero/pole sites, multiplicities, separation and winding evidence. Each added CCL family is
indexed by that exact retained side. -/
structure NonzeroResult
    (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The original finite rational-function argument-principle result. -/ rfap : ArgumentPrinciple.General.NonzeroResult
    numerator denominator
  /-- CCL observations indexed by the retained numerator zero-site family. -/ numeratorCCL :
    Multiplicity.Side.CCL.Basic.SideCCL rfap.numeratorSites
  /-- CCL observations indexed by the retained denominator pole-site family. -/ denominatorCCL :
    Multiplicity.Side.CCL.Basic.SideCCL rfap.denominatorSites

constructive_injectivity NonzeroResult

open Purelib.Polynomial in
set_option genInjectivity false in
/-- A total rational-function result with CCL observations on every nonzero outcome.

The zero-numerator case retains its explicit proof and denominator nonzeroness. A nonzero outcome retains the original
site result with its indexed CCL families. -/
inductive Result (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  where
  /-- Report an identically zero numerator with its denominator nonzeroness proof. -/ | zeroNumerator
      (numeratorZero : numerator.isZero = true)
      (denominatorNonzero : denominator.isZero = false)
  /-- Retain the nonzero argument-principle result and its indexed CCL observations. -/ | nonzero (result :
    Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic.NonzeroResult numerator denominator)

constructive_injectivity Result

end Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic

end
