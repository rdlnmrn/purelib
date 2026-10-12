module
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic
public import Purelib.RootIsolation.Multiplicity.Side.Index

section
public section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic
namespace NonzeroResult

open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RationalFunctions
/-- Index every exact or shrinking-track zero site in the retained reduced numerator family. -/
@[expose] def ZeroIndex
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : ArgumentPrinciple.CCL.Basic.NonzeroResult numerator denominator) : Type :=
  Multiplicity.Side.Index.SideIndex result.rfap.numeratorSites

/-- Index every exact or shrinking-track pole site in the retained reduced denominator family. -/
@[expose] def PoleIndex
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : ArgumentPrinciple.CCL.Basic.NonzeroResult numerator denominator) : Type :=
  Multiplicity.Side.Index.SideIndex result.rfap.denominatorSites
end NonzeroResult
end Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic

end
