module
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic
import Purelib.RationalFunctions.Winding.Box.Basic

section
@[expose] public section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic
namespace NonzeroResult

open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- The retained CCL result has outer box winding equal to the reduced numerator degree minus denominator degree. -/
theorem outerBoxWinding
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : ArgumentPrinciple.CCL.Basic.NonzeroResult numerator denominator) :
    Winding.Box.Basic.rationalBoxWinding
        result.rfap.input.reduction.numeratorReduced
        result.rfap.input.reduction.denominatorReduced
        result.rfap.input.outerBox =
      (result.rfap.input.reduction.numeratorReduced.natDegree : Int) -
        result.rfap.input.reduction.denominatorReduced.natDegree :=
  result.rfap.outerBoxWinding
end NonzeroResult
end Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic

end
