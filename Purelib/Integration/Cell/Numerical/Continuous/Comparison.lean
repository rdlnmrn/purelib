module
public import Purelib.Integration.Cell.Numerical.Continuous
public import Purelib.Integration.Cell.Numerical.Common.Weights
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Comparison of independent numerical integration requests

The actual common refinement retains both original point-state histories.
Its discrepancy budget is computed from the selected witnesses and bounded
using the original point-process coherence and point-width request.
-/

public section

namespace Purelib.Integration.NumericalFrontier.Continuous.Result

open Purelib.Approximation
open Purelib.Data.Rat

/-- Independently produced answers agree within both requests and the point-request budget.

The original moduli may differ while referring to the same numerical point
process family. A computed common refinement retains both source frontiers,
their actual requests and their length-weighted point discrepancy. -/
theorem answer_difference_le {source : Fraction.Rational → BoundProcess}
    {leftModulus rightModulus : Rational.Uniform.Numerical source}
    (left : Result leftModulus) (right : Result rightModulus) (pointRequest : AccuracyRequest) :
    Fraction.abs (left.answer - right.answer) ≤
      left.preparation.request.tolerance + right.preparation.request.tolerance +
        (pointRequest.tolerance + pointRequest.tolerance) := by
  let common := NumericalFrontier.commonReadings left.frontier right.frontier pointRequest
  have comparison := common.answers_difference_le left.answer right.answer left.answer_contains right.answer_contains
  have pointBound := common.pointBudget_le (fun point lower upper => leftModulus.coherent point lower upper)
  have widths := Fraction.Order.Arithmetic.add_le_add_direct left.accurate.le right.accurate.le
  have paid := Fraction.Order.Arithmetic.add_le_add_direct widths pointBound
  exact comparison.trans paid

end Purelib.Integration.NumericalFrontier.Continuous.Result

end
