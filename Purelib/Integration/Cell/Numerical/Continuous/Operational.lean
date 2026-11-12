module
public import Purelib.Integration.Cell.Numerical.Continuous
public import Purelib.Integration.Cell.Numerical.Common.Operational
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Operational replacement of numerical integration sources

Two original numerical source families are compared through their actual
common partition and a finite operational scheduler at each rational tag.
Both result owners and all joint point observations remain retained.
-/

public section

namespace Purelib.Integration.NumericalFrontier.Continuous.Result

open Purelib.Approximation
open Purelib.Data.Rat

/-- Execute point-equivalence schedulers on the two actual independent source frontiers.

Both source moduli supply finite point coherence on the unit interval. The
result retains the original common partition, each pair of point histories,
the selected operational certificates and all returned joint states. -/
@[expose] def jointComparison {leftSource rightSource : Fraction.Rational → BoundProcess}
    {leftModulus : Rational.Uniform.Numerical leftSource} {rightModulus : Rational.Uniform.Numerical rightSource}
    (left : Result leftModulus) (right : Result rightModulus) (pointRequest jointRequest : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point)) :
    JointReadings (NumericalFrontier.commonReadings left.frontier right.frontier pointRequest) jointRequest :=
  NumericalFrontier.requestJointReadings (NumericalFrontier.commonReadings left.frontier right.frontier pointRequest)
    jointRequest equivalent (fun point lower upper => leftModulus.coherent point lower upper)
    (fun point lower upper => rightModulus.coherent point lower upper)

/-- Operationally equivalent numerical sources produce quantitatively agreeing integration answers.

The bound uses the two original integration requests, both point-request
allowances and the joint-scheduler allowance. It is derived from the actual
retained common observations, rather than assuming an integral equality. -/
theorem answer_difference_le_of_operational {leftSource rightSource : Fraction.Rational → BoundProcess}
    {leftModulus : Rational.Uniform.Numerical leftSource} {rightModulus : Rational.Uniform.Numerical rightSource}
    (left : Result leftModulus) (right : Result rightModulus) (pointRequest jointRequest : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point)) :
    Fraction.abs (left.answer - right.answer) ≤
      left.preparation.request.tolerance + right.preparation.request.tolerance +
        (pointRequest.tolerance + pointRequest.tolerance + jointRequest.tolerance) := by
  let joint := left.jointComparison right pointRequest jointRequest equivalent
  have comparison := joint.answers_difference_le left.answer right.answer left.answer_contains right.answer_contains
  have widths := Fraction.Order.Arithmetic.add_le_add_direct left.accurate.le right.accurate.le
  have paid := Fraction.Order.Arithmetic.add_le_add_direct widths
    (Fraction.Order.Basic.le_refl (pointRequest.tolerance + pointRequest.tolerance + jointRequest.tolerance))
  exact comparison.trans paid

end Purelib.Integration.NumericalFrontier.Continuous.Result

end
