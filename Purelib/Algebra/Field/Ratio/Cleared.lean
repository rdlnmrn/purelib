module
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Divine Proportions, Chapter 21: two-dimensional problems

The applications are separated into their finite metric identities and the
geometric incidence arguments that supply those identities.  Denominators are
always accompanied by explicit nonzero certificates.
-/

namespace Purelib.Algebra.Field.Ratio.Cleared

section TwoDimensionalProblems

variable {K : Type*} [ExplicitField K]

/-- Equal ratios with nonzero denominators have equal cross products.

Each denominator comes with its own nonzero certificate for cancelling the corresponding division. -/
public theorem cross_mul_of_div_eq_div
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (ratiosEqual :
      leftNumerator / leftDenominator =
        rightNumerator / rightDenominator) :
    leftNumerator * rightDenominator =
      rightNumerator * leftDenominator := by
  calc
    leftNumerator * rightDenominator =
        (leftNumerator / leftDenominator * leftDenominator) *
          rightDenominator := by
            rw [ExplicitField.div_mul_cancel leftNumerator leftNonzero]
    _ = (rightNumerator / rightDenominator * leftDenominator) *
        rightDenominator := by rw [ratiosEqual]
    _ = (rightNumerator / rightDenominator * rightDenominator) *
        leftDenominator := by ring1
    _ = rightNumerator * leftDenominator := by
      rw [ExplicitField.div_mul_cancel rightNumerator rightNonzero]

end TwoDimensionalProblems
end Purelib.Algebra.Field.Ratio.Cleared

end
