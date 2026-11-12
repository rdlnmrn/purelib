module
public import Purelib.Integration.Cell.Source.Continuous
public import Purelib.Integration.Cell.Source.Comparison.Weights
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Order.Basic

/-!
# Comparison of continuous-source integration requests

Each positive request constructs its own finite partition and source ranges.
The common refinement compares their actual answers without equating those
partitions, tags, source implementations or request histories.
-/

public section

namespace Purelib.Integration.SourceFrontier.Continuous.Result

open Purelib.Approximation
open Purelib.Data.Rat

/-- Independently computed continuous-source answers agree within their two requested widths.

Only equality of the original sources at rational points of the unit interval
is required. The comparison computes a common refinement, retaining both
original frontiers and their source readings. -/
theorem answer_difference_lt_of_same {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {leftModulus : Rational.Uniform.Modulus leftSource} {rightModulus : Rational.Uniform.Modulus rightSource}
    (left : Result leftModulus) (right : Result rightModulus)
    (same : ∀ point, 0 ≤ point → point ≤ 1 → leftSource point = rightSource point) :
    Fraction.abs (left.answer - right.answer) <
      left.preparation.request.tolerance + right.preparation.request.tolerance := by
  let common := SourceFrontier.commonReadings left.frontier right.frontier
  have comparison := common.answers_difference_le_of_same left.answer right.answer left.answer_contains
    right.answer_contains same
  have paid := Fraction.Order.Arithmetic.add_lt_add_direct left.accurate right.accurate
  exact comparison.trans_lt paid

end Purelib.Integration.SourceFrontier.Continuous.Result

end
