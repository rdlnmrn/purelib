module

import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Expression.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Certified finite CCL expression trees

This indexed syntax packages exactly the side conditions needed at each
operation: coherence is carried by every node, division stores finite
denominator apartness, and a complex-log node stores an anchored chart.  An
expression denotes its constructed progressive process, not a completed
complex value.
-/

namespace Purelib.Approximation.Gaussian.Expression
section Expression

/-- The closed rational request modulus supplied by the coherence sidecar of the constructed output process. -/
def requestAllowance (expression :
  Expression)
    (target : Fraction.Rational) : Fraction.Rational :=
  expression.output.coherent.accuracyRequest target

/-- The constructed expression's semantic request modulus is positive for a positive target. -/
theorem requestAllowance_pos (expression :
  Expression) {target : Fraction.Rational}
    (positive : 0 < target) :
    0 < expression.requestAllowance target :=
  expression.output.coherent.accuracyRequest_pos positive

/-- A request below the displayed modulus makes the semantic coherence allowance, not merely the enclosure radius,
smaller than the target. -/
theorem refined_allowance_lt (expression :
  Expression)
    {target request : Fraction.Rational}
    (targetPositive : 0 < target) (requestPositive : 0 < request)
    (requestSmall : request < expression.requestAllowance target) :
    expression.output.coherent.allowance
        (expression.output.name.process.refine expression.output.name.state
          request requestPositive) < target :=
  expression.output.coherent.refine_accurate expression.output.name.state
    target targetPositive
    request requestPositive requestSmall
end Expression

end Purelib.Approximation.Gaussian.Expression

end
