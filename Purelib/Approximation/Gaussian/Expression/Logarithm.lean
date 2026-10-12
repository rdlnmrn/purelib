module

public import Purelib.Approximation.Gaussian.Expression.Basic
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Chart

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

/-- A complex logarithm node cannot be constructed without the anchored finite chart for its actual input expression. -/
def logarithm (input :
  Expression) (branch : Anchored.AnchoredChart input.output) :
    Expression :=
  { output := branch.output
    nodeCount := input.nodeCount + 1
    nodeCount_pos := by omega }
end Expression

end Purelib.Approximation.Gaussian.Expression

end
