module

public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Coherent
public import Purelib.Approximation.Gaussian.Expression.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Name.Coherent
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Exponential.Progressive.Range

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

/-- Construct the certified exponential expression with its coherent output and one additional expression node. -/
def exponential (input :
  Expression) : Expression :=
  { output := Coherent.exp input.output.name
    nodeCount := input.nodeCount + 1
    nodeCount_pos := by omega }
end Expression

end Purelib.Approximation.Gaussian.Expression

end
