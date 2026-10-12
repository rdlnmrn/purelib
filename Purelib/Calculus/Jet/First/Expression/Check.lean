module
import Purelib.Data.Gaussian.Basic
import Purelib.Calculus.Jet.First.Expression.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Calculus.Jet.First.Expression.Evaluation

open Purelib.Data.Gaussian.Basic (Canonical)

section
@[expose] public section

/-!
# Executable first jets and forward differentiation

A `FirstJet` is just two displayed Gaussian rationals: a value and its
first-order coefficient.  It is not a function graph, germ, infinitesimal,
or equivalence class.  The operations below are finite programs implementing
the sum, product, chain, reciprocal, and quotient rules.

`JetExpression` is finite syntax.  Its evaluator computes the value and
first-order coefficient together.  Exponential and logarithm nodes call the
finite sample programs from the preceding calculus modules at the requested
natural depth.
-/

namespace Purelib.Calculus.Jet.First.Expression.Basic
namespace JetExpression

open Purelib.Calculus.Jet.First in
open Purelib.Data in
/-- Check the displayed domain bounds throughout one finite evaluation.

Every subtree must pass. Reciprocal nodes require a nonzero inner value, exponential nodes require squared norm at most
one, and logarithm-of-one-plus nodes require squared norm at most one quarter. The Boolean uses values at the supplied
input and depth. -/
def admissible : Expression.Basic.JetExpression →
  Canonical → Nat → Bool
  | .constant _, _, _ => true
  | .input, _, _ => true
  | .add left right, point, index =>
      left.admissible point index && right.admissible point index
  | .neg expression, point, index => expression.admissible point index
  | .mul left right, point, index =>
      left.admissible point index && right.admissible point index
  | .reciprocal expression, point, index =>
      expression.admissible point index &&
        decide (expression.eval point index ≠ 0)
  | .exponential expression, point, index =>
      expression.admissible point index &&
        decide (Canonical.normSq (expression.eval point index) ≤ 1)
  | .logarithm1p expression, point, index =>
      expression.admissible point index &&
        decide (Canonical.normSq (expression.eval point index) ≤ 1 / 4)

end JetExpression

end Purelib.Calculus.Jet.First.Expression.Basic

end
