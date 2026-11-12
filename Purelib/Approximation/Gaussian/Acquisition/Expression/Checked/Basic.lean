module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

/-!
# Finite expression syntax with checked reciprocal nodes

A base node is the original total acquisition expression. The surrounding
constructors extend its numerical construction language with finite natural
powers, conjugation and partial reciprocal evaluation. The original total
expression evaluator and its square-root sheet semantics remain unchanged.
-/

public section
namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Checked

/-- The checked view of the original finite acquisition grammar.

The exact view retains each original total base region as one node and keeps
all original bounded atom occurrences inside that region. -/
abbrev Expr (arity : Nat) := Basic.Expr arity .checked

namespace Expr

/-- Refer to an original bounded input atom through the unchanged total expression syntax. -/
@[expose] def atom {arity : Nat} (index : Fin arity) : Expr arity := .base (.atom index)

/-- Embed an exact Gaussian rational through its original total-expression constructor. -/
@[expose] def rational {arity : Nat} (value : Purelib.Data.Gaussian.Basic.Canonical) : Expr arity :=
  .base (.rational value)

/-- Count the finite checked-expression nodes, preserving every original child occurrence. -/
@[expose] def size {arity : Nat} (expression : Expr arity) : Nat :=
  let rec count {mode : Basic.Mode} (expression : Basic.Expr arity mode) :
      match mode with | .total => PUnit | .checked => Nat :=
    match expression with
    | .atom _ | .rational _ | .root _ _ => PUnit.unit
    | .neg input =>
      match mode with
      | .total => PUnit.unit
      | .checked => count input + 1
    | .add left right | .sub left right | .mul left right =>
      match mode with
      | .total => PUnit.unit
      | .checked => count left + count right + 1
    | .base _ => 1
    | .pow input _ | .conj input | .inverse input => count input + 1
  termination_by structural expression
  count expression

end Expr

end Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
end
