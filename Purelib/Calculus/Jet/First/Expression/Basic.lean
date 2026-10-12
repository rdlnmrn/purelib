module

public import Purelib.Data.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity

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

/-! ## Finite expression syntax and one-pass differentiation -/

open Purelib.Data in
set_option genInjectivity false in
/-- Finite syntax for Gaussian rational expressions in one input.

Arithmetic nodes combine displayed values. Exponential and logarithm nodes request finite samples at the evaluation
depth; the syntax carries no domain or approximation certificate. -/
inductive JetExpression where
  /-- A fixed Gaussian rational value. -/ | constant : Gaussian.Basic.Canonical →
    JetExpression
  /-- The supplied evaluation point. -/ | input : JetExpression
  /-- The sum of two subexpressions. -/ | add : JetExpression →
    JetExpression →
    JetExpression
  /-- The negative of a subexpression. -/ | neg : JetExpression →
    JetExpression
  /-- The product of two subexpressions. -/ | mul : JetExpression →
    JetExpression →
    JetExpression
  /-- The total Gaussian rational inverse of a subexpression. -/ | reciprocal :
    JetExpression →
    JetExpression
  /-- The finite exponential sample at the value of a subexpression. -/ | exponential :
    JetExpression →
    JetExpression
  /-- The finite logarithm-of-one-plus sample at the value of a subexpression. -/ | logarithm1p :
    JetExpression →
    JetExpression
deriving DecidableEq

constructive_injectivity JetExpression

end Purelib.Calculus.Jet.First.Expression.Basic

end
