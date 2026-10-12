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

namespace Purelib.Calculus.Jet.First.Basic

open Purelib.Data in
set_option genInjectivity false in
/-- A Gaussian rational value paired with its first-order coefficient.

Both components are explicit finite data. The record carries no function or differentiability assertion; its arithmetic
computes the displayed first-order rules. -/
structure FirstJet where
  /-- The displayed Gaussian rational value. -/ value : Gaussian.Basic.Canonical
  /-- The displayed Gaussian rational first-order coefficient. -/ slope : Gaussian.Basic.Canonical
deriving DecidableEq

constructive_injectivity FirstJet

end Purelib.Calculus.Jet.First.Basic

end
