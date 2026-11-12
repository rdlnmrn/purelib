module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.PowerReduction
public import Purelib.Polynomial.Multivariate.Gaussian.PowerCoordinates.Pair
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Pair readback of original retained acquisition expressions

The inspection keeps the entire original compilation, actual annotated leaf
owners and cached normalization. Its result reads bounded real coefficients
at one original selected generator; all unsupported terms and coefficients
remain available through the retained typed outcome.
-/

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic.Normalized

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Multivariate

set_option genInjectivity false in
/-- A pair inspection retaining the complete original expression normalization and all original leaf owners. -/
structure PairInspection {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (normalized : Normalized environment expression)
    (index : Fin normalized.bindings.length) (parameter : Rational) where
  /-- The entire actual expression normalization supplied to the procedure. -/
  source : Normalized environment expression
  /-- The retained source is the entire original input, including its compilation and leaf cache. -/
  source_eq : source = normalized
  /-- The pair or every unresolved condition at that same original cached polynomial and generator index. -/
  result : Gaussian.Normalized.PairCheck normalized.polynomial index parameter

constructive_injectivity PairInspection

/-- Read cached pair coordinates while retaining the original compiled expression and exact selected leaf owners. -/
@[expose] def inspectPair {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (normalized : Normalized environment expression) (index : Fin normalized.bindings.length) (parameter : Rational) :
    PairInspection normalized index parameter :=
  ⟨normalized, rfl, normalized.polynomial.inspectPair index parameter⟩

/-- Pair inspection preserves the complete original expression normalization as actual retained data. -/
theorem inspectPair_source {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (normalized : Normalized environment expression) (index : Fin normalized.bindings.length) (parameter : Rational) :
    (normalized.inspectPair index parameter).source = normalized := rfl

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic.Normalized

end
