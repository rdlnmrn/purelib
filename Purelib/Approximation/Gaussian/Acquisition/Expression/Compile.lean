module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Provenance
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Arithmetic

/-!
# A finite expression front end for certificate acquisition

The numerical compiler retains the actual original children. Existing
certificates are preserved; canonical constant polynomial forms supply further
exact provenance without replacing the source evaluator.
-/

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Multivariate (Sparse)

/-- Compile once and enrich the retained original annotation with inferred exact provenance. -/
@[expose] def Expr.compile {arity : Nat} (environment : Fin arity → Annotated) (expression : Expr arity) :
    Annotated := (expression.retain environment).infer

/-- Evidence inference preserves the exact numerical channel, including its states and refinement program. -/
theorem Expr.compile_channel {arity : Nat} (environment : Fin arity → Annotated) (expression : Expr arity) :
    (expression.compile environment).channel = expression.denote environment :=
  (expression.retain environment).infer_channel.trans (expression.retain environment).channel_eq

/-- A retained constant form supplies its exact rational value when the original compilation has no provenance. -/
theorem Expr.compile_inferred_value {arity : Nat} (environment : Fin arity → Annotated) (expression : Expr arity)
    (value : Canonical)
    (unknown : (expression.retain environment).annotation.provenance = none)
    (same : (expression.normalize environment).polynomial.form.terms =
      (Sparse.constant value).terms) :
    (expression.compile environment).rationalValue = some value :=
  (expression.retain environment).infer_value value unknown same

/-- Supplied equations on original leaf annotations give exact provenance at the unchanged expression evaluator. -/
theorem Expr.compile_reduced_value {arity : Nat} (environment : Fin arity → Annotated) (expression : Expr arity)
    (value : Canonical)
    (unknown : (expression.retain environment).annotation.provenance = none)
    (nonconstant : (expression.normalize environment).Nonconstant)
    (same : (expression.normalize environment).reduceRetained.polynomial.form.terms =
      (Sparse.constant value).terms) :
    (expression.compile environment).rationalValue = some value :=
  (expression.retain environment).infer_reduced_value value unknown nonconstant same

/-- Self-subtraction retains rational provenance with exact value zero. -/
theorem Expr.compile_cancel {arity : Nat} (environment : Fin arity → Annotated) (expression : Expr arity) :
    ((Expr.sub expression expression).compile environment).rationalValue = some 0 := by
  unfold Expr.compile
  rewrite [Expr.retain_sub, dif_pos rfl]
  rfl

/-- Addition of an expression and its syntactic negation retains rational provenance with exact value zero. -/
theorem Expr.compile_add_neg {arity : Nat} (environment : Fin arity → Annotated) (expression : Expr arity) :
    ((Expr.add expression (.neg expression)).compile environment).rationalValue = some 0 := by
  unfold Expr.compile
  rewrite [Expr.retain_add, dif_pos rfl]
  rfl

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

end
