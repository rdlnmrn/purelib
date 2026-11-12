module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Rebinding
public import Purelib.Polynomial.Multivariate.Gaussian.Comparison
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Comparing original acquisition expressions over shared retained bindings

Both actual compilations are retained. Their collected leaf annotations
support a common finite coefficient environment; each original construction
is normalized once, and comparison consumes those same cached forms.
-/

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Polynomial

set_option genInjectivity false in
/-- Two original cached normalizations and their checked rebasing over a common original binding table. -/
structure Comparison {arity : Nat} (environment : Fin arity → Annotated) (first second : Expr arity) where
  /-- The actual first original compilation, bindings, coefficients and comparison. -/
  left : Normalized environment first
  /-- The actual second original compilation, bindings, coefficients and comparison. -/
  right : Normalized environment second
  /-- The actual original annotations used as a common coefficient environment. -/
  bindings : List (Binding environment)
  /-- The first retained table's actual cached positions in the common table. -/
  leftAlignment : Binding.Alignment left.bindings bindings
  /-- The second retained table's actual cached positions in the common table. -/
  rightAlignment : Binding.Alignment right.bindings bindings
  /-- The first source's actual cached coefficients, normal channel and operational comparison. -/
  leftNormalized : Multivariate.Gaussian.Normalized (Binding.channels bindings) left.compiled.annotation.channel
  /-- The second source's actual cached coefficients, normal channel and operational comparison. -/
  rightNormalized : Multivariate.Gaussian.Normalized (Binding.channels bindings) right.compiled.annotation.channel

constructive_injectivity Comparison

namespace Normalized

/-- Align actual cached normalizations and rebase their stored forms.

Both original computations remain retained inputs; their numerical compilation
and coefficient normalization are not executed again. -/
@[expose] def comparison {arity : Nat} {environment : Fin arity → Annotated} {first second : Expr arity}
    (left : Normalized environment first) (right : Normalized environment second) :
    Comparison environment first second :=
  let leftBindings := left.bindings
  let rightBindings := right.bindings
  let bindings := leftBindings ++ rightBindings
  let leftAlignment := Binding.Alignment.ofInclusion leftBindings bindings
    (fun _ present => present.append_left rightBindings)
  let rightAlignment := Binding.Alignment.ofInclusion rightBindings bindings
    (fun _ present => present.append_right leftBindings)
  let leftNormalized := left.rebind bindings leftAlignment
  let rightNormalized := right.rebind bindings rightAlignment
  ⟨left, right, bindings, leftAlignment, rightAlignment, leftNormalized, rightNormalized⟩

/-- The first rebased form is computed from the first actual coefficient cache and its retained position map. -/
theorem comparison_left_form {arity : Nat} {environment : Fin arity → Annotated} {first second : Expr arity}
    (left : Normalized environment first) (right : Normalized environment second) :
    (left.comparison right).leftNormalized.form =
      left.polynomial.form.rename (left.comparison right).leftAlignment.positions.get := rfl

/-- The second rebased form is computed from the second actual coefficient cache and its retained position map. -/
theorem comparison_right_form {arity : Nat} {environment : Fin arity → Annotated} {first second : Expr arity}
    (left : Normalized environment first) (right : Normalized environment second) :
    (left.comparison right).rightNormalized.form =
      right.polynomial.form.rename (left.comparison right).rightAlignment.positions.get := rfl

end Normalized

namespace Compiled

/-- Normalize each retained compilation once, then compare through their actual cached coefficient forms. -/
@[expose] def comparison {arity : Nat} {environment : Fin arity → Annotated} {first second : Expr arity}
    (left : Compiled environment first) (right : Compiled environment second) : Comparison environment first second :=
  left.normalize.comparison right.normalize

end Compiled

namespace Expr

/-- Compile each original expression once and retain the common supported comparison data. -/
@[expose] def comparison {arity : Nat} (environment : Fin arity → Annotated) (first second : Expr arity) :
    Comparison environment first second := (first.retain environment).comparison (second.retain environment)

end Expr

namespace Comparison

/-- Decide the formal identity route using the actual two cached coefficient forms. -/
@[expose] def decide {arity : Nat} {environment : Fin arity → Annotated} {first second : Expr arity}
    (comparison : Comparison environment first second) :
    Multivariate.Gaussian.Normalized.Comparison comparison.leftNormalized comparison.rightNormalized :=
  comparison.leftNormalized.compareForms comparison.rightNormalized

end Comparison

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

end
