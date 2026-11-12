module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Quadratic
public import Purelib.Polynomial.Multivariate.Sparse.Constant
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Data.Gaussian.Basic

/-!
# Exact provenance from retained polynomial normalizations

Constant inspection retains an exact coefficient certificate or the actual
remaining formal terms. Enrichment uses the original channel and its cached
comparison. Existing provenance takes precedence over polynomial inspection.
-/

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Multivariate

variable {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}

/-- Inspect retained coefficients, keeping the precise unresolved formal terms when they are not constant. -/
@[expose] def Normalized.inspect (normalized : Normalized environment expression) :
    Sparse.ConstantView normalized.polynomial.form := normalized.polynomial.form.constantView

/-- The cached coefficient inspector retains a variable or multiple terms rather than an exact constant. -/
@[expose] def Normalized.Nonconstant (normalized : Normalized environment expression) : Prop :=
  normalized.inspect.Nonconstant

/-- Transfer a nonconstant inspection across equality of its retained coefficient form. -/
theorem Normalized.nonconstant_of_form (normalized : Normalized environment expression)
    (form : Sparse Canonical normalized.bindings.length) (same : normalized.polynomial.form = form)
    (nonconstant : form.constantView.Nonconstant) : normalized.Nonconstant := by
  cases same
  exact nonconstant

/-- Enrich the original annotation from a retained constant reading, preserving it in unresolved cases. -/
@[expose] def Normalized.annotationFor (normalized : Normalized environment expression) :
    Sparse.ConstantView normalized.polynomial.form → Annotated
  | .exact value same =>
      ⟨normalized.compiled.annotation.channel, some (.rational (normalized.polynomial.rational value same))⟩
  | .variable _ _ _ => normalized.compiled.annotation
  | .multiple _ _ _ _ => normalized.compiled.annotation

/-- Polynomial inspection leaves the entire original numerical channel unchanged. -/
theorem Normalized.annotationFor_channel (normalized : Normalized environment expression)
    (reading : Sparse.ConstantView normalized.polynomial.form) :
    (normalized.annotationFor reading).channel = normalized.compiled.annotation.channel := by
  cases reading <;> rfl

/-- An exact retained reading gives the displayed coefficient as rational provenance. -/
theorem Normalized.annotationFor_value (normalized : Normalized environment expression) (value : Canonical)
    (same : normalized.polynomial.form.terms = (Sparse.constant value).terms) :
    (normalized.annotationFor (.exact value same)).rationalValue = some value :=
  congrArg some (normalized.polynomial.rational_value value same)

/-- Inspect cached coefficients once and attach any resulting exact evidence to the original channel. -/
@[expose] def Normalized.annotate (normalized : Normalized environment expression) : Annotated :=
  normalized.annotationFor normalized.inspect

/-- Automatic enrichment retains the exact original numerical channel. -/
theorem Normalized.annotate_channel (normalized : Normalized environment expression) :
    normalized.annotate.channel = normalized.compiled.annotation.channel :=
  normalized.annotationFor_channel normalized.inspect

/-- A retained whole-form constant identity determines the automatically inferred rational value. -/
theorem Normalized.annotate_value (normalized : Normalized environment expression) (value : Canonical)
    (same : normalized.polynomial.form.terms = (Sparse.constant value).terms) :
    normalized.annotate.rationalValue = some value := by
  unfold Normalized.annotate Normalized.inspect
  rewrite [Sparse.constantView_eq_exact normalized.polynomial.form value same]
  exact normalized.annotationFor_value value same

/-- Read exact constants first, otherwise inspect retained root owners for admitted quadratic coordinates. -/
@[expose] def Normalized.enrich (normalized : Normalized environment expression) : Annotated :=
  match normalized.inspect with
  | .exact value same => normalized.annotationFor (.exact value same)
  | .variable _ _ _ => normalized.inspectGenerators.annotate
  | .multiple _ _ _ _ => normalized.inspectGenerators.annotate

/-- Rational and quadratic enrichment preserve the entire original numerical channel. -/
theorem Normalized.enrich_channel (normalized : Normalized environment expression) :
    normalized.enrich.channel = normalized.compiled.annotation.channel := by
  unfold Normalized.enrich
  split
  · rfl
  · exact normalized.inspectGenerators.annotate_channel
  · exact normalized.inspectGenerators.annotate_channel

/-- Exact retained coefficient forms receive rational evidence before generator admission is attempted. -/
theorem Normalized.enrich_value (normalized : Normalized environment expression) (value : Canonical)
    (same : normalized.polynomial.form.terms = (Sparse.constant value).terms) :
    normalized.enrich.rationalValue = some value := by
  unfold Normalized.enrich Normalized.inspect
  rewrite [Sparse.constantView_eq_exact normalized.polynomial.form value same]
  exact normalized.annotationFor_value value same

/-- Read a retained constant immediately, otherwise reduce the original supplied power equations before inspection. -/
@[expose] def Normalized.infer (normalized : Normalized environment expression) : Annotated :=
  match normalized.inspect with
  | .exact value same => normalized.annotationFor (.exact value same)
  | .variable _ _ _ => normalized.reduceRetained.enrich
  | .multiple _ _ _ _ => normalized.reduceRetained.enrich

/-- Inference with retained equations preserves the exact original numerical channel. -/
theorem Normalized.infer_channel (normalized : Normalized environment expression) :
    normalized.infer.channel = normalized.compiled.annotation.channel := by
  unfold Normalized.infer
  split
  · rfl
  · exact normalized.reduceRetained.enrich_channel
  · exact normalized.reduceRetained.enrich_channel

/-- Existing constant forms retain their automatic exact reading before further relation reduction. -/
theorem Normalized.infer_value (normalized : Normalized environment expression) (value : Canonical)
    (same : normalized.polynomial.form.terms = (Sparse.constant value).terms) :
    normalized.infer.rationalValue = some value := by
  unfold Normalized.infer Normalized.inspect
  rewrite [Sparse.constantView_eq_exact normalized.polynomial.form value same]
  exact normalized.annotationFor_value value same

/-- A nonconstant original form acquires the exact coefficient obtained from its retained equations. -/
theorem Normalized.infer_reduced_value (normalized : Normalized environment expression) (value : Canonical)
    (nonconstant : normalized.Nonconstant)
    (same : normalized.reduceRetained.polynomial.form.terms = (Sparse.constant value).terms) :
    normalized.infer.rationalValue = some value := by
  unfold Normalized.Nonconstant at nonconstant
  unfold Normalized.infer
  split
  · rename_i value same selected
    rewrite [selected] at nonconstant
    exact False.elim nonconstant
  · exact normalized.reduceRetained.enrich_value value same
  · exact normalized.reduceRetained.enrich_value value same

/-- Preserve supplied provenance, otherwise inspect one normalization of the actual retained compilation. -/
@[expose] def Compiled.infer (compiled : Compiled environment expression) : Annotated :=
  match compiled.annotation.provenance with
  | some _ => compiled.annotation
  | none => compiled.normalize.infer

/-- Enrichment of a retained compilation preserves its actual original channel. -/
theorem Compiled.infer_channel (compiled : Compiled environment expression) :
    compiled.infer.channel = compiled.annotation.channel := by
  unfold Compiled.infer
  split
  · rfl
  · exact compiled.normalize.infer_channel

/-- Any original supplied provenance is retained literally by automatic enrichment. -/
theorem Compiled.infer_preserves (compiled : Compiled environment expression)
    {provenance : Purelib.Approximation.Gaussian.Acquisition.Provenance compiled.annotation.channel}
    (known : compiled.annotation.provenance = some provenance) : compiled.infer = compiled.annotation := by
  unfold Compiled.infer
  rewrite [known]
  rfl

/-- An original annotation without provenance acquires the exact coefficient of its retained constant form. -/
theorem Compiled.infer_value (compiled : Compiled environment expression) (value : Canonical)
    (unknown : compiled.annotation.provenance = none)
    (same : compiled.normalize.polynomial.form.terms = (Sparse.constant value).terms) :
    compiled.infer.rationalValue = some value := by
  unfold Compiled.infer
  rewrite [unknown]
  exact compiled.normalize.infer_value value same

/-- An unsupplied annotation acquires the exact value derived from its original retained binding equations. -/
theorem Compiled.infer_reduced_value (compiled : Compiled environment expression) (value : Canonical)
    (unknown : compiled.annotation.provenance = none)
    (nonconstant : compiled.normalize.Nonconstant)
    (same : compiled.normalize.reduceRetained.polynomial.form.terms = (Sparse.constant value).terms) :
    compiled.infer.rationalValue = some value := by
  unfold Compiled.infer
  rewrite [unknown]
  exact compiled.normalize.infer_reduced_value value nonconstant same

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

end
