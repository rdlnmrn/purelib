module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Inspection
public import Purelib.Polynomial.Multivariate.Gaussian.Normalization
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Polynomial normalization of actual retained acquisition expressions

The original compilation is retained with all of its annotations and child
nodes. Normalization reads their existing leaf bindings and comparisons; it
does not compile another numerical expression or repeat a root isolation.
-/

public section

namespace Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Polynomial

/-- Prefer a retained exact-coefficient certificate, evaluating a fallback only when it is needed. -/
@[expose] def Annotated.normalizeWith {arity : Nat} (bindings : Fin arity → CoherentNamed)
    (annotation : Annotated) (fallback : Unit → Multivariate.Gaussian.Normalized bindings annotation.channel) :
    Multivariate.Gaussian.Normalized bindings annotation.channel :=
  match annotation.provenance with
  | some provenance => match provenance.rationalReading with
    | some evidence => Multivariate.Gaussian.Normalized.ofRational bindings evidence
    | none => fallback ()
  | none => fallback ()

/-- Read the coefficient choice made by an annotation without constructing numerical comparisons. -/
@[expose] def Annotated.coefficientsWith {arity : Nat} (annotation : Annotated)
    (fallback : Unit → Multivariate.Sparse Purelib.Data.Gaussian.Basic.Canonical arity) :=
  match annotation.provenance with
  | some provenance => match provenance.rationalReading with
    | some evidence => Multivariate.Sparse.constant evidence.value
    | none => fallback ()
  | none => fallback ()

/-- The annotation's coefficient readback follows its retained exact reading or the same fallback form. -/
theorem Annotated.normalizeWith_form {arity : Nat} (bindings : Fin arity → CoherentNamed)
    (annotation : Annotated) (fallback : Unit → Multivariate.Gaussian.Normalized bindings annotation.channel)
    (coefficients : Unit → Multivariate.Sparse Purelib.Data.Gaussian.Basic.Canonical arity)
    (same : (fallback ()).form = coefficients ()) :
    (annotation.normalizeWith bindings fallback).form = annotation.coefficientsWith coefficients := by
  unfold normalizeWith coefficientsWith
  cases annotation.provenance with
  | none => exact same
  | some provenance =>
      dsimp only
      cases provenance.rationalReading with
      | none => exact same
      | some evidence => rfl

end Purelib.Approximation.Gaussian.Acquisition

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Polynomial

/-- Normalize an actual original leaf using its checked position in the retained original binding table. -/
@[expose] def Binding.normalize {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) (inspections : Binding.Inspections bindings)
    (leaf : Leaf arity) (annotation : Annotated)
    (annotation_eq : annotation = leaf.annotation environment) (present : Binding.Present leaf bindings) :
    Multivariate.Gaussian.Normalized (Binding.channels bindings) annotation.channel :=
  let position := Binding.locate leaf bindings present
  let inspection := inspections.get bindings position.val
  let normalized := match inspection.scalar with
    | some reading => Multivariate.Gaussian.Normalized.ofRational (Binding.channels bindings) reading
    | none => Multivariate.Gaussian.Normalized.atom (Binding.channels bindings) position.val
  have same : (Binding.channels bindings position.val) = annotation.channel :=
    congrArg Annotated.channel ((Binding.Lookup.annotation_eq position.val position.property).trans annotation_eq.symm)
  normalized.transport same

/-- Read cached coefficient data at one actual bounded original occurrence. -/
@[expose] def Binding.coefficientsAt {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) (inspections : Binding.Inspections bindings)
    (index : Fin bindings.length) :=
  match (inspections.get bindings index).scalar with
  | some reading => Multivariate.Sparse.constant reading.value
  | none => Multivariate.Sparse.atom index

/-- An occurrence without a scalar reading retains its actual original formal atom. -/
theorem Binding.coefficientsAt_nonscalar {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) (inspections : Binding.Inspections bindings)
    (index : Fin bindings.length) (missing : (inspections.get bindings index).scalar = none) :
    Binding.coefficientsAt bindings inspections index = Multivariate.Sparse.atom index := by
  unfold Binding.coefficientsAt
  rewrite [missing]
  rfl

/-- Read the selected original leaf's coefficients from its same retained scalar inspection. -/
@[expose] def Binding.coefficients {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) (inspections : Binding.Inspections bindings)
    (leaf : Leaf arity) (present : Binding.Present leaf bindings) :=
  Binding.coefficientsAt bindings inspections (Binding.locate leaf bindings present).val

/-- Read only the leaf's cached coefficients, leaving its numerical comparison and source transport opaque. -/
theorem Binding.normalize_form {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) (inspections : Binding.Inspections bindings)
    (leaf : Leaf arity) (annotation : Annotated)
    (annotation_eq : annotation = leaf.annotation environment) (present : Binding.Present leaf bindings) :
    (Binding.normalize bindings inspections leaf annotation annotation_eq present).form =
      Binding.coefficients bindings inspections leaf present := by
  unfold Binding.normalize Binding.coefficients Binding.coefficientsAt
  dsimp only [Multivariate.Gaussian.Normalized.transport]
  cases (inspections.get bindings (Binding.locate leaf bindings present).val).scalar <;> rfl

/-- Normalize the actual original construction over a finite table supporting every retained source leaf.

Each child is normalized once. Shared cancellation and square cases consume
that same child normalization twice; retained rational evidence takes the
constant route without rebuilding the annotated numerical source. -/
@[expose] def Construction.normalize {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) (inspections : Binding.Inspections bindings) :
    {expression : Expr arity} → (annotation : Annotated) →
    (construction : Construction environment expression annotation) → construction.Supported bindings →
      Multivariate.Gaussian.Normalized (Binding.channels bindings) annotation.channel
  | _, .(actual), .atom index actual source_eq, supported =>
      Binding.normalize bindings inspections (.atom index) actual source_eq supported
  | _, .(actual), .rational value actual source_eq, _ =>
      actual.normalizeWith (Binding.channels bindings) (fun _ =>
        (Multivariate.Gaussian.Normalized.constant (Binding.channels bindings) value).transport
          (congrArg Annotated.channel source_eq).symm)
  | _, .(actual), .root parameter sheet actual source_eq, supported =>
      Binding.normalize bindings inspections (.root parameter sheet) actual source_eq supported
  | _, annotation, .neg child construction output_eq, supported =>
      annotation.normalizeWith (Binding.channels bindings) (fun _ =>
        let input := construction.normalize bindings inspections child supported
        input.neg.transport (congrArg Annotated.channel output_eq).symm)
  | _, annotation, .add _ first second firstConstruction secondConstruction _ output_eq, supported =>
      annotation.normalizeWith (Binding.channels bindings) (fun _ =>
        let left := firstConstruction.normalize bindings inspections first supported.1
        let right := secondConstruction.normalize bindings inspections second supported.2
        (left.add right).transport (congrArg Annotated.channel output_eq).symm)
  | _, annotation, .addNeg child construction output_eq, supported =>
      annotation.normalizeWith (Binding.channels bindings) (fun _ =>
        let input := construction.normalize bindings inspections child supported
        (input.sub input).transport (congrArg Annotated.channel output_eq).symm)
  | _, annotation, .sub _ first second firstConstruction secondConstruction _ output_eq, supported =>
      annotation.normalizeWith (Binding.channels bindings) (fun _ =>
        let left := firstConstruction.normalize bindings inspections first supported.1
        let right := secondConstruction.normalize bindings inspections second supported.2
        (left.sub right).transport (congrArg Annotated.channel output_eq).symm)
  | _, annotation, .subSelf child construction output_eq, supported =>
      annotation.normalizeWith (Binding.channels bindings) (fun _ =>
        let input := construction.normalize bindings inspections child supported
        (input.sub input).transport (congrArg Annotated.channel output_eq).symm)
  | _, annotation, .mul _ first second firstConstruction secondConstruction _ output_eq, supported =>
      annotation.normalizeWith (Binding.channels bindings) (fun _ =>
        let left := firstConstruction.normalize bindings inspections first supported.1
        let right := secondConstruction.normalize bindings inspections second supported.2
        (left.mul right).transport (congrArg Annotated.channel output_eq).symm)
  | _, annotation, .square child construction _ output_eq, supported =>
      annotation.normalizeWith (Binding.channels bindings) (fun _ =>
        let input := construction.normalize bindings inspections child supported
        (input.mul input).transport (congrArg Annotated.channel output_eq).symm)

/-- Project coefficient operations from the same retained construction and cached leaf inspections.

This readback isolates finite scalar calculation from dependent numerical
comparison fields. It uses the existing sparse operations and the original
construction; it performs no admission or numerical compilation. -/
@[expose] def Construction.coefficients {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) (inspections : Binding.Inspections bindings) :
    {expression : Expr arity} → (annotation : Annotated) →
    (construction : Construction environment expression annotation) → construction.Supported bindings →
      Multivariate.Sparse Purelib.Data.Gaussian.Basic.Canonical bindings.length
  | _, _, .atom index _ _, supported => Binding.coefficients bindings inspections (.atom index) supported
  | _, actual, .rational value _ _, _ => actual.coefficientsWith (fun _ => Multivariate.Sparse.constant value)
  | _, _, .root parameter sheet _ _, supported =>
      Binding.coefficients bindings inspections (.root parameter sheet) supported
  | _, annotation, .neg child construction _, supported =>
      annotation.coefficientsWith (fun _ => (construction.coefficients bindings inspections child supported).neg)
  | _, annotation, .add _ first second firstConstruction secondConstruction _ _, supported =>
      annotation.coefficientsWith (fun _ =>
        (firstConstruction.coefficients bindings inspections first supported.1).add
          (secondConstruction.coefficients bindings inspections second supported.2))
  | _, annotation, .addNeg child construction _, supported =>
      annotation.coefficientsWith (fun _ =>
        let input := construction.coefficients bindings inspections child supported
        input.sub input)
  | _, annotation, .sub _ first second firstConstruction secondConstruction _ _, supported =>
      annotation.coefficientsWith (fun _ =>
        (firstConstruction.coefficients bindings inspections first supported.1).sub
          (secondConstruction.coefficients bindings inspections second supported.2))
  | _, annotation, .subSelf child construction _, supported =>
      annotation.coefficientsWith (fun _ =>
        let input := construction.coefficients bindings inspections child supported
        input.sub input)
  | _, annotation, .mul _ first second firstConstruction secondConstruction _ _, supported =>
      annotation.coefficientsWith (fun _ =>
        (firstConstruction.coefficients bindings inspections first supported.1).mul
          (secondConstruction.coefficients bindings inspections second supported.2))
  | _, annotation, .square child construction _ _, supported =>
      annotation.coefficientsWith (fun _ =>
        let input := construction.coefficients bindings inspections child supported
        input.mul input)

/-- Coefficient projection agrees with normalization of the same original construction and inspection cache. -/
theorem Construction.normalize_form {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) (inspections : Binding.Inspections bindings)
    {expression : Expr arity} {annotation : Annotated} (construction : Construction environment expression annotation)
    (supported : construction.Supported bindings) :
    (construction.normalize bindings inspections annotation supported).form =
      construction.coefficients bindings inspections annotation supported := by
  induction construction with
  | atom index annotation source_eq => exact Binding.normalize_form bindings inspections _ _ source_eq supported
  | rational value annotation source_eq =>
      exact annotation.normalizeWith_form _ _ _ rfl
  | root parameter sheet annotation source_eq =>
      exact Binding.normalize_form bindings inspections _ _ source_eq supported
  | neg child construction output_eq ih =>
      apply Annotated.normalizeWith_form
      exact congrArg Multivariate.Sparse.neg (ih supported)
  | add different first second firstConstruction secondConstruction inferAlgebraic output_eq ihFirst ihSecond =>
      apply Annotated.normalizeWith_form
      exact congrArg₂ Multivariate.Sparse.add (ihFirst supported.1) (ihSecond supported.2)
  | addNeg child construction output_eq ih =>
      apply Annotated.normalizeWith_form
      exact congrArg₂ Multivariate.Sparse.sub (ih supported) (ih supported)
  | sub different first second firstConstruction secondConstruction inferAlgebraic output_eq ihFirst ihSecond =>
      apply Annotated.normalizeWith_form
      exact congrArg₂ Multivariate.Sparse.sub (ihFirst supported.1) (ihSecond supported.2)
  | subSelf child construction output_eq ih =>
      apply Annotated.normalizeWith_form
      exact congrArg₂ Multivariate.Sparse.sub (ih supported) (ih supported)
  | mul different first second firstConstruction secondConstruction inferAlgebraic output_eq ihFirst ihSecond =>
      apply Annotated.normalizeWith_form
      exact congrArg₂ Multivariate.Sparse.mul (ihFirst supported.1) (ihSecond supported.2)
  | square child construction inferAlgebraic output_eq ih =>
      apply Annotated.normalizeWith_form
      exact congrArg₂ Multivariate.Sparse.mul (ih supported) (ih supported)

set_option genInjectivity false in
/-- An original retained compilation with its actual leaf table and cached polynomial comparison. -/
structure Normalized {arity : Nat} (environment : Fin arity → Annotated) (expression : Expr arity) where
  /-- The original retained numerical compilation and all actual child annotations. -/
  compiled : Compiled environment expression
  /-- The actual original indexed atom and labelled root annotations used by normalization. -/
  bindings : List (Binding environment)
  /-- Actual shared provenance inspections at the original table positions. -/
  inspections : Binding.Inspections bindings
  /-- The retained table covers every original variable leaf of the original construction. -/
  supported : compiled.construction.Supported bindings
  /-- The cached coefficient form, normal channel and comparison at the original numerical output. -/
  polynomial : Multivariate.Gaussian.Normalized (Binding.channels bindings) compiled.annotation.channel

constructive_injectivity Normalized

/-- Normalize an existing actual compilation, reusing its original annotations and root owners. -/
@[expose] def Compiled.normalize {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) : Normalized environment expression :=
  let bindings := compiled.bindings
  let inspections := Binding.inspect bindings
  let supported := compiled.construction.supported_bindings
  let polynomial := compiled.construction.normalize bindings inspections compiled.annotation supported
  ⟨compiled, bindings, inspections, supported, polynomial⟩

/-- Compile the original expression once and retain its separate cached polynomial normalization. -/
@[expose] def Expr.normalize {arity : Nat} (environment : Fin arity → Annotated) (expression : Expr arity) :
    Normalized environment expression := (expression.retain environment).normalize

/-- The retained original numerical output remains exactly the original expression evaluator. -/
theorem Normalized.original_eq {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (normalized : Normalized environment expression) :
    normalized.compiled.annotation.channel = expression.denote environment := normalized.compiled.channel_eq

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

end
