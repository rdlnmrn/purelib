module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Evaluation
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Arithmetic
import Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained acquisition compilation

Every node retains its actual annotated output and the actual compiled children
that produced it. Cancellation and repeated multiplication retain one child,
so traversing the construction never invokes the original root producer again.
-/

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic

set_option genInjectivity false in
/-- The original annotated output and actual children of a finite compilation node.

Every node retains its actual source annotations. Equality fields authenticate
its constructor without replacing retained data by a fresh producer call. -/
inductive Construction {arity : Nat} (environment : Fin arity → Annotated) : Expr arity → Annotated → Type 1 where
  /-- Retain the actual annotation obtained at an original atom index. -/
  | atom (index : Fin arity) (annotation : Annotated) (source_eq : annotation = environment index) :
      Construction environment (.atom index) annotation
  /-- Retain the actual exact Gaussian constant annotation. -/
  | rational (value : Canonical) (annotation : Annotated) (source_eq : annotation = Annotated.rational value) :
      Construction environment (.rational value) annotation
  /-- Retain the actual selected root annotation with its original isolation owner. -/
  | root (parameter : Canonical) (sheet : Fin 2) (annotation : Annotated)
      (source_eq : annotation = Annotated.root parameter sheet) :
      Construction environment (.root parameter sheet) annotation
  /-- Retain the original negation output and the actual compiled child that produced it. -/
  | neg {input : Expr arity} {output : Annotated} (child : Annotated)
      (construction : Construction environment input child) (output_eq : output = child.neg) :
      Construction environment (.neg input) output
  /-- Retain an unshared addition output and both original compiled child annotations. -/
  | add {left right : Expr arity} {output : Annotated} (different : right ≠ .neg left)
      (first second : Annotated) (firstConstruction : Construction environment left first)
      (secondConstruction : Construction environment right second) (inferAlgebraic : Bool)
      (output_eq : output = first.add second inferAlgebraic) :
      Construction environment (.add left right) output
  /-- Cancel an original child against its syntactic negation with one retained child annotation. -/
  | addNeg {input : Expr arity} {output : Annotated} (child : Annotated)
      (construction : Construction environment input child) (output_eq : output = child.cancel) :
      Construction environment (.add input (.neg input)) output
  /-- Retain an unshared subtraction output and both original compiled child annotations. -/
  | sub {left right : Expr arity} {output : Annotated} (different : left ≠ right)
      (first second : Annotated) (firstConstruction : Construction environment left first)
      (secondConstruction : Construction environment right second) (inferAlgebraic : Bool)
      (output_eq : output = first.add second.neg inferAlgebraic) :
      Construction environment (.sub left right) output
  /-- Cancel two occurrences of one original retained child annotation. -/
  | subSelf {input : Expr arity} {output : Annotated} (child : Annotated)
      (construction : Construction environment input child) (output_eq : output = child.cancel) :
      Construction environment (.sub input input) output
  /-- Retain an unshared multiplication output and both original compiled child annotations. -/
  | mul {left right : Expr arity} {output : Annotated} (different : left ≠ right)
      (first second : Annotated) (firstConstruction : Construction environment left first)
      (secondConstruction : Construction environment right second) (inferAlgebraic : Bool)
      (output_eq : output = first.mul second inferAlgebraic) :
      Construction environment (.mul left right) output
  /-- Multiply two occurrences of one original retained child annotation. -/
  | square {input : Expr arity} {output : Annotated} (child : Annotated)
      (construction : Construction environment input child) (inferAlgebraic : Bool)
      (output_eq : output = child.square inferAlgebraic) :
      Construction environment (.mul input input) output

constructive_injectivity Construction

set_option genInjectivity false in
/-- An original expression's actual annotated result and its retained compilation construction. -/
structure Compiled {arity : Nat} (environment : Fin arity → Annotated) (expression : Expr arity) where
  /-- The actual annotated output produced once by this compilation node. -/
  annotation : Annotated
  /-- The actual original child annotations and checked operation producing this output. -/
  construction : Construction environment expression annotation

constructive_injectivity Compiled

/-- Package an actual retained annotation and its construction as a compiled child view. -/
@[expose] def Construction.compiled {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (annotation : Annotated) (construction : Construction environment expression annotation) :
    Compiled environment expression := ⟨annotation, construction⟩

/-- A retained construction preserves the exact original expression's numerical channel. -/
theorem Construction.channel_eq {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    {annotation : Annotated} (construction : Construction environment expression annotation) :
    annotation.channel = expression.denote environment := by
  induction construction with
  | atom index annotation source_eq => exact congrArg Annotated.channel source_eq
  | rational value annotation source_eq => exact congrArg Annotated.channel source_eq
  | root parameter sheet annotation source_eq => exact congrArg Annotated.channel source_eq
  | neg child construction output_eq ih =>
      exact (congrArg Annotated.channel output_eq).trans (congrArg CoherentNamed.neg ih)
  | add different first second firstConstruction secondConstruction inferAlgebraic output_eq ihFirst ihSecond =>
      exact (congrArg Annotated.channel output_eq).trans (congrArg₂ CoherentNamed.add ihFirst ihSecond)
  | addNeg child construction output_eq ih =>
      exact (congrArg Annotated.channel output_eq).trans
        (congrArg₂ CoherentNamed.add ih (congrArg CoherentNamed.neg ih))
  | sub different first second firstConstruction secondConstruction inferAlgebraic output_eq ihFirst ihSecond =>
      exact (congrArg Annotated.channel output_eq).trans
        (congrArg₂ CoherentNamed.add ihFirst (congrArg CoherentNamed.neg ihSecond))
  | subSelf child construction output_eq ih =>
      exact (congrArg Annotated.channel output_eq).trans
        (congrArg₂ CoherentNamed.add ih (congrArg CoherentNamed.neg ih))
  | mul different first second firstConstruction secondConstruction inferAlgebraic output_eq ihFirst ihSecond =>
      exact (congrArg Annotated.channel output_eq).trans (congrArg₂ CoherentNamed.mul ihFirst ihSecond)
  | square child construction inferAlgebraic output_eq ih =>
      exact (congrArg Annotated.channel output_eq).trans (congrArg₂ CoherentNamed.mul ih ih)

/-- A compiled view exposes exact numerical readback to its original expression evaluator. -/
theorem Compiled.channel_eq {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) : compiled.annotation.channel = expression.denote environment :=
  compiled.construction.channel_eq

/-- Retained total compilations respect operational comparisons of their actual input atoms.

Every branch consumes its original child annotations, including shared
cancellation and square nodes. Literal-root comparisons use the retained
annotations and their identities, without constructing another root owner.
-/
def Construction.namedEquivalent {arity : Nat} {environment other : Fin arity → Annotated}
    {expression : Expr arity} {firstOutput secondOutput : Annotated}
    (first : Construction environment expression firstOutput) (second : Construction other expression secondOutput)
    (atoms : ∀ index, NamedEquivalent (environment index).channel.name (other index).channel.name) :
    NamedEquivalent firstOutput.channel.name secondOutput.channel.name :=
  match first, second with
  | .atom index _ firstEq, .atom _ _ secondEq =>
      NamedEquivalent.transport
        (congrArg (fun value : Annotated => value.channel.name) firstEq.symm)
        (congrArg (fun value : Annotated => value.channel.name) secondEq.symm) (atoms index)
  | .rational _ first firstEq, .rational _ _ secondEq =>
      NamedEquivalent.transport rfl
        (congrArg (fun value : Annotated => value.channel.name) (firstEq.trans secondEq.symm))
        (NamedEquivalent.refl first.channel.name)
  | .root _ _ first firstEq, .root _ _ _ secondEq =>
      NamedEquivalent.transport rfl
        (congrArg (fun value : Annotated => value.channel.name) (firstEq.trans secondEq.symm))
        (NamedEquivalent.refl first.channel.name)
  | .neg _ child firstEq, .neg _ other secondEq =>
      NamedEquivalent.transport
        (congrArg (fun value : Annotated => value.channel.name) firstEq.symm)
        (congrArg (fun value : Annotated => value.channel.name) secondEq.symm)
        (Additive.coherentNeg_respects _ _ (child.namedEquivalent other atoms))
  | .add _ _ _ first second _ firstEq, .add _ _ _ otherFirst otherSecond _ secondEq =>
      NamedEquivalent.transport
        (congrArg (fun value : Annotated => value.channel.name) firstEq.symm)
        (congrArg (fun value : Annotated => value.channel.name) secondEq.symm)
        (Sum.Congruence.coherentAdd_respects _ _ _ _
          (first.namedEquivalent otherFirst atoms) (second.namedEquivalent otherSecond atoms))
  | .add different _ _ _ _ _ _, .addNeg _ _ _ => False.elim (different rfl)
  | .addNeg _ _ _, .add different _ _ _ _ _ _ => False.elim (different rfl)
  | .addNeg _ child firstEq, .addNeg _ other secondEq =>
      let compared := child.namedEquivalent other atoms
      NamedEquivalent.transport
        (congrArg (fun value : Annotated => value.channel.name) firstEq.symm)
        (congrArg (fun value : Annotated => value.channel.name) secondEq.symm)
        (Sum.Congruence.coherentAdd_respects _ _ _ _ compared (Additive.coherentNeg_respects _ _ compared))
  | .sub _ _ _ first second _ firstEq, .sub _ _ _ otherFirst otherSecond _ secondEq =>
      NamedEquivalent.transport
        (congrArg (fun value : Annotated => value.channel.name) firstEq.symm)
        (congrArg (fun value : Annotated => value.channel.name) secondEq.symm)
        (Sum.Congruence.coherentAdd_respects _ _ _ _ (first.namedEquivalent otherFirst atoms)
          (Additive.coherentNeg_respects _ _ (second.namedEquivalent otherSecond atoms)))
  | .sub different _ _ _ _ _ _, .subSelf _ _ _ => False.elim (different rfl)
  | .subSelf _ _ _, .sub different _ _ _ _ _ _ => False.elim (different rfl)
  | .subSelf _ child firstEq, .subSelf _ other secondEq =>
      let compared := child.namedEquivalent other atoms
      NamedEquivalent.transport
        (congrArg (fun value : Annotated => value.channel.name) firstEq.symm)
        (congrArg (fun value : Annotated => value.channel.name) secondEq.symm)
        (Sum.Congruence.coherentAdd_respects _ _ _ _ compared (Additive.coherentNeg_respects _ _ compared))
  | .mul _ _ _ first second _ firstEq, .mul _ _ _ otherFirst otherSecond _ secondEq =>
      NamedEquivalent.transport
        (congrArg (fun value : Annotated => value.channel.name) firstEq.symm)
        (congrArg (fun value : Annotated => value.channel.name) secondEq.symm)
        (Product.Congruence.coherentMul_respects _ _ _ _
          (first.namedEquivalent otherFirst atoms) (second.namedEquivalent otherSecond atoms))
  | .mul different _ _ _ _ _ _, .square _ _ _ _ => False.elim (different rfl)
  | .square _ _ _ _, .mul different _ _ _ _ _ _ => False.elim (different rfl)
  | .square _ child _ firstEq, .square _ other _ secondEq =>
      let compared := child.namedEquivalent other atoms
      NamedEquivalent.transport
        (congrArg (fun value : Annotated => value.channel.name) firstEq.symm)
        (congrArg (fun value : Annotated => value.channel.name) secondEq.symm)
        (Product.Congruence.coherentMul_respects _ _ _ _ compared compared)
termination_by structural first

/-- Compare both retained compiler outputs using their original construction trees and atom comparisons. -/
def Compiled.namedEquivalent {arity : Nat} {environment other : Fin arity → Annotated} {expression : Expr arity}
    (first : Compiled environment expression) (second : Compiled other expression)
    (atoms : ∀ index, NamedEquivalent (environment index).channel.name (other index).channel.name) :
    NamedEquivalent first.annotation.channel.name second.annotation.channel.name :=
  first.construction.namedEquivalent second.construction atoms

/-- Compile the original numerical expression once, retaining the actual children used by every arithmetic branch.

The inference policy is captured by the shared grammar's structurally recursive
helper. Deferring compound general algebraic inference preserves whole original
leaf annotations and efficient scalar/quadratic branches. -/
@[expose] def Expr.retain {arity : Nat} (environment : Fin arity → Annotated)
    (expression : Expr arity) (inferAlgebraic : Bool := true) : Compiled environment expression :=
  let Result : (mode : Mode) → Expr arity mode → Type 1 :=
    fun mode => match mode with
    | .total => fun expression => Compiled environment expression
    | .checked => fun _ => PUnit
  let rec compile {mode : Mode} (expression : Expr arity mode) : Result mode expression :=
    match expression with
    | .atom index =>
        let annotation := environment index
        ⟨annotation, .atom index annotation rfl⟩
    | .rational value => let annotation := Annotated.rational value
        ⟨annotation, .rational value annotation rfl⟩
    | .root parameter sheet => let annotation := Annotated.root parameter sheet
        ⟨annotation, .root parameter sheet annotation rfl⟩
    | .neg input =>
      match mode with
      | .total =>
          let child := compile input
          ⟨child.annotation.neg, .neg child.annotation child.construction rfl⟩
      | .checked => PUnit.unit
    | .add left right =>
      match mode with
      | .total =>
          if same : right = .neg left then
            let child := compile left
            same.symm ▸ ⟨child.annotation.cancel, .addNeg child.annotation child.construction rfl⟩
          else
            let first := compile left
            let second := compile right
            ⟨first.annotation.add second.annotation inferAlgebraic,
              .add same first.annotation second.annotation first.construction second.construction inferAlgebraic rfl⟩
      | .checked => PUnit.unit
    | .sub left right =>
      match mode with
      | .total =>
          if same : left = right then
            let child := compile left
            same ▸ ⟨child.annotation.cancel, .subSelf child.annotation child.construction rfl⟩
          else
            let first := compile left
            let second := compile right
            ⟨first.annotation.add second.annotation.neg inferAlgebraic,
              .sub same first.annotation second.annotation first.construction second.construction inferAlgebraic rfl⟩
      | .checked => PUnit.unit
    | .mul left right =>
      match mode with
      | .total =>
          if same : left = right then
            let child := compile left
            same ▸ ⟨child.annotation.square inferAlgebraic,
              .square child.annotation child.construction inferAlgebraic rfl⟩
          else
            let first := compile left
            let second := compile right
            ⟨first.annotation.mul second.annotation inferAlgebraic,
              .mul same first.annotation second.annotation first.construction second.construction inferAlgebraic rfl⟩
      | .checked => PUnit.unit
    | .base _ | .pow _ _ | .conj _ | .inverse _ => PUnit.unit
  termination_by structural expression
  compile expression

/-- Retaining an original atom reads its supplied annotation at the same bounded index. -/
@[cbv_eval] theorem Expr.retain_atom {arity : Nat} (environment : Fin arity → Annotated)
    (index : Fin arity) (inferAlgebraic : Bool := true) :
    (Expr.atom index).retain environment inferAlgebraic =
      ⟨environment index, .atom index (environment index) rfl⟩ := rfl

/-- Retaining a scalar stores its original exact annotation and constructor certificate. -/
@[cbv_eval] theorem Expr.retain_rational {arity : Nat} (environment : Fin arity → Annotated)
    (value : Canonical) (inferAlgebraic : Bool := true) :
    (Expr.rational value).retain environment inferAlgebraic =
      ⟨Annotated.rational value, .rational value (Annotated.rational value) rfl⟩ := rfl

/-- Retaining a root stores the original parameter, sheet and actual root annotation. -/
@[cbv_eval] theorem Expr.retain_root {arity : Nat} (environment : Fin arity → Annotated)
    (parameter : Canonical) (sheet : Fin 2) (inferAlgebraic : Bool := true) :
    (Expr.root parameter sheet).retain environment inferAlgebraic =
      ⟨Annotated.root parameter sheet, .root parameter sheet (Annotated.root parameter sheet) rfl⟩ := rfl

/-- Retaining negation consumes the same once-retained original child. -/
@[cbv_eval] theorem Expr.retain_neg {arity : Nat} (environment : Fin arity → Annotated)
    (input : Expr arity) (inferAlgebraic : Bool := true) :
    (Expr.neg input).retain environment inferAlgebraic =
      let child := input.retain environment inferAlgebraic
      ⟨child.annotation.neg, .neg child.annotation child.construction rfl⟩ := rfl

/-- Retaining addition uses the original syntactic sharing decision and its actual child caches. -/
@[cbv_eval] theorem Expr.retain_add {arity : Nat} (environment : Fin arity → Annotated)
    (left right : Expr arity) (inferAlgebraic : Bool := true) :
    (Expr.add left right).retain environment inferAlgebraic =
      if same : right = .neg left then
        let child := left.retain environment inferAlgebraic
        same.symm ▸ ⟨child.annotation.cancel, .addNeg child.annotation child.construction rfl⟩
      else
        let first := left.retain environment inferAlgebraic
        let second := right.retain environment inferAlgebraic
        ⟨first.annotation.add second.annotation inferAlgebraic,
          .add same first.annotation second.annotation first.construction second.construction inferAlgebraic rfl⟩ := rfl

/-- Retaining subtraction uses its original equality decision and retains each actual required child once. -/
@[cbv_eval] theorem Expr.retain_sub {arity : Nat} (environment : Fin arity → Annotated)
    (left right : Expr arity) (inferAlgebraic : Bool := true) :
    (Expr.sub left right).retain environment inferAlgebraic =
      if same : left = right then
        let child := left.retain environment inferAlgebraic
        same ▸ ⟨child.annotation.cancel, .subSelf child.annotation child.construction rfl⟩
      else
        let first := left.retain environment inferAlgebraic
        let second := right.retain environment inferAlgebraic
        ⟨first.annotation.add second.annotation.neg inferAlgebraic,
          .sub same first.annotation second.annotation first.construction second.construction inferAlgebraic rfl⟩ := rfl

/-- Retaining multiplication preserves the shared square branch and both caches of an unshared product. -/
@[cbv_eval] theorem Expr.retain_mul {arity : Nat} (environment : Fin arity → Annotated)
    (left right : Expr arity) (inferAlgebraic : Bool := true) :
    (Expr.mul left right).retain environment inferAlgebraic =
      if same : left = right then
        let child := left.retain environment inferAlgebraic
        same ▸ ⟨child.annotation.square inferAlgebraic, .square child.annotation child.construction inferAlgebraic rfl⟩
      else
        let first := left.retain environment inferAlgebraic
        let second := right.retain environment inferAlgebraic
        ⟨first.annotation.mul second.annotation inferAlgebraic,
          .mul same first.annotation second.annotation first.construction second.construction inferAlgebraic rfl⟩ := rfl

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

end
