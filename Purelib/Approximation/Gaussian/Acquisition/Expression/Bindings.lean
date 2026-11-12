module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Compilation
import Init.Data.List.Basic
public import Purelib.Data.List.DependentProduct
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original leaf bindings of retained acquisition expressions

Each binding stores an actual compiled annotation and its original atom index
or labelled root constructor. Lookup retains a bounded table index or proves
that the requested source leaf is absent; it asserts no numerical inequality.
-/

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List

set_option genInjectivity false in
/-- An original indexed atom or explicitly labelled root leaf of the acquisition syntax. -/
inductive Leaf (arity : Nat) where
  /-- Retain the original atom index in its original environment. -/
  | atom (index : Fin arity)
  /-- Retain the original root parameter and displayed sheet. -/
  | root (parameter : Canonical) (sheet : Fin 2)
  deriving @[expose] DecidableEq

constructive_injectivity Leaf

/-- The original annotated constructor specified by a leaf and its original atom environment. -/
@[expose] def Leaf.annotation {arity : Nat} (environment : Fin arity → Annotated) : Leaf arity → Annotated
  | .atom index => environment index
  | .root parameter sheet => Annotated.root parameter sheet

set_option genInjectivity false in
/-- An actual retained leaf annotation, authenticated against its entire original constructor.

The equality binds root ownership as well as its channel and parameter. A
matching radicand alone never identifies an independently supplied atom. -/
structure Binding {arity : Nat} (environment : Fin arity → Annotated) where
  /-- The original source leaf and its retained index or branch label. -/
  leaf : Leaf arity
  /-- The actual annotation obtained by the original compilation. -/
  annotation : Annotated
  /-- The actual annotation is the entire original leaf constructor's output. -/
  annotation_eq : annotation = leaf.annotation environment

constructive_injectivity Binding

/-- Collect actual retained leaf annotations without invoking their original producers again.

Shared cancellation and square nodes recurse through their single actual child.
Repeated keys remain separate retained occurrences; lookup selects a checked
original occurrence for the common normal-form environment. -/
@[expose] def Construction.bindings {arity : Nat} {environment : Fin arity → Annotated} :
    {expression : Expr arity} → {annotation : Annotated} →
      Construction environment expression annotation → List (Binding environment)
  | _, _, .atom index annotation source_eq => [⟨.atom index, annotation, source_eq⟩]
  | _, _, .rational _ _ _ => []
  | _, _, .root parameter sheet annotation source_eq => [⟨.root parameter sheet, annotation, source_eq⟩]
  | _, _, .neg _ construction _ => construction.bindings
  | _, _, .add _ _ _ first second _ _ => first.bindings ++ second.bindings
  | _, _, .addNeg _ construction _ => construction.bindings
  | _, _, .sub _ _ _ first second _ _ => first.bindings ++ second.bindings
  | _, _, .subSelf _ construction _ => construction.bindings
  | _, _, .mul _ _ _ first second _ _ => first.bindings ++ second.bindings
  | _, _, .square _ construction _ _ => construction.bindings

/-- Read the actual original leaf bindings from a retained compiled view. -/
@[expose] def Compiled.bindings {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (compiled : Compiled environment expression) : List (Binding environment) := compiled.construction.bindings

namespace Binding

/-- The displayed original leaf occurs in the finite retained binding table. -/
@[expose] def Present {arity : Nat} {environment : Fin arity → Annotated} (leaf : Leaf arity) :
    List (Binding environment) → Prop
  | [] => False
  | first :: remaining => first.leaf = leaf ∨ Present leaf remaining

/-- An original occurrence remains present when a retained suffix is appended. -/
theorem Present.append_left {arity : Nat} {environment : Fin arity → Annotated} {leaf : Leaf arity}
    {first : List (Binding environment)} (present : Present leaf first) (second : List (Binding environment)) :
    Present leaf (first ++ second) := by
  induction first with
  | nil => exact False.elim present
  | cons head tail ih =>
      cases present with
      | inl same => exact Or.inl same
      | inr rest => exact Or.inr (ih rest)

/-- An original occurrence remains present when a retained prefix is prepended. -/
theorem Present.append_right {arity : Nat} {environment : Fin arity → Annotated} {leaf : Leaf arity}
    (first : List (Binding environment)) {second : List (Binding environment)} (present : Present leaf second) :
    Present leaf (first ++ second) := by
  induction first with
  | nil => exact present
  | cons head tail ih => exact Or.inr ih

/-- Read the cached coherent channel of an actual original leaf annotation. -/
@[expose] def channel {arity : Nat} {environment : Fin arity → Annotated} (binding : Binding environment) :
    CoherentNamed := binding.annotation.channel

/-- Read a checked original table occurrence using its original retained bound. -/
@[expose] def read {arity : Nat} {environment : Fin arity → Annotated} (bindings : List (Binding environment))
    (index : Fin bindings.length) : Binding environment := bindings[index.val]'index.isLt

/-- Appending the original bounded binding readers returns the same complete records at every appended occurrence. -/
theorem read_appendFn {arity : Nat} {environment : Fin arity → Annotated} :
    (first second : List (Binding environment)) → (index : Fin (first ++ second).length) →
    DependentProduct.appendFn first second (read first) (read second) index = read (first ++ second) index
  | [], _, _ => rfl
  | _head :: remaining, second, index => by
      refine Fin.cases (Eq.refl _) ?_ index
      intro tail
      exact read_appendFn remaining second tail

/-- Read only actual retained coherent channels at their checked original table positions. -/
@[expose] def channels {arity : Nat} {environment : Fin arity → Annotated} (bindings : List (Binding environment)) :
    Fin bindings.length → CoherentNamed := fun index => (read bindings index).channel

/-- Appended left lookup retains the complete original binding at its embedded occurrence.

The equality includes the original leaf, annotation and complete annotation
authentication. It uses the original scalar list-read law and explicit bound. -/
theorem read_append_left {arity : Nat} {environment : Fin arity → Annotated}
    (first second : List (Binding environment)) (index : Fin first.length) :
    read (first ++ second) (DependentProduct.leftIndex first second index) = read first index := by
  let combined := DependentProduct.leftIndex first second index
  have coordinate : combined.val = index.val := DependentProduct.leftIndex_val first second index
  have bound : index.val < (first ++ second).length := coordinate ▸ combined.isLt
  exact (getElem_congr rfl coordinate combined.isLt).trans
    (Append.getElem_append_left first second index.val index.isLt bound)

/-- Appended right lookup retains the complete original binding after the actual original prefix.

Duplicate leaves remain distinct occurrences. The complete right annotation
and authentication are read from the supplied original suffix, not rebuilt. -/
theorem read_append_right {arity : Nat} {environment : Fin arity → Annotated}
    (first second : List (Binding environment)) (index : Fin second.length) :
    read (first ++ second) (DependentProduct.rightIndex first second index) = read second index := by
  let combined := DependentProduct.rightIndex first second index
  have coordinate : combined.val = first.length + index.val := DependentProduct.rightIndex_val first second index
  have bound : first.length + index.val < (first ++ second).length := coordinate ▸ combined.isLt
  exact (getElem_congr rfl coordinate combined.isLt).trans
    (Append.getElem_append_right first second index.val index.isLt bound)

/-- The appended left channel is the same channel of its complete original retained binding. -/
theorem channels_append_left {arity : Nat} {environment : Fin arity → Annotated}
    (first second : List (Binding environment)) (index : Fin first.length) :
    channels (first ++ second) (DependentProduct.leftIndex first second index) = channels first index :=
  congrArg (fun binding : Binding environment => binding.channel) (read_append_left first second index)

/-- The appended right channel is the same channel of its complete original retained binding. -/
theorem channels_append_right {arity : Nat} {environment : Fin arity → Annotated}
    (first second : List (Binding environment)) (index : Fin second.length) :
    channels (first ++ second) (DependentProduct.rightIndex first second index) = channels second index :=
  congrArg (fun binding : Binding environment => binding.channel) (read_append_right first second index)

set_option genInjectivity false in
/-- A checked original occurrence or a proved absence in the displayed finite binding table. -/
inductive Lookup {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) (leaf : Leaf arity) where
  /-- Retain the actual bounded table position and the exact original source-leaf identity. -/
  | found (index : Fin bindings.length) (leaf_eq : (read bindings index).leaf = leaf)
  /-- Prove absence from every original table position, without identifying numerical channel values. -/
  | missing (absent : ∀ index : Fin bindings.length, (read bindings index).leaf ≠ leaf)

constructive_injectivity Lookup

/-- Search the finite original table, retaining either its first matching occurrence or a proof of absence. -/
@[expose] def lookup {arity : Nat} {environment : Fin arity → Annotated}
    (leaf : Leaf arity) : (bindings : List (Binding environment)) → Lookup bindings leaf
  | [] => .missing (fun index => Fin.elim0 index)
  | first :: remaining =>
      if same : first.leaf = leaf then
        .found ⟨0, Nat.zero_lt_succ _⟩ same
      else
        match lookup leaf remaining with
        | .found index leaf_eq =>
            .found ⟨index.val + 1, Nat.succ_lt_succ index.isLt⟩ leaf_eq
        | .missing absent =>
            .missing (fun index => Fin.cases same (fun tail => absent tail) index)

/-- Locate a certified original occurrence by finite key comparison, retaining its original table bound. -/
@[expose, cbv_opaque] def locate {arity : Nat} {environment : Fin arity → Annotated} (leaf : Leaf arity)
    (bindings : List (Binding environment)) (present : Present leaf bindings) :
      {index : Fin bindings.length // (read bindings index).leaf = leaf} :=
  match bindings, present with
  | [], impossible => False.elim impossible
  | first :: remaining, present =>
      if same : first.leaf = leaf then
        ⟨⟨0, Nat.zero_lt_succ _⟩, same⟩
      else
        have tailPresent : Present leaf remaining := by
          cases present with
          | inl equal => exact False.elim (same equal)
          | inr tail => exact tail
        let position := locate leaf remaining tailPresent
        ⟨⟨position.val.val + 1, Nat.succ_lt_succ position.val.isLt⟩, position.property⟩

/-- Locate a retained occurrence through the original pointwise list recursion.

The current table, membership proof and bounded tail position are the exact
inputs and intermediate data of the lookup procedure. -/
@[cbv_eval] theorem locate_eq {arity : Nat} {environment : Fin arity → Annotated}
    (leaf : Leaf arity) (bindings : List (Binding environment)) (present : Present leaf bindings) :
    locate leaf bindings present =
      match bindings, present with
      | [], impossible => False.elim impossible
      | first :: remaining, present =>
          if same : first.leaf = leaf then
            ⟨⟨0, Nat.zero_lt_succ _⟩, same⟩
          else
            have tailPresent : Present leaf remaining := by
              cases present with
              | inl equal => exact False.elim (same equal)
              | inr tail => exact tail
            let position := locate leaf remaining tailPresent
            ⟨⟨position.val.val + 1, Nat.succ_lt_succ position.val.isLt⟩, position.property⟩ := by
  cases bindings <;> rfl

/-- A matching original first occurrence is the position selected by finite leaf lookup. -/
theorem locate_zero {arity : Nat} {environment : Fin arity → Annotated}
    (leaf : Leaf arity) (bindings : List (Binding environment)) (present : Present leaf bindings)
    (bound : 0 < bindings.length) (selected : (read bindings ⟨0, bound⟩).leaf = leaf) :
    (locate leaf bindings present).val = ⟨0, bound⟩ := by
  cases bindings with
  | nil => exact False.elim (Nat.not_lt_zero 0 bound)
  | cons first remaining =>
      change first.leaf = leaf at selected
      change (if same : first.leaf = leaf then
        (⟨⟨0, Nat.zero_lt_succ _⟩, same⟩ : {index : Fin (first :: remaining).length //
          (read (first :: remaining) index).leaf = leaf})
        else _).val = ⟨0, bound⟩
      rewrite [dif_pos selected]
      rfl

/-- The retained lookup position reads an actual cached annotation of the requested original leaf. -/
theorem Lookup.annotation_eq {arity : Nat} {environment : Fin arity → Annotated}
    {bindings : List (Binding environment)} {leaf : Leaf arity}
    (index : Fin bindings.length) (leaf_eq : (read bindings index).leaf = leaf) :
    (read bindings index).annotation = leaf.annotation environment :=
  (read bindings index).annotation_eq.trans (congrArg (Leaf.annotation environment) leaf_eq)

end Binding

/-- Every original variable leaf of a retained construction is present in the specified finite binding table. -/
@[expose] def Construction.Supported {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) : {expression : Expr arity} → {annotation : Annotated} →
      Construction environment expression annotation → Prop
  | _, _, .atom index _ _ => Binding.Present (.atom index) bindings
  | _, _, .rational _ _ _ => True
  | _, _, .root parameter sheet _ _ => Binding.Present (.root parameter sheet) bindings
  | _, _, .neg _ construction _ => construction.Supported bindings
  | _, _, .add _ _ _ first second _ _ => first.Supported bindings ∧ second.Supported bindings
  | _, _, .addNeg _ construction _ => construction.Supported bindings
  | _, _, .sub _ _ _ first second _ _ => first.Supported bindings ∧ second.Supported bindings
  | _, _, .subSelf _ construction _ => construction.Supported bindings
  | _, _, .mul _ _ _ first second _ _ => first.Supported bindings ∧ second.Supported bindings
  | _, _, .square _ construction _ _ => construction.Supported bindings

/-- Inclusion of every collected original leaf gives support for the complete retained construction. -/
theorem Construction.supported_of_present {arity : Nat} {environment : Fin arity → Annotated}
    {expression : Expr arity} {annotation : Annotated} (construction : Construction environment expression annotation)
    (bindings : List (Binding environment))
    (included : ∀ leaf, Binding.Present leaf construction.bindings → Binding.Present leaf bindings) :
    construction.Supported bindings := by
  induction construction with
  | atom index annotation source_eq => exact included (.atom index) (Or.inl rfl)
  | rational value annotation source_eq => exact True.intro
  | root parameter sheet annotation source_eq => exact included (.root parameter sheet) (Or.inl rfl)
  | neg child construction output_eq ih => exact ih included
  | add different first second firstConstruction secondConstruction inferAlgebraic output_eq ihFirst ihSecond =>
      exact ⟨ihFirst (fun leaf present => included leaf (present.append_left secondConstruction.bindings)),
        ihSecond (fun leaf present => included leaf (present.append_right firstConstruction.bindings))⟩
  | addNeg child construction output_eq ih => exact ih included
  | sub different first second firstConstruction secondConstruction inferAlgebraic output_eq ihFirst ihSecond =>
      exact ⟨ihFirst (fun leaf present => included leaf (present.append_left secondConstruction.bindings)),
        ihSecond (fun leaf present => included leaf (present.append_right firstConstruction.bindings))⟩
  | subSelf child construction output_eq ih => exact ih included
  | mul different first second firstConstruction secondConstruction inferAlgebraic output_eq ihFirst ihSecond =>
      exact ⟨ihFirst (fun leaf present => included leaf (present.append_left secondConstruction.bindings)),
        ihSecond (fun leaf present => included leaf (present.append_right firstConstruction.bindings))⟩
  | square child construction inferAlgebraic output_eq ih => exact ih included

/-- The actual collected binding table supports its complete original retained construction. -/
theorem Construction.supported_bindings {arity : Nat} {environment : Fin arity → Annotated}
    {expression : Expr arity} {annotation : Annotated} (construction : Construction environment expression annotation) :
    construction.Supported construction.bindings :=
  construction.supported_of_present construction.bindings (fun _ present => present)

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

end
