module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Construction
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Left-to-right checked-expression evaluation contexts

A right-child context retains the completed original left child. A left-child
context retains the exact unvisited right syntax. Invalid reciprocals and
unresolved original admissions propagate through these same contexts.
-/

public section
namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Checked

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Equivalence.Zero (ZeroIdentity)

variable {arity : Nat} {environment : Fin arity → Annotated}

set_option genInjectivity false in
/-- A total unary operation in the checked syntax. -/
inductive Unary where
  /-- Original numerical negation. -/
  | neg
  /-- The displayed finite natural power. -/
  | pow (exponent : Nat)
  /-- Original numerical conjugation. -/
  | conj

constructive_injectivity Unary

/-- Apply a total unary operation to its exact retained child syntax. -/
@[expose] def Unary.expression (operation : Unary) (input : Expr arity) : Expr arity :=
  match operation with
  | .neg => .neg input
  | .pow exponent => .pow input exponent
  | .conj => .conj input

/-- Apply a total unary operation to the same completed original child. -/
@[expose] def Unary.complete (operation : Unary) {input : Expr arity} (child : Construction.Result environment input) :
    Construction.Result environment (operation.expression input) :=
  match operation with
  | .neg => child.neg
  | .pow exponent => child.pow exponent
  | .conj => child.conj

set_option genInjectivity false in
/-- A binary operation evaluated through its original children from left to right. -/
inductive Binary where
  /-- Original numerical addition. -/
  | add
  /-- Original numerical subtraction. -/
  | sub
  /-- Original numerical multiplication. -/
  | mul

constructive_injectivity Binary

/-- Apply a binary operation to its original ordered child syntax. -/
@[expose] def Binary.expression (operation : Binary) (left right : Expr arity) : Expr arity :=
  match operation with
  | .add => .add left right
  | .sub => .sub left right
  | .mul => .mul left right

/-- Apply a binary operation to the same two completed original children. -/
@[expose] def Binary.complete (operation : Binary) {left right : Expr arity}
    (first : Construction.Result environment left) (second : Construction.Result environment right) :
    Construction.Result environment (operation.expression left right) :=
  match operation with
  | .add => first.add second
  | .sub => first.sub second
  | .mul => first.mul second

set_option genInjectivity false in
/-- One original evaluation frame, retaining the completed prefix and unvisited syntax. -/
inductive Frame (environment : Fin arity → Annotated) : Expr arity → Expr arity → Type 1 where
  /-- A total unary parent waits for its original child. -/
  | unary (operation : Unary) (input : Expr arity) : Frame environment input (operation.expression input)
  /-- A checked reciprocal waits for its original denominator. -/
  | inverse (input : Expr arity) : Frame environment input (.inverse input)
  /-- The original left child is unfinished; the original right syntax has not yet been evaluated. -/
  | left (operation : Binary) (left right : Expr arity) : Frame environment left (operation.expression left right)
  /-- The original right child is unfinished; its original left sibling is already completed and cached. -/
  | right (operation : Binary) {left : Expr arity} (first : Construction.Result environment left) (right : Expr arity) :
      Frame environment right (operation.expression left right)

constructive_injectivity Frame

/-- Read the actual already completed original sibling retained by a right-child frame. -/
@[expose] def Frame.completed {input output : Expr arity} : Frame environment input output →
    Option ((original : Expr arity) × Construction.Result environment original)
  | .right _ first _ => some ⟨_, first⟩
  | .unary _ _ | .inverse _ | .left _ _ _ => none

set_option genInjectivity false in
/-- The first invalid reciprocal in the original left-to-right evaluation order.

Every preceding sibling is completed. Every subsequent sibling remains in its
original unvisited syntax, so a later invalid reciprocal cannot replace this
original occurrence.
-/
inductive Invalid (environment : Fin arity → Annotated) : Expr arity → Type 1 where
  /-- The actual completed denominator is operationally zero at this original reciprocal occurrence. -/
  | inverse {input : Expr arity} (child : Construction.Result environment input) (zero : ZeroIdentity child.channel) :
      Invalid environment (.inverse input)
  /-- Retain the original context around the first invalid occurrence. -/
  | through {input output : Expr arity} (frame : Frame environment input output) (first : Invalid environment input) :
      Invalid environment output

constructive_injectivity Invalid

/-- Read the actual completed original prefix surrounding the first invalid reciprocal, in evaluation order. -/
@[expose] def Invalid.prefix {expression : Expr arity} : Invalid environment expression →
    List ((original : Expr arity) × Construction.Result environment original)
  | .inverse _ _ => []
  | .through frame first => match frame.completed with
    | none => first.prefix
    | some retained => retained :: first.prefix

/-- Read the actual completed denominator and its exact zero obstruction at the first invalid original occurrence. -/
@[expose] def Invalid.denominator {expression : Expr arity} : Invalid environment expression →
    (original : Expr arity) × (child : Construction.Result environment original) × ZeroIdentity child.channel
  | .inverse child zero => ⟨_, child, zero⟩
  | .through _ first => first.denominator

set_option genInjectivity false in
/-- An unresolved original algebraic admission and the retained evaluation frames surrounding it. -/
inductive Pending (environment : Fin arity → Annotated) : Expr arity → Type 1 where
  /-- Retain the actual original compilation, partial slots and exact first missing original bounded occurrence. -/
  | base {expression : Basic.Expr arity} (cached : Base.Cached environment expression)
      (missing : Base.Missing cached.compiled.bindings cached.slots cached.required)
      (unresolved : List (Fin cached.compiled.bindings.length))
      (unresolved_eq : unresolved = Base.Slots.missing cached.compiled.bindings cached.slots cached.required) :
      Pending environment (.base expression)
  /-- Retain original completed siblings and unvisited syntax surrounding this exact unresolved occurrence. -/
  | through {input output : Expr arity} (frame : Frame environment input output) (pending : Pending environment input) :
      Pending environment output

constructive_injectivity Pending

/-- Read the same already completed original siblings retained across a suspension, in evaluation order. -/
@[expose] def Pending.prefix {expression : Expr arity} : Pending environment expression →
    List ((original : Expr arity) × Construction.Result environment original)
  | .base _ _ _ _ => []
  | .through frame pending => match frame.completed with
    | none => pending.prefix
    | some retained => retained :: pending.prefix

set_option genInjectivity false in
/-- One finite evaluation outcome with original success, first invalid reciprocal or retained unresolved admissions. -/
inductive Outcome (environment : Fin arity → Annotated) (expression : Expr arity) where
  /-- The original checked expression has a productive retained numerical construction. -/
  | completed (value : Construction.Result environment expression)
  /-- Its first invalid reciprocal has an exact original zero obstruction. -/
  | invalid (first : Invalid environment expression)
  /-- Its original partial work and unresolved admission request are retained for resumption. -/
  | pending (request : Pending environment expression)

constructive_injectivity Outcome

/-- A finite evaluation has resolved, either productively or by its exact first reciprocal obstruction. -/
@[expose] def Outcome.Resolved {expression : Expr arity} : Outcome environment expression → Prop
  | .completed _ => True
  | .invalid _ => True
  | .pending _ => False

/-- A full materialization preserves the original exact invalidity or admission request on failure. -/
abbrev MaterializedOutcome (environment : Fin arity → Annotated) (expression : Expr arity) :=
  Except (Invalid environment expression ⊕ Pending environment expression) (Completed environment expression)

/-- Return a retained full original Sidecar result at an explicit boundary, preserving exact failure/pending data. -/
@[expose] def Outcome.materialize {expression : Expr arity} :
    Outcome environment expression → MaterializedOutcome environment expression
  | .completed value => .ok value.materialize
  | .invalid first => .error (.inl first)
  | .pending request => .error (.inr request)

end Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
end
